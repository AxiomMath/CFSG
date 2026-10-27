module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.HallHigman

universe u

open Subgroup CFSG.LocalCores

@[expose] def IsPiSeparable (π : Set Nat.Primes) (X : Type*) [Group X] : Prop :=
  ∀ H : Subgroup X, H.IsSubnormal → ∀ (T : Subgroup H) [T.Normal], IsSimpleGroup (H ⧸ T) →
    (∀ q : Nat.Primes, q.val ∣ T.index → q ∈ π) ∨ ∀ q : Nat.Primes, q.val ∣ T.index → q ∉ π

@[expose] def IsPSolvable (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ H : Subgroup X, H.IsSubnormal → ∀ (T : Subgroup H) [T.Normal], IsSimpleGroup (H ⧸ T) →
    T.index = p ∨ Nat.Coprime p T.index

theorem isPiSeparable_of_isPSolvable {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    (hX : IsPSolvable p X) : IsPiSeparable {q : Nat.Primes | q.val = p} X := by
  intro H hH T _ hs
  rcases hX H hH T hs with h | h
  · exact Or.inl fun q hq => (Nat.prime_dvd_prime_iff_eq q.2 hp).1 (h ▸ hq)
  · exact Or.inr fun q hq hqp => (Nat.Prime.coprime_iff_not_dvd hp).1 h
      (by rw [← show q.val = p from hqp]; exact hq)

variable {X : Type*} [Group X]

private abbrev IsNum (ρ : Set Nat.Primes) (n : ℕ) : Prop := ∀ q : Nat.Primes, q.val ∣ n → q ∈ ρ

private theorem IsNum.dvd {ρ : Set Nat.Primes} {m n : ℕ} (h : IsNum ρ n) (hmn : m ∣ n) :
    IsNum ρ m := fun q hq => h q (hq.trans hmn)

private theorem IsNum.mul {ρ : Set Nat.Primes} {m n : ℕ} (hm : IsNum ρ m) (hn : IsNum ρ n) :
    IsNum ρ (m * n) := fun q hq => by
  rcases (Nat.Prime.dvd_mul q.2).1 hq with h | h
  exacts [hm q h, hn q h]

private theorem IsNum.coprime {ρ : Set Nat.Primes} {m n : ℕ} (hm : IsNum ρ m)
    (hn : IsNum ρᶜ n) : Nat.Coprime m n :=
  Nat.coprime_of_dvd fun k hk hkm hkn => hn ⟨k, hk⟩ hkn (hm ⟨k, hk⟩ hkm)

private theorem IsNum.eq_one {ρ : Set Nat.Primes} {n : ℕ} (hm : IsNum ρ n)
    (hn : IsNum ρᶜ n) : n = 1 :=
  (Nat.coprime_self n).1 (hm.coprime hn)

private theorem isNum_index_inf {M : Type*} [Group M] {ρ : Set Nat.Primes} {K L : Subgroup M}
    [L.Normal] (hK : IsNum ρ K.index) (hL : IsNum ρ L.index) : IsNum ρ (K ⊓ L).index := by
  have h := Subgroup.relIndex_inf_mul_relIndex L K ⊤
  rw [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right, inf_comm] at h
  rw [← h]
  exact (hL.dvd (Subgroup.relIndex_dvd_index_of_normal L K)).mul hK

private theorem isSimpleGroup_quotient_of_maximal {M : Type*} [Group M] {S : Subgroup M}
    [S.Normal] (hS : S ≠ ⊤) (hmax : ∀ T : Subgroup M, T.Normal → S ≤ T → T = S ∨ T = ⊤) :
    IsSimpleGroup (M ⧸ S) := by
  have : Nontrivial (M ⧸ S) := by
    obtain ⟨g, -, hg⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hS)
    exact ⟨⟨QuotientGroup.mk g, 1, fun h => hg ((QuotientGroup.eq_one_iff g).1 h)⟩⟩
  refine { eq_bot_or_eq_top_of_normal := fun T hT => ?_ }
  have hle : S ≤ T.comap (QuotientGroup.mk' S) := fun x hx => by
    simp [(QuotientGroup.eq_one_iff x).2 hx]
  rcases hmax _ (hT.comap _) hle with h | h
  · refine Or.inl (eq_bot_iff.2 fun t ht => ?_)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    have : g ∈ T.comap (QuotientGroup.mk' S) := ht
    rw [h] at this
    exact (Subgroup.mem_bot).2 ((QuotientGroup.eq_one_iff g).2 this)
  · refine Or.inr (eq_top_iff.2 fun t _ => ?_)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    have : g ∈ T.comap (QuotientGroup.mk' S) := by rw [h]; exact mem_top g
    exact this

private theorem finite_subgroup (M : Type*) [Group M] [Finite M] : Finite (Subgroup M) :=
  Finite.of_injective (fun H : Subgroup M => (H : Set M)) SetLike.coe_injective

private theorem isNum_index_of_minimal [Finite X] {ρ : Set Nat.Primes} {P M : Subgroup X}
    [P.Normal] [M.Normal] (hPM : P ≤ M) {S : Subgroup M} [S.Normal]
    (hPS : P.subgroupOf M ≤ S) (hSne : S ≠ ⊤) (hS : IsNum ρ S.index)
    (hmin : ∀ N : Subgroup X, N.Normal → P ≤ N → N ≤ M → N = P ∨ N = M) :
    IsNum ρ (P.subgroupOf M).index := by
  classical
  have := finite_subgroup M
  let 𝓚 : Set (Subgroup M) := {K | P.subgroupOf M ≤ K ∧ K.Normal ∧ IsNum ρ K.index}
  have hinf : ∀ K ∈ 𝓚, ∀ L ∈ 𝓚, K ⊓ L ∈ 𝓚 := by
    rintro K ⟨hPK, hKn, hK⟩ L ⟨hPL, hLn, hL⟩
    exact ⟨le_inf hPK hPL, inferInstance, isNum_index_inf hK hL⟩
  have hSK : S ∈ 𝓚 := ⟨hPS, inferInstance, hS⟩
  obtain ⟨K₀, hK₀⟩ := 𝓚.toFinite.exists_minimal ⟨S, hSK⟩
  obtain ⟨hPK₀, hK₀n, hK₀i⟩ := hK₀.prop
  have hK₀S : K₀ ≤ S := (hK₀.le_of_le (hinf K₀ hK₀.prop S hSK) inf_le_left).trans inf_le_right
  have hinv : ∀ g : X, K₀.map (MulAut.conjNormal g).toMonoidHom = K₀ := by
    intro g
    set φ := MulAut.conjNormal (H := M) g
    have hK₁ : K₀.map φ.toMonoidHom ∈ 𝓚 := by
      refine ⟨fun x hx => ⟨MulAut.conjNormal g⁻¹ x, hPK₀ ?_, ?_⟩, hK₀n.map _ φ.surjective, ?_⟩
      · change ((MulAut.conjNormal g⁻¹ x : M) : X) ∈ P
        rw [MulAut.conjNormal_apply]
        exact ‹P.Normal›.conj_mem _ hx _
      · apply Subtype.ext
        change ((MulAut.conjNormal g (MulAut.conjNormal g⁻¹ x) : M) : X) = x
        simp only [MulAut.conjNormal_apply]
        group
      · rw [show φ.toMonoidHom = ((φ : M ≃* M) : M →* M) from rfl, Subgroup.index_map_equiv]
        exact hK₀i
    have hle : K₀ ≤ K₀.map φ.toMonoidHom :=
      (hK₀.le_of_le (hinf K₀ hK₀.prop _ hK₁) inf_le_left).trans inf_le_right
    have hcard : Nat.card (K₀.map φ.toMonoidHom) = Nat.card K₀ :=
      Subgroup.card_map_of_injective φ.injective
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  set N := K₀.map M.subtype with hNdef
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, hk, rfl⟩ := hn
    refine ⟨MulAut.conjNormal g k, ?_, by simp⟩
    rw [← hinv g]
    exact ⟨k, hk, rfl⟩
  have hPN : P ≤ N := fun x hx => ⟨⟨x, hPM hx⟩, hPK₀ hx, rfl⟩
  rcases hmin N hNn hPN (map_subtype_le K₀) with h | h
  · have : K₀ = P.subgroupOf M := by
      rw [← h, hNdef]
      exact (Subgroup.comap_map_eq_self_of_injective M.subtype_injective K₀).symm
    exact this ▸ hK₀i
  · exfalso
    have : K₀ = ⊤ := by
      rw [← Subgroup.comap_map_eq_self_of_injective M.subtype_injective K₀]
      change N.subgroupOf M = ⊤
      rw [h, subgroupOf_self]
    exact hSne (eq_top_iff.2 (this ▸ hK₀S))

theorem centralizer_piCore_le_piCore [Finite X] {π : Set Nat.Primes} (hX : IsPiSeparable π X)
    (hcore : piCore πᶜ X = ⊥) : centralizer (piCore π X : Set X) ≤ piCore π X := by
  classical
  have := finite_subgroup X
  set P := piCore π X with hPdef
  have hPπ : IsPiSubgroup π P := piCore_isPiSubgroup π
  set C := centralizer (P : Set X) with hCdef
  by_contra hCP
  let 𝓜 : Set (Subgroup X) := {M | M.Normal ∧ P < M ∧ M ≤ C ⊔ P}
  have hCPmem : C ⊔ P ∈ 𝓜 :=
    ⟨Subgroup.sup_normal _ _, lt_of_le_of_ne le_sup_right fun h => hCP (h ▸ le_sup_left),
      le_rfl⟩
  obtain ⟨M, hM⟩ := 𝓜.toFinite.exists_minimal ⟨_, hCPmem⟩
  obtain ⟨hMn, hPM, hMCP⟩ := hM.prop
  have hmin : ∀ N : Subgroup X, N.Normal → P ≤ N → N ≤ M → N = P ∨ N = M := by
    intro N hNn hPN hNM
    rcases eq_or_lt_of_le hPN with h | h
    · exact Or.inl h.symm
    · exact Or.inr (le_antisymm hNM (hM.le_of_le ⟨hNn, h, hNM.trans hMCP⟩ hNM))
  have := finite_subgroup M
  have hP'ne : P.subgroupOf M ≠ ⊤ := fun h =>
    lt_irrefl P (lt_of_lt_of_le hPM (Subgroup.subgroupOf_eq_top.1 h))
  let 𝓢 : Set (Subgroup M) := {S | S.Normal ∧ P.subgroupOf M ≤ S ∧ S ≠ ⊤}
  obtain ⟨S, hS⟩ := 𝓢.toFinite.exists_maximal ⟨P.subgroupOf M, inferInstance, le_rfl, hP'ne⟩
  obtain ⟨hSn, hP'S, hSne⟩ := hS.prop
  have hsimple : IsSimpleGroup (M ⧸ S) := isSimpleGroup_quotient_of_maximal hSne fun T hT hST => by
    by_cases hT' : T = ⊤
    · exact Or.inr hT'
    · exact Or.inl (le_antisymm (hS.le_of_ge ⟨hT, hP'S.trans hST, hT'⟩ hST) hST)
  have hcardM : Nat.card M = Nat.card P * (P.subgroupOf M).index := by
    rw [← (P.subgroupOf M).card_mul_index]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM.le).toEquiv
  rcases hX M hMn.isSubnormal S hsimple with hρ | hρ
  ·
    have hMP := isNum_index_of_minimal hPM.le hP'S hSne hρ hmin
    have hMπ : IsPiSubgroup π M := by
      intro q hq
      rw [hcardM] at hq
      exact (IsNum.mul (fun q hq => hPπ q hq) hMP) q hq
    exact lt_irrefl P (lt_of_lt_of_le hPM (le_piCore_of_normal hMn hMπ))
  ·
    have hMP := isNum_index_of_minimal hPM.le hP'S hSne hρ hmin
    set D := C ⊓ M with hDdef
    have hDn : D.Normal := inferInstance
    have hDP : D ⊔ P = M := by
      refine le_antisymm (sup_le inf_le_right hPM.le) fun m hm => ?_
      obtain ⟨c, hc, p, hp, rfl⟩ := mem_sup_of_normal_right.1 (hMCP hm)
      have hcM : c ∈ M := by simpa using M.mul_mem hm (M.inv_mem (hPM.le hp))
      exact mul_mem_sup ⟨hc, hcM⟩ hp
    set A := P.subgroupOf D with hAdef
    have hidx : A.index = (P.subgroupOf M).index := by
      change P.relIndex D = P.relIndex M
      rw [← hDP, Subgroup.relIndex_sup_right]
    have hidxπ : IsNum πᶜ A.index := by rw [hidx]; exact hMP
    have hAπ : IsNum π (Nat.card A) := by
      refine IsNum.dvd (fun q hq => hPπ q hq) ?_
      rw [← Subgroup.card_map_of_injective D.subtype_injective]
      exact Subgroup.card_dvd_of_le (by rw [subgroupOf_map_subtype]; exact inf_le_left)
    obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime (hAπ.coprime hidxπ)
    have hQcard : Nat.card Q = A.index :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (hQ.card_mul_card.trans A.card_mul_index.symm)
    set Q' := Q.map D.subtype with hQ'def
    have hQ'card : Nat.card Q' = A.index :=
      (Subgroup.card_map_of_injective D.subtype_injective).trans hQcard
    have hπ' : ∀ r ∈ D, IsNum πᶜ (orderOf r) → r ∈ Q' := by
      intro r hr hro
      obtain ⟨⟨a, q⟩, haq⟩ := hQ.2 ⟨r, hr⟩
      have haP : ((a.1 : D) : X) ∈ P := a.2
      have hqC : ((q.1 : D) : X) ∈ C := (q.1).2.1
      have hcomm : Commute ((a.1 : D) : X) ((q.1 : D) : X) :=
        Subgroup.mem_centralizer_iff.1 hqC _ haP
      have hr' : r = ((a.1 : D) : X) * ((q.1 : D) : X) := by
        have := congrArg Subtype.val haq
        simpa using this.symm
      have hqm : ((q.1 : D) : X) ^ Nat.card Q = 1 := by
        have h1 : (⟨q.1, q.2⟩ : Q) ^ Nat.card Q = 1 := pow_card_eq_one'
        exact_mod_cast congrArg (fun x : Q => ((x : D) : X)) h1
      have hrm : r ^ Nat.card Q = ((a.1 : D) : X) ^ Nat.card Q := by
        rw [hr', hcomm.mul_pow, hqm, mul_one]
      have hPa : IsNum π (orderOf ((a.1 : D) : X)) :=
        IsNum.dvd (fun q hq => hPπ q hq) (Subgroup.orderOf_dvd_natCard P haP)
      have ham : ((a.1 : D) : X) ^ Nat.card Q = 1 := by
        refine orderOf_eq_one_iff.1 (IsNum.eq_one (hPa.dvd (orderOf_pow_dvd _)) ?_)
        rw [← hrm]
        exact hro.dvd (orderOf_pow_dvd _)
      have ha1 : ((a.1 : D) : X) = 1 := by
        have hmπ' : IsNum πᶜ (Nat.card Q) := by rw [hQcard]; exact hidxπ
        exact orderOf_eq_one_iff.1
          (IsNum.eq_one hPa (hmπ'.dvd (orderOf_dvd_of_pow_eq_one ham)))
      rw [hr', ha1, one_mul]
      exact ⟨q.1, q.2, rfl⟩
    have hQ'n : Q'.Normal := by
      refine ⟨fun x hx g => hπ' _ (hDn.conj_mem x (map_subtype_le Q hx) g) ?_⟩
      have hconj : orderOf (g * x * g⁻¹) = orderOf x := by
        have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
        simpa [MulAut.conj_apply] using this
      rw [hconj]
      exact IsNum.dvd (by rw [hQ'card]; exact hidxπ) (Subgroup.orderOf_dvd_natCard Q' hx)
    have hQ'bot : Q' = ⊥ := by
      have h := le_piCore_of_normal hQ'n fun q hq => hidxπ q (hQ'card ▸ hq)
      rw [hcore] at h
      exact le_bot_iff.1 h
    have h1 : (P.subgroupOf M).index = 1 := by
      rw [← hidx, ← hQ'card, hQ'bot, Subgroup.card_bot]
    exact hP'ne (Subgroup.index_eq_one.1 h1)

private theorem eq_or_eq_top_of_isSimpleGroup_quotient {A : Type*} [Group A] {T : Subgroup A}
    [T.Normal] (hs : IsSimpleGroup (A ⧸ T)) {L : Subgroup A} (hL : L.Normal) (hTL : T ≤ L) :
    L = T ∨ L = ⊤ := by
  rcases (hL.map _ (QuotientGroup.mk'_surjective T)).eq_bot_or_eq_top with h | h
  · refine Or.inl (le_antisymm (fun x hx => ?_) hTL)
    have hx' : QuotientGroup.mk' T x ∈ L.map (QuotientGroup.mk' T) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).1 hx'
  · refine Or.inr (eq_top_iff.2 fun x _ => ?_)
    have hx' : QuotientGroup.mk' T x ∈ L.map (QuotientGroup.mk' T) := by rw [h]; exact mem_top _
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyx' : y⁻¹ * x ∈ T := QuotientGroup.eq.1 hyx
    simpa using L.mul_mem hy (hTL hyx')

private theorem IsPiSeparable.apply_equiv {π : Set Nat.Primes} (hX : IsPiSeparable π X)
    {H : Subgroup X} (hH : H.IsSubnormal) {A : Type*} [Group A] (e : A ≃* H) (T : Subgroup A)
    [T.Normal] (hs : IsSimpleGroup (A ⧸ T)) : IsNum π T.index ∨ IsNum πᶜ T.index := by
  have : (T.map (e : A →* H)).Normal := ‹T.Normal›.map _ e.surjective
  have hs' : IsSimpleGroup (H ⧸ T.map (e : A →* H)) :=
    (QuotientGroup.congr T (T.map (e : A →* H)) e rfl).symm.isSimpleGroup
  have h := hX H hH (T.map (e : A →* H)) hs'
  rwa [Subgroup.index_map_equiv] at h

theorem IsPiSeparable.normal {π : Set Nat.Primes} (hX : IsPiSeparable π X) (M : Subgroup X)
    [M.Normal] : IsPiSeparable π M := fun H hH T _ hs =>
  hX.apply_equiv (hH.trans' ‹M.Normal›.isSubnormal)
    (H.equivMapOfInjective M.subtype M.subtype_injective) T hs

theorem IsPiSeparable.section_index {π : Set Nat.Primes} (n : ℕ) :
    ∀ {X : Type u} [Group X] [Finite X], Nat.card X = n → IsPiSeparable π X →
      ∀ {A : Type u} [Group A] (f : A →* X), Function.Injective f → ∀ (T : Subgroup A) [T.Normal],
        IsSimpleGroup (A ⧸ T) →
          (∀ q : Nat.Primes, q.val ∣ T.index → q ∈ π) ∨
            ∀ q : Nat.Primes, q.val ∣ T.index → q ∉ π := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn hX A _ f hf T _ hs
  classical
  have := finite_subgroup X
  have hbot : (⊥ : Subgroup X) ≠ ⊤ := by
    intro h
    obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have h1 : ∀ x : A, x = 1 := fun x => hf (by
      have hx : f x ∈ (⊥ : Subgroup X) := h ▸ mem_top (f x)
      rw [Subgroup.mem_bot] at hx
      rw [hx, map_one])
    exact hab (by rw [h1 a, h1 b])
  let 𝓝 : Set (Subgroup X) := {M | M.Normal ∧ M ≠ ⊤}
  obtain ⟨M, hM⟩ := 𝓝.toFinite.exists_maximal ⟨⊥, normal_bot, hbot⟩
  obtain ⟨hMn, hMne⟩ := hM.prop
  have hmax : ∀ K : Subgroup X, K.Normal → M ≤ K → K = M ∨ K = ⊤ := fun K hK hMK => by
    by_cases hKt : K = ⊤
    · exact Or.inr hKt
    · exact Or.inl (le_antisymm (hM.le_of_ge ⟨hK, hKt⟩ hMK) hMK)
  have hXM : IsNum π M.index ∨ IsNum πᶜ M.index :=
    hX.apply_equiv IsSubnormal.top Subgroup.topEquiv.symm M
      (isSimpleGroup_quotient_of_maximal hMne hmax)
  set L := M.comap f with hLdef
  by_cases hLT : L ≤ T
  ·
    have hdvd : T.index ∣ M.index :=
      (Subgroup.index_dvd_of_le hLT).trans (by
        rw [hLdef, Subgroup.index_comap]
        exact Subgroup.relIndex_dvd_index_of_normal M f.range)
    rcases hXM with h | h
    exacts [Or.inl (h.dvd hdvd), Or.inr (h.dvd hdvd)]
  ·
    have htop : L ⊔ T = ⊤ :=
      (eq_or_eq_top_of_isSimpleGroup_quotient hs (Subgroup.sup_normal L T)
        le_sup_right).resolve_left fun h => hLT (h ▸ le_sup_left)
    have hidx : T.index = (T.subgroupOf L).index := by
      rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
      rfl
    have e2 : ↥(L ⊔ T) ⧸ T.subgroupOf (L ⊔ T) ≃* A ⧸ T :=
      QuotientGroup.congr _ _ ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) (by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, htop ▸ mem_top x⟩, hx, rfl⟩)
    have hsL : IsSimpleGroup (L ⧸ T.subgroupOf L) :=
      have := hs
      ((QuotientGroup.quotientInfEquivProdNormalQuotient L T).trans e2).isSimpleGroup
    let g : L →* M := (f.comp L.subtype).codRestrict M fun x => x.2
    have hg : Function.Injective g := fun x y h => Subtype.ext (hf (congrArg Subtype.val h))
    have hMlt : Nat.card M < n := by
      rw [← hn, ← Subgroup.card_top (G := X)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hMne)
    rw [hidx]
    exact ih _ hMlt rfl (hX.normal M) g hg (T.subgroupOf L) hsL

theorem IsPiSeparable.subgroup {X : Type u} [Group X] [Finite X] {π : Set Nat.Primes}
    (hX : IsPiSeparable π X) (K : Subgroup X) : IsPiSeparable π K := fun H _ T _ hs =>
  IsPiSeparable.section_index _ rfl hX (K.subtype.comp H.subtype)
    (K.subtype_injective.comp H.subtype_injective) T hs

theorem IsPiSeparable.quotient {X : Type u} [Group X] [Finite X] {π : Set Nat.Primes}
    (hX : IsPiSeparable π X) (N : Subgroup X) [N.Normal] : IsPiSeparable π (X ⧸ N) := by
  intro H _ T _ hs
  set B := H.comap (QuotientGroup.mk' N)
  let ψ : B →* H := ((QuotientGroup.mk' N).comp B.subtype).codRestrict H fun x => x.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨x, hy⟩, rfl⟩
  let ψ' := (QuotientGroup.mk' T).comp ψ
  have hψ' : Function.Surjective ψ' := (QuotientGroup.mk'_surjective T).comp hψ
  let e := QuotientGroup.quotientKerEquivOfSurjective ψ' hψ'
  have hs' : IsSimpleGroup (B ⧸ ψ'.ker) := e.isSimpleGroup
  have h := IsPiSeparable.section_index _ rfl hX B.subtype B.subtype_injective ψ'.ker hs'
  have hidx : ψ'.ker.index = T.index := Nat.card_congr e.toEquiv
  rwa [hidx] at h

theorem IsPiSeparable.minimal_normal {X : Type u} [Group X] [Finite X] {π : Set Nat.Primes}
    (hX : IsPiSeparable π X) {N : Subgroup X} [N.Normal] (hN : N ≠ ⊥)
    (hmin : ∀ K : Subgroup X, K.Normal → K ≤ N → K = ⊥ ∨ K = N) :
    (∀ q : Nat.Primes, q.val ∣ Nat.card N → q ∈ π) ∨
      ∀ q : Nat.Primes, q.val ∣ Nat.card N → q ∉ π := by
  classical
  have := finite_subgroup N
  have hbotN : (⊥ : Subgroup N) ≠ ⊤ := by
    intro h
    refine hN (eq_bot_iff.2 fun x hx => ?_)
    have hx' : (⟨x, hx⟩ : N) ∈ (⊥ : Subgroup N) := h ▸ mem_top _
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val ((Subgroup.mem_bot).1 hx'))
  let 𝓢 : Set (Subgroup N) := {S | S.Normal ∧ S ≠ ⊤}
  obtain ⟨S, hS⟩ := 𝓢.toFinite.exists_maximal ⟨⊥, normal_bot, hbotN⟩
  obtain ⟨hSn, hSne⟩ := hS.prop
  have hsimple : IsSimpleGroup (N ⧸ S) := isSimpleGroup_quotient_of_maximal hSne fun T hT hST => by
    by_cases hT' : T = ⊤
    · exact Or.inr hT'
    · exact Or.inl (le_antisymm (hS.le_of_ge ⟨hT, hT'⟩ hST) hST)
  have hcard : ((⊥ : Subgroup X).subgroupOf N).index = Nat.card N := by
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot]
  have hPS : (⊥ : Subgroup X).subgroupOf N ≤ S := by rw [Subgroup.bot_subgroupOf]; exact bot_le
  have hmin' : ∀ K : Subgroup X, K.Normal → ⊥ ≤ K → K ≤ N → K = ⊥ ∨ K = N :=
    fun K hK _ hKN => hmin K hK hKN
  rcases IsPiSeparable.section_index _ rfl hX N.subtype N.subtype_injective S hsimple with h | h
  · exact Or.inl (hcard ▸ isNum_index_of_minimal bot_le hPS hSne h hmin')
  · exact Or.inr (hcard ▸ isNum_index_of_minimal bot_le hPS hSne h hmin')

theorem isCharacteristicP_of_isPSolvable [Finite X] {p : ℕ} [hp : Fact p.Prime]
    (hX : IsPSolvable p X) (hcore : pPrimeCore p X = ⊥) : IsCharacteristicP p X := by
  unfold IsCharacteristicP
  rw [pCore_eq_piCore X p]
  refine centralizer_piCore_le_piCore (isPiSeparable_of_isPSolvable hp.out hX) ?_
  rw [← hcore, pPrimeCore_eq_piCore X p]
  rfl

theorem hall_higman_pi_core_self_centralizing :
    (∀ (π : Set Nat.Primes) (X : Type*) [Group X] [Finite X], IsPiSeparable π X →
      piCore πᶜ X = ⊥ → centralizer (piCore π X : Set X) ≤ piCore π X) ∧
    ∀ (p : ℕ) [Fact p.Prime] (X : Type*) [Group X] [Finite X], IsPSolvable p X →
      pPrimeCore p X = ⊥ → IsCharacteristicP p X :=
  ⟨fun _ _ _ _ hX hcore => centralizer_piCore_le_piCore hX hcore,
    fun _ _ _ _ _ hX hcore => isCharacteristicP_of_isPSolvable hX hcore⟩

end CFSG.HallHigman

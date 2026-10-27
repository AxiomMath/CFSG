module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
public import CFSG.LocalAnalysis.AGLEmbedding.SUPairInduction
public import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.AGLEmbedding.SUPair

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem oUpperTwo_le (X : Subgroup Y) : oUpperTwo X ≤ X :=
  (closure_le _).mpr fun _ hx => hx.1

theorem isSubnormal_oUpperTwo {T : Subgroup Y} (hT : IsSubnormal T ⊤) :
    IsSubnormal (oUpperTwo T) ⊤ := by
  refine IsSubnormal.step (oUpperTwo_le T) ⟨fun n hn g => ?_⟩ hT
  rw [mem_subgroupOf] at hn ⊢
  have hTg : T.map (MulAut.conj (g : Y)).toMonoidHom = T := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact T.mul_mem (T.mul_mem g.2 hx) (T.inv_mem g.2)
    · intro x hx
      refine ⟨(g : Y)⁻¹ * x * (g : Y), T.mul_mem (T.mul_mem (T.inv_mem g.2) hx) g.2, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have h := map_oUpperTwo (MulAut.conj (g : Y)).toMonoidHom T
  rw [hTg] at h
  have hmem : (g : Y) * (n : Y) * (g : Y)⁻¹ ∈
      (oUpperTwo T).map (MulAut.conj (g : Y)).toMonoidHom :=
    ⟨n, hn, by simp [MulAut.conj_apply]⟩
  rw [h] at hmem
  simpa using hmem

theorem exists_two_pow_mem {T : Subgroup Y} {t : Y} (ht : t ∈ T) :
    ∃ a : ℕ, t ^ (2 ^ a) ∈ oUpperTwo T := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t).ne'
  refine ⟨a, subset_closure ⟨T.pow_mem ht _, ?_⟩⟩
  have hdvd : 2 ^ a ∣ orderOf t := ⟨m, hn⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hn,
    Nat.mul_div_cancel_left m (pow_pos two_pos a)]
  exact hm

theorem le_normalizer_commutator_zpowers {N : Subgroup Y} {t : Y}
    (ht : t ∈ normalizer (N : Set Y)) :
    N ≤ normalizer ((⁅N, zpowers t⁆ : Subgroup Y) : Set Y) := by
  intro x hx
  refine mem_normalizer_fintype fun c hc => ?_
  have hle : ⁅N, zpowers t⁆.map (MulAut.conj x).toMonoidHom ≤ ⁅N, zpowers t⁆ := by
    rw [Subgroup.commutator_def, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨n, hn, v, hv, rfl⟩, rfl⟩
    have e : (MulAut.conj x).toMonoidHom ⁅n, v⁆ = ⁅x * n, v⁆ * ⁅x, v⁆⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [SetLike.mem_coe, e]
    exact mul_mem (commutator_mem_commutator (N.mul_mem hx hn) hv)
      (inv_mem (commutator_mem_commutator hx hv))
  exact hle ⟨c, hc, by simp [MulAut.conj_apply]⟩

theorem commute_of_conj_mem_zpowers_three {a b : Y} (ha : orderOf a = 3) {k : ℕ}
    (hb : b ^ (3 ^ k) = 1) (hab : b * a * b⁻¹ ∈ zpowers a) : b * a = a * b := by
  classical
  have ha3 : a ^ 3 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    norm_num at ha
  rw [mem_zpowers_iff_mem_range_orderOf, ha] at hab
  simp only [Finset.mem_image, Finset.mem_range] at hab
  obtain ⟨j, hj3, hj⟩ := hab
  interval_cases j
  · exfalso
    apply ha1
    have : b * a * b⁻¹ = 1 := by rw [← hj, pow_zero]
    have := congrArg (fun g => b⁻¹ * g * b) this
    simpa [mul_assoc] using this
  · rw [pow_one] at hj
    calc b * a = b * a * b⁻¹ * b := by group
      _ = a * b := by rw [← hj]
  · exfalso
    have hinv : b * a * b⁻¹ = a⁻¹ := by
      rw [← hj, eq_inv_iff_mul_eq_one, ← pow_succ, ha3]
    have hb2 : b ^ 2 * a = a * b ^ 2 := by
      have : b ^ 2 * a * (b ^ 2)⁻¹ = a := by
        calc b ^ 2 * a * (b ^ 2)⁻¹ = b * (b * a * b⁻¹) * b⁻¹ := by rw [sq]; group
          _ = b * a⁻¹ * b⁻¹ := by rw [hinv]
          _ = (b * a * b⁻¹)⁻¹ := by group
          _ = a := by rw [hinv, inv_inv]
      calc b ^ 2 * a = b ^ 2 * a * (b ^ 2)⁻¹ * b ^ 2 := by group
        _ = a * b ^ 2 := by rw [this]
    have hcop : Nat.Coprime 2 (orderOf b) :=
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3)).coprime_dvd_right
        (orderOf_dvd_of_pow_eq_one hb)
    obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
    have hbc : b * a = a * b := by
      rw [← hr]
      exact ((Commute.pow_left hb2 r : Commute ((b ^ 2) ^ r) a)).eq
    have : a⁻¹ = a := by
      rw [← hinv]
      calc b * a * b⁻¹ = a * b * b⁻¹ := by rw [hbc]
        _ = a := by group
    apply ha1
    have h2 : a ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [← this]; exact inv_mul_cancel a
    calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha3, h2]; group

theorem eq_of_le_of_noncomm {A Z B : Subgroup Y} (hA : Heis27 A Z) (hBA : B ≤ A) {s d : Y}
    (hs : s ∈ B) (hd : d ∈ B) (hsd : s * d ≠ d * s) : B = A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine eq_of_le_of_card_ge hBA ?_
  rw [hA.card]
  have hdvd : Nat.card B ∣ 27 := hA.card ▸ card_dvd_of_le hBA
  have hnc : ¬ ∀ a b : ↥B, a * b = b * a := fun h =>
    hsd (congrArg Subtype.val (h ⟨s, hs⟩ ⟨d, hd⟩))
  have : Nat.card B ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 27 = {1, 3, 9, 27} := by decide
  rw [hdiv] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h | h | h
  · exfalso
    apply hnc
    haveI : Subsingleton ↥B := (Nat.card_eq_one_iff_unique.mp h).1
    intro a b
    exact Subsingleton.elim _ _
  · exfalso
    apply hnc
    haveI : IsCyclic ↥B := isCyclic_of_prime_card h
    letI := IsCyclic.commGroup (α := ↥B)
    exact fun a b => mul_comm a b
  · exfalso
    exact hnc (IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by rw [h]; norm_num))
  · rw [h]

theorem conj_mem_oUpperTwo {T : Subgroup Y} {g a : Y} (hg : g ∈ T) (ha : a ∈ oUpperTwo T) :
    g * a * g⁻¹ ∈ oUpperTwo T := by
  have hTg : T.map (MulAut.conj g).toMonoidHom = T := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact T.mul_mem (T.mul_mem hg hx) (T.inv_mem hg)
    · intro x hx
      refine ⟨g⁻¹ * x * g, T.mul_mem (T.mul_mem (T.inv_mem hg) hx) hg, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have h := map_oUpperTwo (MulAut.conj g).toMonoidHom T
  rw [hTg] at h
  have hmem : g * a * g⁻¹ ∈ (oUpperTwo T).map (MulAut.conj g).toMonoidHom :=
    ⟨a, ha, by simp [MulAut.conj_apply]⟩
  rwa [h] at hmem

theorem mem_normalizer_sup_of {A₁ A₂ : Subgroup Y} {g : Y}
    (h₁ : ∀ a ∈ A₁, g * a * g⁻¹ ∈ A₁ ⊔ A₂) (h₂ : ∀ a ∈ A₂, g * a * g⁻¹ ∈ A₁ ⊔ A₂) :
    g ∈ normalizer ((A₁ ⊔ A₂ : Subgroup Y) : Set Y) := by
  refine mem_normalizer_fintype fun x hx => ?_
  have hle : (A₁ ⊔ A₂).map (MulAut.conj g).toMonoidHom ≤ A₁ ⊔ A₂ := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using h₁ a ha
    · rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using h₂ a ha
  exact hle ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem exists_common_two_subgroup {D : Subgroup Y} [D.Normal] (hD3 : IsPGroup 3 D)
    {T₁ T₂ : Subgroup Y} (h₁ : IsSubnormal T₁ ⊤) (h₂ : IsSubnormal T₂ ⊤)
    (hT₁ : ∀ t ∈ T₁, ∃ a : ℕ, t ^ (2 ^ a) ∈ D) (hT₂ : ∀ t ∈ T₂, ∃ a : ℕ, t ^ (2 ^ a) ∈ D)
    {f₁ f₂ : Y} (hf₁ : f₁ ∈ T₁) (hf₂ : f₂ ∈ T₂) (hf₁2 : ∃ k : ℕ, f₁ ^ (2 ^ k) = 1)
    (hf₂2 : ∃ k : ℕ, f₂ ^ (2 ^ k) = 1) :
    ∃ d ∈ D, ∃ S : Subgroup Y, IsPGroup 2 S ∧ f₁ ∈ S ∧ d⁻¹ * f₂ * d ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  set Q : Subgroup (Y ⧸ D) := pCoreOf 2 (⊤ : Subgroup (Y ⧸ D)) with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  have hTQ : ∀ {T : Subgroup Y}, IsSubnormal T ⊤ → (∀ t ∈ T, ∃ a : ℕ, t ^ (2 ^ a) ∈ D) →
      T.map π ≤ Q := by
    intro T hT hTD
    refine SubnormalCommute.le_pCoreOf_of_isSubnormal ?_ ?_
    · have := hT.map π
      rwa [map_top_of_surjective π hπs] at this
    · rintro ⟨x, ⟨t, ht, rfl⟩⟩
      obtain ⟨a, ha⟩ := hTD t ht
      refine ⟨a, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ha
  set O : Subgroup Y := Q.comap π with hO
  have hf₁O : f₁ ∈ O := hTQ h₁ hT₁ (mem_map_of_mem π hf₁)
  have hf₂O : f₂ ∈ O := hTQ h₂ hT₂ (mem_map_of_mem π hf₂)
  have hDO : D ≤ O := fun d hd => by
    show π d ∈ Q
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff d).mpr hd]
    exact one_mem Q
  have h2f : ∀ {f : Y} (hfO : f ∈ O), (∃ k : ℕ, f ^ (2 ^ k) = 1) →
      IsPGroup 2 ((zpowers f).subgroupOf O) := by
    rintro f hfO ⟨k, hk⟩ ⟨⟨g, hgO⟩, hg⟩
    have hg' : g ∈ zpowers f := by simpa [mem_subgroupOf] using hg
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hg'
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨S₁, hS₁⟩ := (h2f hf₁O hf₁2).exists_le_sylow
  obtain ⟨S₂, hS₂⟩ := (h2f hf₂O hf₂2).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥O S₁ S₂
  set S : Subgroup Y := (S₁ : Subgroup ↥O).map O.subtype with hS
  have hS2 : IsPGroup 2 S := S₁.isPGroup'.map O.subtype
  have hf₁S : f₁ ∈ S := ⟨⟨f₁, hf₁O⟩, hS₁ (mem_subgroupOf.mpr (mem_zpowers f₁)), rfl⟩
  have hf₂g : (g : Y)⁻¹ * f₂ * g ∈ S := by
    have h : (⟨f₂, hf₂O⟩ : ↥O) ∈ (S₂ : Subgroup ↥O) :=
      hS₂ (mem_subgroupOf.mpr (mem_zpowers f₂))
    rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at h
    refine ⟨_, h, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  set φ : ↥O →* Y ⧸ D := π.comp O.subtype with hφ
  have hker : φ.ker = D.subgroupOf O := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf]
    rfl
  have hrange : φ.range = Q := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact x.2
    · intro q hq
      obtain ⟨y, rfl⟩ := hπs q
      exact ⟨⟨y, hq⟩, rfl⟩
  have hOcard : Nat.card O = Nat.card Q * Nat.card D := by
    have h1 := card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hker,
      Nat.card_congr (subgroupOfEquivOfLe hDO).toEquiv] at h1
    exact h1
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hQ2
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hD3
  have hS₁card : 2 ^ m ∣ Nat.card S := by
    rw [hS, card_map_of_injective O.subtype_injective]
    have hidx := (S₁ : Subgroup ↥O).card_mul_index
    have hnd : ¬ 2 ∣ (S₁ : Subgroup ↥O).index := S₁.not_dvd_index
    have hcop : Nat.Coprime (2 ^ m) (S₁ : Subgroup ↥O).index :=
      Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd)
    have hdvd : 2 ^ m ∣ Nat.card S₁ * (S₁ : Subgroup ↥O).index := by
      rw [hidx, hOcard, hm]
      exact dvd_mul_right _ _
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hDS : D ⊔ S = O := by
    refine eq_of_le_of_card_ge (sup_le hDO (map_subtype_le _)) ?_
    rw [hOcard, hm, hn]
    have h3 : 3 ^ n ∣ Nat.card ↥(D ⊔ S) := hn ▸ card_dvd_of_le le_sup_left
    have h2 : 2 ^ m ∣ Nat.card ↥(D ⊔ S) := hS₁card.trans (card_dvd_of_le le_sup_right)
    have hcop : Nat.Coprime (2 ^ m) (3 ^ n) :=
      Nat.Coprime.pow m n (by norm_num : Nat.Coprime 2 3)
    exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd h2 h3)
  have hgmem : (g : Y) ∈ (↑(D ⊔ S) : Set Y) := by rw [hDS]; exact g.2
  rw [normal_mul] at hgmem
  obtain ⟨d, hd, s, hs, hgds⟩ := Set.mem_mul.mp hgmem
  refine ⟨d, hd, S, hS2, hf₁S, ?_⟩
  have e : d⁻¹ * f₂ * d = s * ((g : Y)⁻¹ * f₂ * g) * s⁻¹ := by rw [← hgds]; group
  rw [e]
  exact S.mul_mem (S.mul_mem hs hf₂g) (S.inv_mem hs)

theorem subnormalSUThreeTwoCommute_holds : SubnormalSUThreeTwoCommute := by
  intro Y _ _ _ T₁ T₂ h₁ h₂ hu₁ hu₂ hne
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s₁, d₁, z₁, f₁, -, -, hf₁T, hf₁4, hs₁u, hd₁u, hz₁c, hH₁, hs₁O, hd₁O, hsd₁⟩ :=
    exists_data_of_su hu₁
  obtain ⟨s₂, d₂, z₂, f₂, -, -, hf₂T, hf₂4, hs₂u, hd₂u, hz₂c, hH₂, hs₂O, hd₂O, hsd₂⟩ :=
    exists_data_of_su hu₂
  set A₁ := oUpperTwo T₁ with hA₁
  set A₂ := oUpperTwo T₂ with hA₂
  set D : Subgroup Y := pCoreOf 3 (⊤ : Subgroup Y) with hDdef
  have hD3 : IsPGroup 3 D := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 ⊤
  have hDN : ∀ g : Y, g ∈ normalizer (D : Set Y) := fun g =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 3 ⊤ (le_normalizer (mem_top g))
  haveI hDn : D.Normal := normalizer_eq_top_iff.mp (eq_top_iff.mpr fun g _ => hDN g)
  have hD3el : ∀ x ∈ D, ∃ k : ℕ, x ^ (3 ^ k) = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hD3 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hA3 : ∀ {A Z : Subgroup Y}, Heis27 A Z → IsPGroup 3 A := fun hH ⟨a, ha⟩ =>
    ⟨1, Subtype.ext (by simpa using hH.cube a ha)⟩
  have hA₁D : A₁ ≤ D :=
    SubnormalCommute.le_pCoreOf_of_isSubnormal (isSubnormal_oUpperTwo h₁) (hA3 hH₁)
  have hA₂D : A₂ ≤ D :=
    SubnormalCommute.le_pCoreOf_of_isSubnormal (isSubnormal_oUpperTwo h₂) (hA3 hH₂)
  have hD2 : ¬ 2 ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hD3
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hcommT : ∀ {T : Subgroup Y}, IsSubnormal T ⊤ → ∀ {t : Y}, t ∈ T →
      (∃ k : ℕ, t ^ (2 ^ k) = 1) → ⁅D, zpowers t⁆ ≤ oUpperTwo T := by
    intro T hT t ht hk
    obtain ⟨k, hk⟩ := hk
    have h2t : IsPGroup 2 (zpowers t) := by
      rintro ⟨g, hg⟩
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
      refine ⟨k, Subtype.ext ?_⟩
      change (t ^ n) ^ 2 ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    have hE := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 2
      Nat.prime_two (zpowers t) D h2t hD2 (fun g _ => hDN g)
    have hET := SubnormalCommute.commutator_zpowers_le_of_isSubnormal hT hE ht le_top
    intro x hx
    have hxD : x ∈ D := commutator_le_left D (zpowers t) hx
    obtain ⟨k', hk'⟩ := hD3el x hxD
    exact subset_closure ⟨hET hx,
      (Odd.pow (by decide : Odd 3)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hk')⟩
  have h4 : ∀ {f : Y}, f ^ 4 = 1 → ∃ k : ℕ, (f ^ 2) ^ (2 ^ k) = 1 := fun hf =>
    ⟨1, by rw [pow_one, ← pow_mul]; exact hf⟩
  have h4' : ∀ {f : Y}, f ^ 4 = 1 → ∃ k : ℕ, f ^ (2 ^ k) = 1 := fun hf => ⟨2, hf⟩
  have hsq_mem : ∀ {B : Subgroup Y} {u s : Y}, s ∈ B → u * s * u⁻¹ = s⁻¹ → s ^ 3 = 1 →
      s ∈ ⁅B, zpowers u⁆ := by
    intro B u s hs hus hs3
    have h1 : s * u * s⁻¹ * u⁻¹ = s ^ 2 := by
      rw [show s * u * s⁻¹ * u⁻¹ = s * (u * s * u⁻¹)⁻¹ by group, hus, inv_inv, sq]
    have h2 : s ^ 2 ∈ ⁅B, zpowers u⁆ := by
      have := commutator_mem_commutator hs (mem_zpowers u)
      rwa [commutatorElement_def, h1] at this
    have h3 : s = (s ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hs3, one_mul]
    rw [h3]
    exact pow_mem h2 2
  have hDu₁ : ⁅D, zpowers (f₁ ^ 2)⁆ = A₁ :=
    eq_of_le_of_noncomm hH₁ (hcommT h₁ (pow_mem hf₁T 2) (h4 hf₁4))
      (hsq_mem (hA₁D hs₁O) hs₁u (hH₁.cube _ hs₁O)) (hsq_mem (hA₁D hd₁O) hd₁u (hH₁.cube _ hd₁O))
      hsd₁
  have hDu₂ : ⁅D, zpowers (f₂ ^ 2)⁆ = A₂ :=
    eq_of_le_of_noncomm hH₂ (hcommT h₂ (pow_mem hf₂T 2) (h4 hf₂4))
      (hsq_mem (hA₂D hs₂O) hs₂u (hH₂.cube _ hs₂O)) (hsq_mem (hA₂D hd₂O) hd₂u (hH₂.cube _ hd₂O))
      hsd₂
  have hA₁N : D ≤ normalizer (A₁ : Set Y) := hDu₁ ▸ le_normalizer_commutator_zpowers (hDN _)
  have hA₂N : D ≤ normalizer (A₂ : Set Y) := hDu₂ ▸ le_normalizer_commutator_zpowers (hDN _)
  have hnorm : ∀ {A : Subgroup Y}, D ≤ normalizer (A : Set Y) → ∀ x ∈ D, ∀ a ∈ A,
      x * a * x⁻¹ ∈ A := fun hN x hx a ha => (mem_normalizer_iff.mp (hN hx) a).mp ha
  by_cases hint : A₁ ⊓ A₂ = ⊥
  · rw [eq_bot_iff, ← hint, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · have := hnorm hA₁N b (hA₂D hb) a⁻¹ (inv_mem ha)
      rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
      exact A₁.mul_mem ha this
    · have := hnorm hA₂N a (hA₁D ha) b hb
      exact A₂.mul_mem this (inv_mem hb)
  have hz3 : ∀ {z : Y} {A : Subgroup Y}, Heis27 A (zpowers z) → orderOf z = 3 := by
    intro z A hH
    have := hH.card_center
    rwa [Nat.card_zpowers] at this
  have hz₁3 := hz3 hH₁
  have hz₂3 := hz3 hH₂
  have hgen : ∀ {z c : Y}, orderOf z = 3 → c ∈ zpowers z → c ≠ 1 → zpowers c = zpowers z := by
    intro z c hz hc hc1
    refine eq_of_le_of_card_ge (zpowers_le.mpr hc) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hz]
    have hc3 : c ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hz,
        pow_orderOf_eq_one, one_zpow]
    rw [orderOf_eq_prime hc3 hc1]
  have hZ₁A₂ : zpowers z₁ ≤ A₂ := by
    by_contra hn
    apply hint
    rw [eq_bot_iff]
    rintro n ⟨hnA₁, hnA₂⟩
    rw [mem_bot]
    have hcen : ∀ a ∈ A₁, n * a = a * n := by
      intro a ha
      have hcZ : n * a * n⁻¹ * a⁻¹ ∈ zpowers z₁ := hH₁.comm_mem n hnA₁ a ha
      have hcA₂ : n * a * n⁻¹ * a⁻¹ ∈ A₂ := by
        have := hnorm hA₂N a (hA₁D ha) n⁻¹ (inv_mem hnA₂)
        rw [show n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) by group]
        exact A₂.mul_mem hnA₂ this
      have hc1 : n * a * n⁻¹ * a⁻¹ = 1 := by
        by_contra hc1
        apply hn
        rw [← hgen hz₁3 hcZ hc1]
        exact zpowers_le.mpr hcA₂
      calc n * a = n * a * n⁻¹ * a⁻¹ * (a * n) := by group
        _ = a * n := by rw [hc1, one_mul]
    have hnZ := hH₁.center_le n hnA₁ hcen
    by_contra hn1
    apply hn
    rw [← hgen hz₁3 hnZ hn1]
    exact zpowers_le.mpr hnA₂
  have hDz : ∀ {A : Subgroup Y} {z : Y}, Heis27 A (zpowers z) → D ≤ normalizer (A : Set Y) →
      ∀ x ∈ D, x * z = z * x := by
    intro A z hH hAN x hx
    have hxz : x * z * x⁻¹ ∈ zpowers z := by
      apply hH.center_le
      · exact hnorm hAN x hx z (hH.le (mem_zpowers z))
      · intro a ha
        have ha' : x⁻¹ * a * x ∈ A := by
          have := hnorm hAN x⁻¹ (inv_mem hx) a ha
          simpa using this
        have hc := hH.central z (mem_zpowers z) _ ha'
        calc x * z * x⁻¹ * a = x * (z * (x⁻¹ * a * x)) * x⁻¹ := by group
          _ = x * ((x⁻¹ * a * x) * z) * x⁻¹ := by rw [hc]
          _ = a * (x * z * x⁻¹) := by group
    obtain ⟨k, hk⟩ := hD3el x hx
    exact commute_of_conj_mem_zpowers_three (hz3 hH) hk hxz
  have hZeq : zpowers z₁ = zpowers z₂ := by
    have hz₁A₂ : z₁ ∈ A₂ := hZ₁A₂ (mem_zpowers z₁)
    refine eq_of_le_of_card_ge (zpowers_le.mpr ?_) ?_
    · apply hH₂.center_le z₁ hz₁A₂
      intro b hb
      exact (hDz hH₁ hA₁N b (hA₂D hb)).symm
    · rw [hH₁.card_center, hH₂.card_center]
  set Z := zpowers z₂ with hZ
  have hH₁' : Heis27 A₁ Z := hZeq ▸ hH₁
  set K := A₁ ⊔ A₂ with hK
  have hKD : K ≤ D := sup_le hA₁D hA₂D
  have hKN : D ≤ normalizer (K : Set Y) := fun x hx =>
    mem_normalizer_sup_of (fun a ha => mem_sup_left (hnorm hA₁N x hx a ha))
      (fun a ha => mem_sup_right (hnorm hA₂N x hx a ha))
  have hKcard : Nat.card K ≤ 243 := by
    have hle : A₁ ≤ normalizer (A₂ : Set Y) := hA₁D.trans hA₂N
    haveI := Subgroup.normal_subgroupOf_of_le_normalizer hle
    haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hle
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A₁ A₂ hle
    have c1 := card_eq_card_quotient_mul_card_subgroup (A₂.subgroupOf A₁)
    have c2 := card_eq_card_quotient_mul_card_subgroup (A₂.subgroupOf (A₁ ⊔ A₂))
    rw [Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv, hH₂.card,
      ← Nat.card_congr e.toEquiv] at c2
    have hZA₁ : Z ≤ A₁ := hH₁'.le
    have h3 : 3 ≤ Nat.card (A₂.subgroupOf A₁) := by
      have hZs : Z.subgroupOf A₁ ≤ A₂.subgroupOf A₁ := fun x hx =>
        mem_subgroupOf.mpr (hH₂.le (mem_subgroupOf.mp hx))
      have := card_le_of_le hZs
      rwa [Nat.card_congr (subgroupOfEquivOfLe hZA₁).toEquiv, hH₂.card_center] at this
    rw [hH₁.card] at c1
    rw [c2]
    nlinarith
  have hfK : ∀ {T : Subgroup Y} {f : Y}, IsSubnormal T ⊤ → f ∈ T → f ^ 4 = 1 →
      (oUpperTwo T = A₁ ∨ oUpperTwo T = A₂) → f ∈ normalizer (K : Set Y) := by
    intro T f hT hfT hf4 hTA
    have hc := hcommT hT hfT (h4' hf4)
    have key : ∀ a ∈ D, f * a * f⁻¹ = a * (a⁻¹ * f * a * f⁻¹) := fun a _ => by group
    have hcm : ∀ a ∈ D, a⁻¹ * f * a * f⁻¹ ∈ oUpperTwo T := fun a ha => by
      have := commutator_mem_commutator (inv_mem ha) (mem_zpowers f)
      rw [commutatorElement_def, inv_inv] at this
      exact hc this
    have hTK : oUpperTwo T ≤ K := by
      rcases hTA with h | h <;> rw [h]
      · exact le_sup_left
      · exact le_sup_right
    refine mem_normalizer_sup_of (fun a ha => ?_) (fun a ha => ?_)
    · rw [key a (hA₁D ha)]
      exact mul_mem (mem_sup_left ha) (hTK (hcm a (hA₁D ha)))
    · rw [key a (hA₂D ha)]
      exact mul_mem (mem_sup_right ha) (hTK (hcm a (hA₂D ha)))
  have hf₁K : f₁ ∈ normalizer (K : Set Y) := hfK h₁ hf₁T hf₁4 (Or.inl rfl)
  have hf₂K : f₂ ∈ normalizer (K : Set Y) := hfK h₂ hf₂T hf₂4 (Or.inr rfl)
  have hf₁Z : ∀ w ∈ Z, f₁ * w = w * f₁ := by
    intro w hw
    rw [← hZeq] at hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact ((Commute.zpow_right (hz₁c f₁ hf₁T).symm k : Commute f₁ (z₁ ^ k))).eq
  have hf₂Z : ∀ w ∈ Z, f₂ * w = w * f₂ := by
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact ((Commute.zpow_right (hz₂c f₂ hf₂T).symm k : Commute f₂ (z₂ ^ k))).eq
  have hDZ : ∀ x ∈ D, ∀ w ∈ Z, x * w = w * x := by
    intro x hx w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact ((Commute.zpow_right (hDz hH₂ hA₂N x hx) k : Commute x (z₂ ^ k))).eq
  have haOf₁ : SUPair.aOf K f₁ = A₁ :=
    eq_of_le_of_noncomm hH₁' ((commutator_mono hKD le_rfl).trans hDu₁.le)
      (hsq_mem (mem_sup_left hs₁O) hs₁u (hH₁.cube _ hs₁O))
      (hsq_mem (mem_sup_left hd₁O) hd₁u (hH₁.cube _ hd₁O)) hsd₁
  have haOf₂ : SUPair.aOf K f₂ = A₂ :=
    eq_of_le_of_noncomm hH₂ ((commutator_mono hKD le_rfl).trans hDu₂.le)
      (hsq_mem (mem_sup_right hs₂O) hs₂u (hH₂.cube _ hs₂O))
      (hsq_mem (mem_sup_right hd₂O) hd₂u (hH₂.cube _ hd₂O)) hsd₂
  have hgood₁ : Good K Z f₁ :=
    ⟨hf₁4, haOf₁ ▸ hH₁', haOf₁ ▸ le_sup_left, haOf₁ ▸ hKD.trans hA₁N⟩
  have hgood₂ : Good K Z f₂ :=
    ⟨hf₂4, haOf₂ ▸ hH₂, haOf₂ ▸ le_sup_right, haOf₂ ▸ hKD.trans hA₂N⟩
  have hTD : ∀ {T : Subgroup Y}, oUpperTwo T ≤ D → ∀ t ∈ T, ∃ a : ℕ, t ^ (2 ^ a) ∈ D :=
    fun hTD t ht => by
      obtain ⟨a, ha⟩ := exists_two_pow_mem ht
      exact ⟨a, hTD ha⟩
  obtain ⟨d, hdD, S, hS2, hf₁S, hf₂S⟩ := exists_common_two_subgroup hD3 h₁ h₂ (hTD hA₁D)
    (hTD hA₂D) hf₁T hf₂T (h4' hf₁4) (h4' hf₂4)
  have hdK : d⁻¹ ∈ normalizer (K : Set Y) := hKN (inv_mem hdD)
  have hgood₂' : Good K Z (d⁻¹ * f₂ * d) := by
    have := hgood₂.conj hdK (hDZ _ (inv_mem hdD))
    rwa [inv_inv] at this
  have haOf₂' : SUPair.aOf K (d⁻¹ * f₂ * d) = A₂ := by
    rw [show d⁻¹ * f₂ * d = d⁻¹ * f₂ * d⁻¹⁻¹ by rw [inv_inv], aOf_conj hdK, haOf₂,
      conjS_eq_of_mem_normalizer (hA₂N (inv_mem hdD))]
  set P : Subgroup Y := closure {f₁, d⁻¹ * f₂ * d} with hP
  have hPS : P ≤ S := by
    rw [hP, closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hf₁S
    · exact hf₂S
  have hPK : P ≤ normalizer (K : Set Y) := by
    rw [hP, closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hf₁K
    · exact mul_mem (mul_mem hdK hf₂K) (hKN hdD)
  have hPZ' : P ≤ centralizer (Z : Set Y) := by
    rw [hP, closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_centralizer_iff]
    rcases hx with rfl | rfl
    · intro w hw
      exact (hf₁Z w hw).symm
    · intro w hw
      have e1 := hDZ d hdD w hw
      have e2 := hf₂Z w hw
      have e3 := hDZ _ (inv_mem hdD) w hw
      calc w * (d⁻¹ * f₂ * d) = d⁻¹ * (w * f₂) * d := by
            rw [show w * (d⁻¹ * f₂ * d) = (w * d⁻¹) * f₂ * d by group, ← e3]; group
        _ = d⁻¹ * (f₂ * w) * d := by rw [e2]
        _ = d⁻¹ * f₂ * (w * d) := by group
        _ = d⁻¹ * f₂ * d * w := by rw [← e1]; group
  have hPZ : ∀ g ∈ P, ∀ w ∈ Z, g * w = w * g := fun g hg w hw =>
    ((mem_centralizer_iff.mp (hPZ' hg)) w hw).symm
  have hclaim := good_claim hKcard P (hS2.to_le hPS) hPK hPZ f₁ (subset_closure (by simp))
    (d⁻¹ * f₂ * d) (subset_closure (by simp)) hgood₁ hgood₂'
  rw [haOf₂', haOf₁] at hclaim
  rcases hclaim with h | h
  · exact absurd h.symm hne
  · rw [commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact (h a ha b hb).symm

end CFSG.AGLEmbedding.SUPair

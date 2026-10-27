module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab1
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

@[expose] def HasU4Quot {S : Type} [Group S] (C : Subgroup S) : Prop :=
  ∃ (A : Subgroup S) (T : Type) (_ : Group T) (_ : IsSimpleGroup T) (_ : ↥A →* T),
    A ≤ C ∧ Nat.card T = 25920 ∧ ∃ f : ↥A →* T, Function.Surjective f

theorem HasU4Quot.of_surj {S : Type} [Group S] {C A : Subgroup S} (hAC : A ≤ C) {T : Type}
    [Group T] [IsSimpleGroup T] (hT : Nat.card T = 25920) (f : ↥A →* T)
    (hf : Function.Surjective f) : HasU4Quot C :=
  ⟨A, T, inferInstance, inferInstance, f, hAC, hT, f, hf⟩

theorem HasU4Quot.dvd_card {S : Type} [Group S] [Finite S] {C : Subgroup S} (h : HasU4Quot C) :
    25920 ∣ Nat.card C := by
  obtain ⟨A, T, _, _, _, hAC, hT, f, hf⟩ := h
  have h1 := Subgroup.card_dvd_of_surjective hf
  rw [hT] at h1
  exact h1.trans (Subgroup.card_dvd_of_le hAC)

theorem not_comm_of_card_25920 {T : Type} [Group T] [IsSimpleGroup T] (hT : Nat.card T = 25920) :
    ¬ ∀ a b : T, a * b = b * a := by
  intro hcomm
  letI : CommGroup T := { (inferInstance : Group T) with mul_comm := hcomm }
  have hprime := (CommGroup.is_simple_iff_prime_card (α := T)).1 inferInstance
  rw [hT] at hprime
  exact absurd hprime (by norm_num)

theorem commutator_eq_top_of_card_25920 {T : Type} [Group T] [IsSimpleGroup T]
    (hT : Nat.card T = 25920) : commutator T = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator T) with h | h
  · exfalso
    apply not_comm_of_card_25920 hT
    intro a b
    have : ⁅a, b⁆ ∈ commutator T := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h

theorem HasU4Quot.not_isSolvable {S : Type} [Group S] {C : Subgroup S} (h : HasU4Quot C) :
    ¬ Group.IsSolvable ↥C := by
  obtain ⟨A, T, _, _, _, hAC, hT, f, hf⟩ := h
  intro hC
  haveI : Group.IsSolvable ↥A :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAC)
  haveI : Group.IsSolvable T := Group.isSolvable_of_surjective hf
  exact not_comm_of_card_25920 hT (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance)

theorem HasU4Quot.map_equiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {C : Subgroup S}
    (h : HasU4Quot C) : HasU4Quot (C.map e.toMonoidHom) := by
  obtain ⟨A, T, _, _, _, hAC, hT, f, hf⟩ := h
  refine HasU4Quot.of_surj (Subgroup.map_mono hAC) hT
    (f.comp (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).symm.toMonoidHom) ?_
  exact hf.comp (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).symm.surjective

theorem HasU4Quot.of_comm_le {S : Type} [Group S] {C C' : Subgroup S} (hC' : C' ≤ C)
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ C') (h : HasU4Quot C) : HasU4Quot C' := by
  obtain ⟨A, T, _, _, _, hAC, hT, f, hf⟩ := h
  have hAA : A ⊓ C' ≤ A := inf_le_left
  let M : Subgroup T := ((A ⊓ C').subgroupOf A).map f
  have hMn : M.Normal := by
    refine ⟨fun m hm t => ?_⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hm
    obtain ⟨a, rfl⟩ := hf t
    refine Subgroup.mem_map.2 ⟨a * x * a⁻¹, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxA : (x : S) ∈ A ⊓ C' := hx
    refine ⟨?_, ?_⟩
    · exact A.mul_mem (A.mul_mem a.2 x.2) (A.inv_mem a.2)
    · have h1 : ⁅(a : S), (x : S)⁆ ∈ C' := hcomm _ (hAC a.2) _ (hAC x.2)
      have h2 : (a : S) * x * (a : S)⁻¹ = ⁅(a : S), (x : S)⁆ * x := by
        simp [commutatorElement_def, mul_assoc]
      show (a : S) * x * (a : S)⁻¹ ∈ C'
      rw [h2]
      exact C'.mul_mem h1 hxA.2
  have hMtop : M = ⊤ := by
    haveI := hMn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hM | hM
    · exfalso
      apply not_comm_of_card_25920 hT
      intro t₁ t₂
      obtain ⟨a₁, rfl⟩ := hf t₁
      obtain ⟨a₂, rfl⟩ := hf t₂
      have hc : ⁅a₁, a₂⁆ ∈ (A ⊓ C').subgroupOf A := by
        rw [Subgroup.mem_subgroupOf]
        refine ⟨?_, ?_⟩
        · exact A.mul_mem (A.mul_mem (A.mul_mem a₁.2 a₂.2) (A.inv_mem a₁.2)) (A.inv_mem a₂.2)
        · exact hcomm _ (hAC a₁.2) _ (hAC a₂.2)
      have : f ⁅a₁, a₂⁆ ∈ M := Subgroup.mem_map_of_mem f hc
      rw [hM, Subgroup.mem_bot, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact hM
  refine HasU4Quot.of_surj (inf_le_right : A ⊓ C' ≤ C') hT
    (f.comp (Subgroup.inclusion hAA)) ?_
  intro t
  have ht : t ∈ M := by rw [hMtop]; exact Subgroup.mem_top t
  obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.1 ht
  rw [Subgroup.mem_subgroupOf] at hx
  refine ⟨⟨(x : S), hx⟩, ?_⟩
  show f (Subgroup.inclusion hAA ⟨(x : S), hx⟩) = t
  have hx' : Subgroup.inclusion hAA ⟨(x : S), hx⟩ = x := Subtype.ext rfl
  rw [hx']
  exact hxt

theorem HasU4Quot.exists_perfect {S : Type} [Group S] [Finite S] {C : Subgroup S}
    (h : HasU4Quot C) : ∃ L : Subgroup S, L ≤ C ∧ Group.IsPerfect ↥L ∧ 25920 ∣ Nat.card L := by
  classical
  obtain ⟨A, T, _, _, _, hAC, hT, f, hf⟩ := h
  have hTp : commutator T = ⊤ := commutator_eq_top_of_card_25920 hT
  let P : Subgroup ↥A → Prop := fun L₀ => L₀.map f = ⊤
  have hex : ∃ n, ∃ L₀ : Subgroup ↥A, P L₀ ∧ Nat.card L₀ = n :=
    ⟨_, ⊤, by simpa [P, MonoidHom.range_eq_map] using MonoidHom.range_eq_top.2 hf, rfl⟩
  obtain ⟨L₀, hL₀P, hL₀c⟩ := Nat.find_spec hex
  have hmin : ∀ L₁ : Subgroup ↥A, P L₁ → Nat.card L₀ ≤ Nat.card L₁ := fun L₁ hL₁ => by
    rw [hL₀c]
    exact Nat.find_min' hex ⟨L₁, hL₁, rfl⟩
  have hcomm_le : ⁅L₀, L₀⁆ ≤ L₀ := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact L₀.mul_mem (L₀.mul_mem (L₀.mul_mem ha hb) (L₀.inv_mem ha)) (L₀.inv_mem hb)
  have hPcomm : P ⁅L₀, L₀⁆ := by
    show (⁅L₀, L₀⁆).map f = ⊤
    rw [Subgroup.map_commutator]
    have h1 : L₀.map f = ⊤ := hL₀P
    rw [h1]
    rw [commutator_def] at hTp
    exact hTp
  have hPeq : ⁅L₀, L₀⁆ = L₀ :=
    Subgroup.eq_of_le_of_card_ge hcomm_le (hmin _ hPcomm)
  refine ⟨L₀.map A.subtype, (Subgroup.map_subtype_le L₀).trans hAC, ?_, ?_⟩
  · rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, hPeq]
  · rw [Subgroup.card_map_of_injective A.subtype_injective]
    have h2 := Subgroup.card_map_dvd L₀ f
    have h3 : L₀.map f = ⊤ := hL₀P
    rw [h3, Subgroup.card_top, hT] at h2
    exact h2

@[expose] def U4InnModel (M : Type) [Group M] : Prop :=
  IsSimpleGroup M → ∀ u : MulAut M, u ^ 3 = 1 → HasU4Quot (u4Fix u) →
    GLAPPrimeCore 3 ↥(u4Fix u) = ⊥

theorem u4Fix_congr {S T : Type} [Group S] [Group T] (e : S ≃* T) (u : MulAut S) :
    u4Fix (MulAut.congr e u) = (u4Fix u).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    show u (e.symm y) = e.symm y
    apply e.injective
    have : (MulAut.congr e u) y = y := hy
    simpa [MulAut.congr_apply] using this
  · rintro ⟨x, hx, rfl⟩
    have hx' : u x = x := hx
    show (MulAut.congr e u) (e x) = e x
    simp [MulAut.congr_apply, hx']

theorem pPrimeCore_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.pPrimeCore 3 Y = ⊥) : CFSG.pPrimeCore 3 X = ⊥ := by
  have := CFSG.pPrimeCore_map_iso 3 e
  rw [h] at this
  exact (Subgroup.map_eq_bot_iff_of_injective _ (show Function.Injective e.toMonoidHom from e.injective)).1 this

theorem U4InnModel.of_mulEquiv {S M : Type} [Group S] [Group M] (e : S ≃* M) (h : U4InnModel M) :
    U4InnModel S := by
  intro hS u hu3 hq
  haveI : IsSimpleGroup M := e.symm.isSimpleGroup
  have hu3' : (MulAut.congr e u) ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hq' : HasU4Quot (u4Fix (MulAut.congr e u)) := by
    rw [u4Fix_congr]
    exact hq.map_equiv e
  have h1 := h inferInstance _ hu3' hq'
  have e2 : ↥(u4Fix u) ≃* ↥(u4Fix (MulAut.congr e u)) := by
    rw [u4Fix_congr]
    exact Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective
  exact pPrimeCore_eq_bot_of_mulEquiv e2 h1

theorem pPrimeCore_eq_bot_of_simple {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (h3 : 3 ∣ Nat.card X) : CFSG.pPrimeCore 3 X = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hK hcop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top] at hcop
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)

theorem u4Fix_one {M : Type} [Group M] : u4Fix (1 : MulAut M) = ⊤ := by
  ext x
  simp [u4Fix]

theorem pPrimeCore_u4Fix_one {M : Type} [Group M] [Finite M] [IsSimpleGroup M]
    (h3 : 3 ∣ Nat.card M) : GLAPPrimeCore 3 ↥(u4Fix (1 : MulAut M)) = ⊥ := by
  rw [u4Fix_one]
  exact pPrimeCore_eq_bot_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup M) ≃* M)
    (pPrimeCore_eq_bot_of_simple h3)

theorem centralizer_map_equiv {G H : Type*} [Group G] [Group H] (τ : G ≃* H) (s : G) :
    (Subgroup.centralizer ({s} : Set G)).map τ.toMonoidHom =
      Subgroup.centralizer ({τ s} : Set H) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    show τ x * τ s = τ s * τ x
    rw [← map_mul, ← map_mul, hx']
  · intro hy
    refine ⟨τ.symm y, ?_, τ.apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply τ.injective
    rw [map_mul, map_mul, τ.apply_symm_apply]
    exact hy

theorem pPrimeCore_centralizer_of_equiv {G H : Type*} [Group G] [Group H] (τ : G ≃* H) (s : G)
    (h : CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({τ s} : Set H)) = ⊥) :
    CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  let e : ↥(Subgroup.centralizer ({s} : Set G)) ≃* ↥(Subgroup.centralizer ({τ s} : Set H)) :=
    (Subgroup.equivMapOfInjective _ τ.toMonoidHom τ.injective).trans
      (MulEquiv.subgroupCongr (centralizer_map_equiv τ s))
  exact pPrimeCore_eq_bot_of_mulEquiv e h

theorem centralizer_inv_eq {G : Type*} [Group G] (s : G) :
    Subgroup.centralizer ({s⁻¹} : Set G) = Subgroup.centralizer ({s} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact (Commute.inv_right_iff (a := x) (b := s))

theorem u4Fix_conj {G : Type} [Group G] (s : G) :
    u4Fix (MulAut.conj s) = Subgroup.centralizer ({s} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  show MulAut.conj s x = x ↔ x * s = s * x
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc x * s = (s * x * s⁻¹) * s := by rw [h]
      _ = s * x := by group
  · intro h
    rw [← h]
    group

theorem center_eq_bot_of_simple_of_not_comm {T : Type*} [Group T] [IsSimpleGroup T]
    (hnc : ¬ ∀ a b : T, a * b = b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    apply hnc
    intro a b
    have ha : a ∈ Subgroup.center T := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem subgroupOf_perfect {G : Type*} [Group G] {C L : Subgroup G} (hLC : L ≤ C)
    (hL : Group.IsPerfect ↥L) :
    ⁅L.subgroupOf C, L.subgroupOf C⁆ = L.subgroupOf C := by
  have h : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hL
  apply Subgroup.map_injective (f := C.subtype) C.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLC, h]

theorem pPrimeCore_eq_bot_of_normal {G : Type*} [Group G] [Finite G] {ι : Type*}
    (K : ι → Subgroup G) (hKn : ∀ i, (K i).Normal) (hK : ∀ i, CFSG.pPrimeCore 3 ↥(K i) = ⊥)
    (hcent : ∀ g : G, (∀ i, ∀ k ∈ K i, g * k = k * g) → ∃ m : ℕ, g ^ (3 ^ m) = 1) :
    CFSG.pPrimeCore 3 G = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hNK : ∀ i, ∀ x ∈ N, x ∈ K i → x = 1 := by
    intro i x hxN hxK
    haveI := hKn i
    have hbot : N.subgroupOf (K i) ≤ CFSG.pPrimeCore 3 ↥(K i) := by
      refine le_sSup ⟨inferInstance, ?_⟩
      have h1 : Nat.card (N.subgroupOf (K i)) ∣ Nat.card N := by
        let φ : ↥(N.subgroupOf (K i)) →* ↥N :=
          (((K i).subtype.comp (N.subgroupOf (K i)).subtype).codRestrict N fun x => x.2)
        have hφ : Function.Injective φ := by
          intro a b hab
          have := congrArg Subtype.val hab
          exact Subtype.ext (Subtype.ext this)
        exact Subgroup.card_dvd_of_injective φ hφ
      exact Nat.Coprime.coprime_dvd_right h1 hcop
    rw [hK i, le_bot_iff] at hbot
    have : (⟨x, hxK⟩ : ↥(K i)) ∈ N.subgroupOf (K i) := hxN
    rw [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hcomm : ∀ i, ∀ k ∈ K i, n * k = k * n := by
    intro i k hk
    haveI := hKn i
    have h1 : n * k * n⁻¹ * k⁻¹ ∈ N := by
      have : k * n⁻¹ * k⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem hn) k
      have := N.mul_mem hn this
      simpa [mul_assoc] using this
    have h2 : n * k * n⁻¹ * k⁻¹ ∈ K i := by
      have : n * k * n⁻¹ ∈ K i := (hKn i).conj_mem k hk n
      exact (K i).mul_mem this ((K i).inv_mem hk)
    have h3 := hNK i _ h1 h2
    calc n * k = (n * k * n⁻¹ * k⁻¹) * (k * n) := by group
      _ = k * n := by rw [h3, one_mul]
  obtain ⟨m, hm⟩ := hcent n hcomm
  have hdvd : orderOf n ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm
  have hcop2 : Nat.Coprime 3 (orderOf n) := by
    have h1 : orderOf n ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨n, hn⟩ : ↥N)
      rwa [Subgroup.orderOf_mk] at this
    exact Nat.Coprime.coprime_dvd_right h1 hcop
  have h1 : orderOf n = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_left m hcop2).symm) hdvd
  exact orderOf_eq_one_iff.1 h1

theorem pPrimeCore_eq_bot_of_exponent {H : Type*} [Group H]
    (h : ∀ g : H, ∃ m : ℕ, g ^ (3 ^ m) = 1) : CFSG.pPrimeCore 3 H = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  obtain ⟨m, hm⟩ := h n
  have hdvd : orderOf n ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm
  have hcop2 : Nat.Coprime 3 (orderOf n) := by
    have h1 : orderOf n ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨n, hn⟩ : ↥N)
      rwa [Subgroup.orderOf_mk] at this
    exact Nat.Coprime.coprime_dvd_right h1 hcop
  have h1 : orderOf n = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_left m hcop2).symm) hdvd
  exact orderOf_eq_one_iff.1 h1

theorem pPrimeCore_eq_bot_of_ker_range {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hk : CFSG.pPrimeCore 3 ↥f.ker = ⊥) (hr : CFSG.pPrimeCore 3 ↥f.range = ⊥) :
    CFSG.pPrimeCore 3 G = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  rw [eq_bot_iff]
  have hNK : ∀ x ∈ N, x ∈ f.ker → x = 1 := by
    intro x hxN hxK
    have hbot : N.subgroupOf f.ker ≤ CFSG.pPrimeCore 3 ↥f.ker := by
      refine le_sSup ⟨inferInstance, ?_⟩
      have h1 : Nat.card (N.subgroupOf f.ker) ∣ Nat.card N := by
        let φ : ↥(N.subgroupOf f.ker) →* ↥N :=
          (((f.ker).subtype.comp (N.subgroupOf f.ker).subtype).codRestrict N fun x => x.2)
        have hφ : Function.Injective φ := by
          intro a b hab
          have := congrArg Subtype.val hab
          exact Subtype.ext (Subtype.ext this)
        exact Subgroup.card_dvd_of_injective φ hφ
      exact Nat.Coprime.coprime_dvd_right h1 hcop
    rw [hk, le_bot_iff] at hbot
    have : (⟨x, hxK⟩ : ↥f.ker) ∈ N.subgroupOf f.ker := hxN
    rw [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hNr : ∀ x ∈ N, f x = 1 := by
    intro x hxN
    have hn : (N.map f.rangeRestrict).Normal := hN.map _ (MonoidHom.rangeRestrict_surjective f)
    have hbot : N.map f.rangeRestrict ≤ CFSG.pPrimeCore 3 ↥f.range := by
      refine le_sSup ⟨hn, ?_⟩
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd N f.rangeRestrict) hcop
    rw [hr, le_bot_iff] at hbot
    have : f.rangeRestrict x ∈ N.map f.rangeRestrict := Subgroup.mem_map_of_mem _ hxN
    rw [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  intro x hx
  rw [Subgroup.mem_bot]
  exact hNK x hx (MonoidHom.mem_ker.2 (hNr x hx))

theorem pPrimeCore_eq_bot_of_normal_in {M : Type*} [Group M] [Finite M] (X : Subgroup M) {ι : Type*}
    (K : ι → Subgroup M) (hKX : ∀ i, K i ≤ X)
    (hKn : ∀ i, ∀ x ∈ X, ∀ k ∈ K i, x * k * x⁻¹ ∈ K i)
    (hK : ∀ i, CFSG.pPrimeCore 3 ↥(K i) = ⊥)
    (hcent : ∀ g ∈ X, (∀ i, ∀ k ∈ K i, g * k = k * g) → ∃ m : ℕ, g ^ (3 ^ m) = 1) :
    CFSG.pPrimeCore 3 ↥X = ⊥ := by
  refine pPrimeCore_eq_bot_of_normal (fun i => (K i).subgroupOf X) (fun i => ?_) (fun i => ?_) ?_
  · exact (Subgroup.normal_subgroupOf_iff (hKX i)).2 fun k x hk hx => hKn i x hx k hk
  · exact pPrimeCore_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hKX i)) (hK i)
  · intro g hg
    obtain ⟨m, hm⟩ := hcent g.1 g.2 (fun i k hk => by
      have := hg i ⟨k, hKX i hk⟩ hk
      exact congrArg Subtype.val this)
    exact ⟨m, Subtype.ext (by simpa using hm)⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB

end

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bFlip
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bTop

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section Summands

variable {P M : Type} [Group P] [AddCommGroup M] [Module (ZMod 2) M]

theorem eq_one_of_commute_simple_summands (π : P →* (M ≃ₗ[ZMod 2] M)) {ι : Type}
    (U : ι → Submodule (ZMod 2) M) (htop : (⨆ i, U i) = ⊤) (hne : ∀ i, U i ≠ ⊥)
    (hinv : ∀ i g, ∀ x ∈ U i, π g x ∈ U i)
    (hsimple : ∀ i, ∀ W : Submodule (ZMod 2) M, W ≤ U i → (∀ g, ∀ x ∈ W, π g x ∈ W) →
      W = ⊥ ∨ W = U i)
    (c : M ≃ₗ[ZMod 2] M) (hcc : c * c = 1) (hcomm : ∀ x, c * π x = π x * c)
    (hcU : ∀ i, ∀ u ∈ U i, c u ∈ U i) : c = 1 := by
  have hcc' : ∀ v, c (c v) = v := fun v => by
    have := congrArg (fun e : M ≃ₗ[ZMod 2] M => e v) hcc
    exact this
  have hcomm' : ∀ x v, c (π x v) = π x (c v) := fun x v => by
    have := congrArg (fun e : M ≃ₗ[ZMod 2] M => e v) (hcomm x)
    exact this
  have h2 : ∀ v : M, v + v = 0 := fun v => by
    have : (2 : ZMod 2) • v = 0 := by
      rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rwa [two_smul] at this
  have hfix : ∀ i, ∀ u ∈ U i, c u = u := by
    intro i u hu
    let W : Submodule (ZMod 2) M := (U i) ⊓ LinearMap.ker (c.toLinearMap - 1)
    have hWinv : ∀ g, ∀ x ∈ W, π g x ∈ W := by
      rintro g x ⟨hx1, hx2⟩
      refine ⟨hinv i g x hx1, ?_⟩
      have h0 : c x - x = 0 := hx2
      show c (π g x) - π g x = 0
      rw [hcomm', sub_eq_zero]
      rw [sub_eq_zero] at h0
      rw [h0]
    rcases hsimple i W inf_le_left hWinv with hW | hW
    · exfalso
      apply hne i
      rw [eq_bot_iff]
      intro u' hu'
      have hmem : c u' + u' ∈ W := by
        refine ⟨(U i).add_mem (hcU i u' hu') hu', ?_⟩
        show c (c u' + u') - (c u' + u') = 0
        rw [map_add, hcc']
        abel
      rw [hW] at hmem
      have h0 : c u' + u' = 0 := (Submodule.mem_bot _).mp hmem
      have h1 : c u' = u' := by
        have : c u' = -u' := eq_neg_of_add_eq_zero_left h0
        rw [this]
        exact neg_eq_of_add_eq_zero_left (h2 u')
      have hu'W : u' ∈ W := ⟨hu', show c u' - u' = 0 by rw [h1, sub_self]⟩
      rw [hW] at hu'W
      exact hu'W
    · have hu' : u ∈ W := by rw [hW]; exact hu
      have h0 : c u - u = 0 := hu'.2
      exact sub_eq_zero.mp h0
  have hle : (⨆ i, U i) ≤ LinearMap.ker (c.toLinearMap - 1) := by
    refine iSup_le fun i u hu => ?_
    show c u - u = 0
    rw [hfix i u hu, sub_self]
  rw [htop] at hle
  refine LinearEquiv.ext fun v => ?_
  have h0 : c v - v = 0 := hle (Submodule.mem_top (x := v))
  exact sub_eq_zero.mp h0

end Summands

section Counting

theorem card_mul_card_fixed_lt {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (t : M ≃ₗ[ZMod 2] M) (ht : t ∈ A)
    (hA : Nat.card A < 2 ^ Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - 1))) :
    Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m} < Nat.card M := by
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  set D : M →ₗ[ZMod 2] M := t.toLinearMap - 1 with hD
  have h1 : Nat.card M = 2 ^ Module.finrank (ZMod 2) M := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (LinearMap.ker D) = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker D) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h3 := LinearMap.finrank_range_add_finrank_ker D
  have hC : Nat.card {m : M // ∀ a ∈ A, a m = m} ≤ Nat.card (LinearMap.ker D) := by
    refine Nat.card_le_card_of_injective (fun m => ⟨m.1, ?_⟩) ?_
    · show t m.1 - m.1 = 0
      rw [m.2 t ht, sub_self]
    · intro a b h
      exact Subtype.ext (congrArg (fun x => x.1) h)
  have hpos : 0 < Nat.card (LinearMap.ker D) := Nat.card_pos
  calc Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m}
      ≤ Nat.card A * Nat.card (LinearMap.ker D) := Nat.mul_le_mul_left _ hC
    _ < 2 ^ Module.finrank (ZMod 2) (LinearMap.range D) * Nat.card (LinearMap.ker D) :=
        Nat.mul_lt_mul_of_pos_right hA hpos
    _ = Nat.card M := by rw [h1, h2, ← pow_add, h3]

end Counting

section NormAut

variable {G Ge : Type} [Group G] [Group Ge] (π : G →* Ge)

@[expose] noncomputable def inducedAut (hπ : Function.Injective π) (a : Ge)
    (h₁ : ∀ x, ∃ y, a * π x * a⁻¹ = π y) (h₂ : ∀ x, ∃ y, a⁻¹ * π x * a = π y) : MulAut G where
  toFun x := Classical.choose (h₁ x)
  invFun x := Classical.choose (h₂ x)
  left_inv x := hπ (by
    have e1 := Classical.choose_spec (h₁ x)
    have e2 := Classical.choose_spec (h₂ (Classical.choose (h₁ x)))
    rw [← e2, ← e1]
    group)
  right_inv x := hπ (by
    have e1 := Classical.choose_spec (h₁ (Classical.choose (h₂ x)))
    have e2 := Classical.choose_spec (h₂ x)
    rw [← e1, ← e2]
    group)
  map_mul' x y := hπ (by
    have e := Classical.choose_spec (h₁ (x * y))
    have ex := Classical.choose_spec (h₁ x)
    have ey := Classical.choose_spec (h₁ y)
    show π (Classical.choose (h₁ (x * y))) =
      π (Classical.choose (h₁ x) * Classical.choose (h₁ y))
    rw [map_mul π (Classical.choose (h₁ x)) (Classical.choose (h₁ y)), ← ex, ← ey, ← e, map_mul]
    group)

theorem π_inducedAut (hπ : Function.Injective π) (a : Ge)
    (h₁ : ∀ x, ∃ y, a * π x * a⁻¹ = π y) (h₂ : ∀ x, ∃ y, a⁻¹ * π x * a = π y) (x : G) :
    π (inducedAut π hπ a h₁ h₂ x) = a * π x * a⁻¹ :=
  (Classical.choose_spec (h₁ x)).symm

variable (hπ : Function.Injective π) (A : Subgroup Ge)
  (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)

@[expose] noncomputable def normAut : A →* MulAut G :=
  MonoidHom.mk' (fun a => inducedAut π hπ a.1 (hnorm a.1 a.2)
      (fun x => by simpa using hnorm a.1⁻¹ (inv_mem a.2) x))
    (fun a b => MulEquiv.ext fun x => hπ (by
      rw [MulAut.mul_apply, π_inducedAut, π_inducedAut, π_inducedAut]
      show (a.1 * b.1) * π x * (a.1 * b.1)⁻¹ = a.1 * (b.1 * π x * b.1⁻¹) * a.1⁻¹
      group))

theorem π_normAut (a : A) (x : G) : π (normAut π hπ A hnorm a x) = a.1 * π x * a.1⁻¹ :=
  π_inducedAut π hπ _ _ _ x

end NormAut

section Setting

variable {K : Type} [Field K] {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

structure Offender (π : antiSp K →* (M ≃ₗ[ZMod 2] M)) (A : Subgroup (M ≃ₗ[ZMod 2] M)) : Prop where
  inj : Function.Injective π
  norm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y
  sq : ∀ a ∈ A, a * a = 1
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  summands : SimpleSummandsStable π A

variable {π : antiSp K →* (M ≃ₗ[ZMod 2] M)} {A : Subgroup (M ≃ₗ[ZMod 2] M)}

theorem Offender.eq_one_of_commute (H : Offender π A) (g : antiSp K) (a : M ≃ₗ[ZMod 2] M)
    (ha : a ∈ A) (hcc : (π g * a) * (π g * a) = 1)
    (hcomm : ∀ x, (π g * a) * π x = π x * (π g * a)) : π g * a = 1 := by
  obtain ⟨ι, U, -, htop, hU⟩ := H.summands
  refine eq_one_of_commute_simple_summands π U htop (fun i => (hU i).1)
    (fun i g' x hx => (hU i).2.2.1 g' x hx) (fun i W hW hWinv => (hU i).2.2.2.1 W hW hWinv)
    (π g * a) hcc hcomm (fun i u hu => ?_)
  show π g (a u) ∈ U i
  exact (hU i).2.2.1 g _ ((hU i).2.2.2.2 a ha u hu)

theorem Offender.normAut_eq_one (H : Offender π A) (a : A)
    (h : normAut π H.inj A H.norm a = 1) : a = 1 := by
  have hcomm : ∀ x, (π 1 * a.1) * π x = π x * (π 1 * a.1) := fun x => by
    have h1 := π_normAut π H.inj A H.norm a x
    rw [h] at h1
    simp only [map_one, one_mul]
    have h2 : a.1 * π x * a.1⁻¹ = π x := by rw [← h1]; rfl
    calc a.1 * π x = (a.1 * π x * a.1⁻¹) * a.1 := by group
      _ = π x * a.1 := by rw [h2]
  have hcc : (π 1 * a.1) * (π 1 * a.1) = 1 := by
    simpa using H.sq a.1 a.2
  have h1 := H.eq_one_of_commute 1 a.1 a.2 hcc hcomm
  have h2 : a.1 = 1 := by simpa using h1
  exact Subtype.ext h2

end Setting

section Inner

variable {K : Type} [Field K] [CharP K 2] {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
  {π : antiSp K →* (M ≃ₗ[ZMod 2] M)} {A : Subgroup (M ≃ₗ[ZMod 2] M)}

theorem Offender.normAut_mem_inner_iff (H : Offender π A) (a : A) :
    normAut π H.inj A H.norm a ∈ inner (antiSp K) ↔ ∃ g, π g = a.1 := by
  constructor
  · rintro ⟨g, hg⟩
    have hconj : ∀ x, a.1 * π x * a.1⁻¹ = π g * π x * (π g)⁻¹ := fun x => by
      rw [← π_normAut π H.inj A H.norm a x, ← hg]
      simp [MulAut.conj_apply]
    have hgg : g * g = 1 := by
      apply conj_injective (K := K)
      have h1 : normAut π H.inj A H.norm (a * a) = 1 := by
        have : a * a = 1 := Subtype.ext (H.sq a.1 a.2)
        rw [this, map_one]
      rw [map_mul] at h1
      rw [map_mul, hg, h1, map_one]
    have hpp : π g * π g = 1 := by rw [← map_mul, hgg, map_one]
    have hpinv : (π g)⁻¹ = π g := inv_eq_of_mul_eq_one_right hpp
    have hcomm : ∀ x, (π g * a.1) * π x = π x * (π g * a.1) := fun x => by
      calc (π g * a.1) * π x = π g * (a.1 * π x * a.1⁻¹) * a.1 := by group
        _ = π g * (π g * π x * (π g)⁻¹) * a.1 := by rw [hconj x]
        _ = (π g * π g) * π x * (π g * a.1) := by rw [hpinv]; group
        _ = π x * (π g * a.1) := by rw [hpp, one_mul]
    have h3 : π g * a.1 * π g = a.1 := by
      have := hcomm g
      rw [this]
      calc π g * (π g * a.1) = (π g * π g) * a.1 := by group
        _ = a.1 := by rw [hpp, one_mul]
    have hcc : (π g * a.1) * (π g * a.1) = 1 := by
      calc (π g * a.1) * (π g * a.1) = (π g * a.1 * π g) * a.1 := by group
        _ = a.1 * a.1 := by rw [h3]
        _ = 1 := H.sq a.1 a.2
    have h4 := H.eq_one_of_commute g a.1 a.2 hcc hcomm
    refine ⟨g, ?_⟩
    have h5 : π g = a.1⁻¹ := eq_inv_of_mul_eq_one_left h4
    rw [h5]
    exact inv_eq_of_mul_eq_one_right (H.sq a.1 a.2)
  · rintro ⟨g, hg⟩
    refine ⟨g, MulEquiv.ext fun x => H.inj ?_⟩
    rw [π_normAut, ← hg]
    simp [MulAut.conj_apply]

variable (π A) in
@[expose] noncomputable def outerHom (hπ : Function.Injective π)
    (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y) : A →* Outer (antiSp K) :=
  (QuotientGroup.mk' (inner (antiSp K))).comp (normAut π hπ A hnorm)

omit [CharP K 2] in
theorem mem_ker_outerHom (H : Offender π A) (a : A) :
    a ∈ (outerHom π A H.inj H.norm).ker ↔ normAut π H.inj A H.norm a ∈ inner (antiSp K) := by
  rw [MonoidHom.mem_ker]
  exact QuotientGroup.eq_one_iff _

end Inner

section Card

variable {K : Type} [Field K] [CharP K 2] {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
  {π : antiSp K →* (M ≃ₗ[ZMod 2] M)} {A : Subgroup (M ≃ₗ[ZMod 2] M)}

theorem Offender.card_eq (H : Offender π A) :
    Nat.card A = Nat.card (A.comap π) * Nat.card (outerHom π A H.inj H.norm).range := by
  set Ψ := outerHom π A H.inj H.norm with hΨ
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Ψ.ker
  have h2 : Nat.card (A ⧸ Ψ.ker) = Nat.card Ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange Ψ).toEquiv
  have hmem : ∀ x : A.comap π, (⟨π x.1, x.2⟩ : A) ∈ Ψ.ker := fun x =>
    (mem_ker_outerHom H _).mpr ((H.normAut_mem_inner_iff _).mpr ⟨x.1, rfl⟩)
  have h3 : Nat.card Ψ.ker = Nat.card (A.comap π) := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun x : A.comap π => (⟨⟨π x.1, x.2⟩, hmem x⟩ : Ψ.ker)) ⟨?_, ?_⟩)).symm
    · intro x y hxy
      exact Subtype.ext (H.inj (congrArg (fun z : Ψ.ker => z.1.1) hxy))
    · rintro ⟨a, ha⟩
      obtain ⟨g, hg⟩ := (H.normAut_mem_inner_iff a).mp ((mem_ker_outerHom H a).mp ha)
      refine ⟨⟨g, by show π g ∈ A; rw [hg]; exact a.2⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hg)
  rw [h1, h2, h3, mul_comm]

omit [CharP K 2] in
theorem Offender.card_range_le_two (H : Offender π A) [Finite (Outer (antiSp K))]
    (hcyc : IsCyclic (Outer (antiSp K))) :
    Nat.card (outerHom π A H.inj H.norm).range ≤ 2 := by
  classical
  have : Fintype (Outer (antiSp K)) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := Outer (antiSp K)) (n := 2) (by norm_num)
  have hsq : ∀ y : (outerHom π A H.inj H.norm).range, y.1 ^ 2 = 1 := by
    rintro ⟨_, a, rfl⟩
    show (outerHom π A H.inj H.norm a) ^ 2 = 1
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one, _root_.sq]
      exact H.sq a.1 a.2)
    rw [this, map_one]
  have hinj : Function.Injective (fun y : (outerHom π A H.inj H.norm).range =>
      (⟨y.1, hsq y⟩ : {z : Outer (antiSp K) // z ^ 2 = 1})) := fun y y' h =>
    Subtype.ext (congrArg (fun z : {z : Outer (antiSp K) // z ^ 2 = 1} => z.1) h)
  calc Nat.card (outerHom π A H.inj H.norm).range
      ≤ Nat.card {z : Outer (antiSp K) // z ^ 2 = 1} := Nat.card_le_card_of_injective _ hinj
    _ = (Finset.univ.filter fun z : Outer (antiSp K) => z ^ 2 = 1).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 2 := hle

end Card

section Reduction

variable {K : Type} [Field K] [CharP K 2] [Fintype K] {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M] {π : antiSp K →* (M ≃ₗ[ZMod 2] M)} {A : Subgroup (M ≃ₗ[ZMod 2] M)}

@[expose] noncomputable def dispRank (t : M ≃ₗ[ZMod 2] M) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - 1))

omit [CharP K 2] [Fintype K] in
theorem rk0_one : rk0 (1 : antiSp K) = 0 := by
  simp [rk0]

omit [Fintype K] in
theorem offender_reduction {f : ℕ} (hf : 2 ≤ f) [Finite M] (H : Offender π A) (hA1 : A ≠ ⊥)
    [Finite (Outer (antiSp K))] (hcyc : IsCyclic (Outer (antiSp K)))
    (h25 : ∀ z : antiSp K, z * z = 1 → z ≠ 1 → 3 * f ≤ dispRank (π z) ∧
      (rk0 z = 2 → rk1 z = 2 → 4 * f ≤ dispRank (π z)))
    (hmax : ∀ E : Subgroup (antiSp K), (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 2 ^ (3 * f) ∧
      (Nat.card E = 2 ^ (3 * f) → ∃ z ∈ E, rk0 z = 2 ∧ rk1 z = 2))
    (h24 : ∀ θ : MulAut (antiSp K), θ * θ = 1 → θ ∉ inner (antiSp K) →
      ∀ E : Subgroup (antiSp K), E ≤ fixedSubgroup θ → (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 2 ^ (if Even f then 3 * (f / 2) else 2 * f))
    (h26 : ∀ a : A, normAut π H.inj A H.norm a ∉ inner (antiSp K) → 4 ≤ dispRank a.1) :
    Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m} < Nat.card M := by
  classical
  have : Finite (M ≃ₗ[ZMod 2] M) :=
    Finite.of_injective (fun e : M ≃ₗ[ZMod 2] M => (e : M → M)) DFunLike.coe_injective
  have : Finite A := inferInstance
  set Ψ := outerHom π A H.inj H.norm with hΨ
  have hcardA := H.card_eq
  have hq := H.card_range_le_two hcyc
  set Ê : Subgroup (antiSp K) := A.comap π with hÊ
  have hÊsq : ∀ x ∈ Ê, x * x = 1 := fun x hx => by
    apply H.inj
    rw [map_mul, map_one]
    exact H.sq _ hx
  have hÊA : ∀ x ∈ Ê, π x ∈ A := fun x hx => hx
  have hpowle : ∀ {m n : ℕ}, m ≤ n → 2 ^ m ≤ 2 ^ n := fun h => Nat.pow_le_pow_right (by norm_num) h
  by_cases hΨ1 : ∀ a : A, Ψ a = 1
  ·
    have hrange : Ψ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      exact hΨ1 a
    have hAÊ : Nat.card A = Nat.card Ê := by
      rw [hcardA, hrange, Subgroup.card_bot, mul_one]
    have hÊne : Ê ≠ ⊥ := fun h => hA1 (Subgroup.card_eq_one.mp (by rw [hAÊ, h, Subgroup.card_bot]))
    obtain ⟨⟨z, hzÊ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hÊne
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    obtain ⟨hmax1, hmax2⟩ := hmax Ê hÊsq
    rcases hmax1.lt_or_eq with hlt | heq
    · refine card_mul_card_fixed_lt A (π z) (hÊA z hzÊ) ?_
      calc Nat.card A = Nat.card Ê := hAÊ
        _ < 2 ^ (3 * f) := hlt
        _ ≤ 2 ^ dispRank (π z) := hpowle (h25 z (hÊsq z hzÊ) hz1').1
    · obtain ⟨z', hz'Ê, hr0, hr1⟩ := hmax2 heq
      have hz'1 : z' ≠ 1 := fun h => by
        rw [h, rk0_one] at hr0
        omega
      refine card_mul_card_fixed_lt A (π z') (hÊA z' hz'Ê) ?_
      calc Nat.card A = Nat.card Ê := hAÊ
        _ = 2 ^ (3 * f) := heq
        _ < 2 ^ (4 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        _ ≤ 2 ^ dispRank (π z') := hpowle ((h25 z' (hÊsq z' hz'Ê) hz'1).2 hr0 hr1)
  · push Not at hΨ1
    obtain ⟨a₀, ha₀⟩ := hΨ1
    have hout : normAut π H.inj A H.norm a₀ ∉ inner (antiSp K) := fun h =>
      ha₀ (MonoidHom.mem_ker.mp ((mem_ker_outerHom H a₀).mpr h))
    have hθθ : normAut π H.inj A H.norm a₀ * normAut π H.inj A H.norm a₀ = 1 := by
      rw [← map_mul]
      have : a₀ * a₀ = 1 := Subtype.ext (H.sq a₀.1 a₀.2)
      rw [this, map_one]
    have hcard2 : Nat.card A ≤ 2 * Nat.card Ê := by
      calc Nat.card A = Nat.card Ê * Nat.card Ψ.range := hcardA
        _ ≤ Nat.card Ê * 2 := Nat.mul_le_mul_left _ hq
        _ = 2 * Nat.card Ê := mul_comm _ _
    by_cases hÊbot : Ê = ⊥
    · have h1 : Nat.card Ê = 1 := by rw [hÊbot, Subgroup.card_bot]
      refine card_mul_card_fixed_lt A a₀.1 a₀.2 ?_
      have h4 := h26 a₀ hout
      calc Nat.card A ≤ 2 * Nat.card Ê := hcard2
        _ = 2 := by rw [h1]
        _ < 2 ^ 4 := by norm_num
        _ ≤ 2 ^ dispRank a₀.1 := hpowle h4
    · obtain ⟨⟨z, hzÊ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hÊbot
      have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
      have hfix : Ê ≤ fixedSubgroup (normAut π H.inj A H.norm a₀) := by
        intro x hx
        rw [mem_fixedSubgroup]
        apply H.inj
        rw [π_normAut]
        have := H.comm a₀.1 a₀.2 (π x) (hÊA x hx)
        calc a₀.1 * π x * a₀.1⁻¹ = (π x * a₀.1) * a₀.1⁻¹ := by rw [this]
          _ = π x := by group
      have h24' := h24 _ hθθ hout Ê hfix hÊsq
      have hbd : (if Even f then 3 * (f / 2) else 2 * f) + 1 < 3 * f := by
        split_ifs with hev
        · omega
        · omega
      refine card_mul_card_fixed_lt A (π z) (hÊA z hzÊ) ?_
      calc Nat.card A ≤ 2 * Nat.card Ê := hcard2
        _ ≤ 2 * 2 ^ (if Even f then 3 * (f / 2) else 2 * f) := Nat.mul_le_mul_left _ h24'
        _ = 2 ^ ((if Even f then 3 * (f / 2) else 2 * f) + 1) := by rw [pow_succ, mul_comm]
        _ < 2 ^ (3 * f) := Nat.pow_lt_pow_right (by norm_num) hbd
        _ ≤ 2 ^ dispRank (π z) := hpowle (h25 z (hÊsq z hzÊ) hz1').1

end Reduction

section Core

theorem diagram_normalizer_excludes_offenders_antiSp
    {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] [Finite M] (π : antiSp K →* (M ≃ₗ[ZMod 2] M))
    (hπ : Function.Injective π) (b : M ≃ₗ[ZMod 2] M) (h : antiSp K) {j : ℕ} (hjodd : Odd j)
    (hj2 : j < 2 * f) (hb : ∀ x, b * π x * b⁻¹ = π (h * (minorAut K ^ j) x * h⁻¹))
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥) (hsum : SimpleSummandsStable π A) :
    Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m} < Nat.card M := by
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  let _ : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have := hAe
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    rwa [_root_.sq] at this
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb' => by
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨a, ha⟩ ⟨b, hb'⟩)
  have H : Offender π A := ⟨hπ, hnorm, hsq, hcomm, hsum⟩
  obtain ⟨-, hcyc, hcard, hN24⟩ :=
    even_symplectic_four_outer_involution_rank_and_perfect_residual hf hK
  have : Finite (Outer (antiSp K)) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  let π' : Representation (ZMod 2) (antiSp K) M :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := M)).comp π
  have hπ'inj : Function.Injective π' := fun g g' hg =>
    hπ (LinearEquiv.toLinearMap_injective hg)
  have hπ'nt : ∃ g, π' g ≠ 1 := ⟨invX K, fun h1 => invX_ne_one (hπ'inj (h1.trans (map_one π').symm))⟩
  have hb' : ∀ (g : antiSp K) (w : M),
      b (π' g (b.symm w)) = π' (h * (minorAut K ^ j) g * h⁻¹) w := fun g w => by
    have := congrArg (fun e : M ≃ₗ[ZMod 2] M => e w) (hb g)
    exact this
  have h25 : ∀ z : antiSp K, z * z = 1 → z ≠ 1 → 3 * f ≤ dispRank (π z) ∧
      (rk0 z = 2 → rk1 z = 2 → 4 * f ≤ dispRank (π z)) := fun z hz hz1 =>
    binary_diagram_stable_modules_have_large_inner_involution_ranks hf hKf π' hπ'nt b h
      (Nat.odd_iff.mp hjodd) hj2 hb' hz hz1
  have hmax := (involution_rank_pairs_and_maximal_elementary_witness hK).2.2
  have h24 : ∀ θ : MulAut (antiSp K), θ * θ = 1 → θ ∉ inner (antiSp K) →
      ∀ E : Subgroup (antiSp K), E ≤ fixedSubgroup θ → (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 2 ^ (if Even f then 3 * (f / 2) else 2 * f) :=
    fun θ hθ hθinn E hE hEsq => (hN24 θ hθ hθinn).2.1 E hE hEsq
  have h26 : ∀ a : A, normAut π H.inj A H.norm a ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K) → 4 ≤ dispRank a.1 := by
    intro a ha
    have ha1 : a.1 ≠ 1 := fun h1 => ha (by
      have : a = 1 := Subtype.ext h1
      rw [this, map_one]
      exact one_mem _)
    have hord : orderOf a.1 = 2 :=
      orderOf_eq_prime (by rw [_root_.sq]; exact hsq a.1 a.2) ha1
    exact outer_involutions_have_binary_displacement_at_least_four hf hKf π' hπ'inj a.1 hord
      (normAut π H.inj A H.norm a) ha (fun g w => by
        have := π_normAut π H.inj A H.norm a g
        have h2 := congrArg (fun e : M ≃ₗ[ZMod 2] M => e w) this
        exact h2.symm)
  exact offender_reduction hf H hA1 hcyc h25 hmax h24 h26

end Core

section Transport

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem simpleSummandsStable_comp {P P' M : Type} [Group P] [Group P'] [AddCommGroup M]
    [Module (ZMod 2) M] (e : P' ≃* P) (π : P →* (M ≃ₗ[ZMod 2] M))
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (h : SimpleSummandsStable π A) :
    SimpleSummandsStable (π.comp e.toMonoidHom) A := by
  obtain ⟨ι, U, hind, htop, hU⟩ := h
  refine ⟨ι, U, hind, htop, fun i => ⟨(hU i).1, ?_, ?_, ?_, (hU i).2.2.2.2⟩⟩
  · obtain ⟨x, hx, g, hg⟩ := (hU i).2.1
    exact ⟨x, hx, e.symm g, by simpa using hg⟩
  · intro g x hx
    exact (hU i).2.2.1 (e g) x hx
  · intro W hW hWinv
    refine (hU i).2.2.2.1 W hW fun g x hx => ?_
    have := hWinv (e.symm g) x hx
    simpa using this

theorem diagram_normalizer_excludes_offenders
    : DiagramNormalizerExcludesOffenders := by
  intro f K _ _ _ hf hK M _ _ _ π hπ b g₀ j hjodd hj1 hj2 hb A hnorm hAe hA1 hsum
  let κ := antiProjEquiv K
  let πG : antiSp K →* (M ≃ₗ[ZMod 2] M) := π.comp κ.toMonoidHom
  have hπG : Function.Injective πG := hπ.comp κ.injective
  let p : StatedProj (StatedSp 2 K) := proj 2 K g₀
  let h : antiSp K := κ.symm p
  have hγ : ∀ (n : ℕ) (x : antiSp K), (exceptionalAut K ^ n) (κ x) = κ ((minorAut K ^ n) x) := by
    intro n x
    rw [← autCongr_minorAut, ← map_pow]
    show antiProjEquiv K ((minorAut K ^ n) ((antiProjEquiv K).symm (antiProjEquiv K x))) = _
    rw [MulEquiv.symm_apply_apply]
  have hb' : ∀ x, b * πG x * b⁻¹ = πG (h * (minorAut K ^ j) x * h⁻¹) := by
    intro x
    have h1 := hb (κ x)
    rw [MulAut.mul_apply, spInner_eq_conj, MulAut.conj_apply, hγ] at h1
    have e : p * κ ((minorAut K ^ j) x) * p⁻¹ = κ (h * (minorAut K ^ j) x * h⁻¹) := by
      simp [h, map_mul, map_inv]
    rw [e] at h1
    exact h1
  have hnorm' : ∀ a ∈ A, ∀ x, ∃ y, a * πG x * a⁻¹ = πG y := by
    intro a ha x
    obtain ⟨y, hy⟩ := hnorm a ha (κ x)
    exact ⟨κ.symm y, by simpa [πG] using hy⟩
  exact diagram_normalizer_excludes_offenders_antiSp hf hK πG hπG b h hjodd hj2 hb' A hnorm' hAe hA1
    (simpleSummandsStable_comp κ π A hsum)

end Transport

end CFSG.QuasithinUnique.Setup.X7b

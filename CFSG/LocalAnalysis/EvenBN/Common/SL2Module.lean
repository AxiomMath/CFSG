module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulSection
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup Matrix
open scoped commutatorElement

variable {k : Type*} [Field k] [Finite k]

omit [Field k] in
theorem exists_finset_card_four (h4 : 4 ≤ Nat.card k) : ∃ s : Finset k, s.card = 4 := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨s, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset k)) (n := 4)
    (by rw [Finset.card_univ, Fintype.card_eq_nat_card]; omega)
  exact ⟨s, hs.2⟩

omit [Finite k] in
theorem sl2_isSimpleGroup_of_charTwo [CharP k 2] (h4 : 4 ≤ Nat.card k) :
    IsSimpleGroup (SpecialLinearGroup (Fin 2) k) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hc : Subgroup.center (SpecialLinearGroup (Fin 2) k) = ⊥ := by
    refine eq_bot_iff.mpr fun A hA => ?_
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
    have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
    subst hr1
    rw [Subgroup.mem_bot]
    ext i j
    have := congrFun (congrFun hrA i) j
    simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have e : SpecialLinearGroup (Fin 2) k ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact e.isSimpleGroup

theorem eq_one_of_card_lt [CharP k 2] {X V : Type*} [Group X] [Group V] [Finite X] [Finite V]
    {m d : ℕ} (e : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m)
    (hm3 : m ≠ 3) (ρ : X →* MulAut V) (hV : Nat.card V = 2 ^ d) (hd : d < 2 * m) : ρ = 1 := by
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have := sl2_isSimpleGroup_of_charTwo h4
  have hX : IsSimpleGroup X := e.isSimpleGroup
  rcases hX.eq_bot_or_eq_top_of_normal ρ.ker with hb | ht
  · exfalso
    have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hb
    have hJ : 2 ^ m * ((2 ^ m) ^ 2 - 1) ∣ Nat.card X := by
      rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk]
    have hZ : 2 ≤ m → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ 2 ^ (2 * m) - 1 ∧
        ∀ j : ℕ, 0 < j → j < 2 * m → ¬ ℓ ∣ 2 ^ j - 1 := fun _ =>
      CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * m) (by omega) (by omega)
    have := CFSG.SL2MinimalFaithful.two_mul_le_of_injective Nat.prime_two (by omega) hJ hZ ρ
      hinj hV
    omega
  · ext x v
    have hx : x ∈ ρ.ker := ht ▸ mem_top x
    rw [MonoidHom.mem_ker] at hx
    rw [hx, MonoidHom.one_apply]

variable {G : Type*} [Group G] [Finite G]

theorem le_centralizer_of_card_lt [CharP k 2] {X V : Subgroup G} {m d : ℕ}
    (e : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (hXV : X ≤ normalizer (V : Set G)) (hV : Nat.card V = 2 ^ d) (hd : d < 2 * m) :
    X ≤ centralizer (V : Set G) := by
  have h1 := eq_one_of_card_lt e hk hm hm3 (CFSG.SL2MinimalFaithful.conjAction hXV) hV hd
  intro x hx
  rw [mem_centralizer_iff]
  intro v hv
  have h2 := congrArg (fun φ : X →* MulAut V => ((φ ⟨x, hx⟩ ⟨v, hv⟩ : V) : G)) h1
  simp only [CFSG.SL2MinimalFaithful.conjAction_apply, MonoidHom.one_apply, MulAut.one_apply]
    at h2
  have h3 : x * v * x⁻¹ = v := h2
  calc v * x = x * v * x⁻¹ * x := by rw [h3]
    _ = x * v := by group

theorem commutator_mem_of_card_lt [CharP k 2] {X Y Z : Subgroup G} {m d : ℕ}
    (e : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (hZY : Z ≤ Y) (hYZ : Y ≤ normalizer (Z : Set G)) (hXY : X ≤ normalizer (Y : Set G))
    (hXZ : X ≤ normalizer (Z : Set G)) (hcard : Nat.card Y = 2 ^ d * Nat.card Z)
    (hd : d < 2 * m) {x y : G} (hx : x ∈ X) (hy : y ∈ Y) : x * y * x⁻¹ * y⁻¹ ∈ Z := by
  set Z' : Subgroup Y := Z.subgroupOf Y with hZ'
  have hZ'n : Z'.Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hYZ g.2) n).mp (Subgroup.mem_subgroupOf.mp hn))⟩
  have hZ'card : Nat.card Z' = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY).toEquiv
  set ρY := CFSG.SL2MinimalFaithful.conjAction hXY
  have hmap : ∀ j, Z'.map (ρY j : Y →* Y) = Z' := by
    intro j
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      change (j : G) * z * (j : G)⁻¹ ∈ Z
      exact (Subgroup.mem_normalizer_iff.mp (hXZ j.2) z).mp hz
    · intro z hz
      refine ⟨ρY j⁻¹ z, ?_, ?_⟩
      · change ((j⁻¹ : X) : G) * z * ((j⁻¹ : X) : G)⁻¹ ∈ Z
        exact (Subgroup.mem_normalizer_iff.mp (hXZ (X.inv_mem j.2)) z).mp hz
      · change ρY j (ρY j⁻¹ z) = z
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  set ρ := CFSG.SL2MinimalFaithful.quotientAction ρY Z' hmap
  have hVcard : Nat.card (Y ⧸ Z') = 2 ^ d := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
    rw [hZ'card, hcard] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  have h1 := eq_one_of_card_lt e hk hm hm3 ρ hVcard hd
  have h2 : ρ ⟨x, hx⟩ ((⟨y, hy⟩ : Y) : Y ⧸ Z') = ((⟨y, hy⟩ : Y) : Y ⧸ Z') := by
    rw [h1, MonoidHom.one_apply, MulAut.one_apply]
  rw [CFSG.SL2MinimalFaithful.quotientAction_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    at h2
  change (ρY ⟨x, hx⟩ ⟨y, hy⟩ : G)⁻¹ * y ∈ Z at h2
  rw [CFSG.SL2MinimalFaithful.conjAction_apply] at h2
  have h3 := (CFSG.SL2MinimalFaithful.inv_mul_mem_iff hYZ hy).1 h2
  exact h3

theorem eq_bot_or_eq_of_card_le [CharP k 2] {X A V₀ : Subgroup G} {m a : ℕ}
    (e : X ≃* SpecialLinearGroup (Fin 2) k) (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAcard : Nat.card A = 2 ^ a) (ha : a ≤ 2 * m)
    (hXA : X ≤ normalizer (A : Set G)) (hXV : X ≤ normalizer (V₀ : Set G)) (hVA : V₀ ≤ A)
    (hnc : ¬ X ≤ centralizer (A : Set G)) : V₀ = ⊥ ∨ V₀ = A := by
  by_contra hne
  push Not at hne
  obtain ⟨hV1, hVA'⟩ := hne
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨b, hb, hVb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hAcard ▸ Subgroup.card_dvd_of_le hVA)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hV1 ((Subgroup.card_eq_one).1 (by rw [hVb, pow_zero]))
  have hba : b ≠ a := by
    rintro rfl
    exact hVA' (Subgroup.eq_of_le_of_card_ge hVA (by rw [hVb, hAcard]))
  have hba' : b < a := lt_of_le_of_ne hb hba
  have hXV₀ : X ≤ centralizer (V₀ : Set G) :=
    le_centralizer_of_card_lt e hk hm hm3 hXV hVb (by omega)
  have hVnA : A ≤ normalizer (V₀ : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      rw [show x * v * x⁻¹ = v by rw [hAc x hx v (hVA hv), mul_inv_cancel_right]]
      exact hv
    · intro hv
      have hv' : x * v * x⁻¹ ∈ A := hVA hv
      have hvA : v ∈ A := by
        have := mul_mem (mul_mem (inv_mem hx) hv') hx
        rwa [show x⁻¹ * (x * v * x⁻¹) * x = v by group] at this
      rw [show v = x * v * x⁻¹ by rw [hAc x hx v hvA, mul_inv_cancel_right]]
      exact hv
  have hcardA : Nat.card A = 2 ^ (a - b) * Nat.card V₀ := by
    rw [hAcard, hVb, ← pow_add, Nat.sub_add_cancel hb]
  have hXq : ∀ x ∈ X, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ V₀ := fun x hx y hy =>
    commutator_mem_of_card_lt e hk hm hm3 hVA hVnA hXA hXV hcardA (by omega) hx hy
  have hXA' : ⁅⁅A, X⁆, X⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro c hc x hx
    have hcV : c ∈ V₀ := by
      have : ⁅A, X⁆ ≤ V₀ := by
        rw [commutator_le]
        intro y hy x' hx'
        have := hXq x' hx' y⁻¹ (inv_mem hy)
        have e1 : ⁅y, x'⁆ = x' * y⁻¹ * x'⁻¹ * y⁻¹⁻¹ := by
          rw [commutatorElement_def]
          have := hAc y hy (x' * y⁻¹ * x'⁻¹) (by
            have := (mem_normalizer_iff.1 (hXA hx') y⁻¹).1 (inv_mem hy)
            exact this)
          calc y * x' * y⁻¹ * x'⁻¹ = y * (x' * y⁻¹ * x'⁻¹) := by group
            _ = (x' * y⁻¹ * x'⁻¹) * y := this
            _ = x' * y⁻¹ * x'⁻¹ * y⁻¹⁻¹ := by rw [inv_inv]
        rw [e1]
        exact this
      exact this hc
    have := mem_centralizer_iff.1 (hXV₀ hx) c hcV
    rw [commutatorElement_def, this, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hXA'' : ⁅⁅X, A⁆, X⁆ = ⊥ := by
    rw [commutator_comm X A]
    exact hXA'
  have hcomm := commutator_commutator_eq_bot_of_rotate hXA'' hXA'
  have hperf : ⁅X, X⁆ = X := by
    have := LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h4)
    have : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
      e.symm.surjective
    exact Subgroup.isPerfect_iff.1 this
  rw [hperf] at hcomm
  exact hnc ((commutator_eq_bot_iff_le_centralizer).1 hcomm)

end CFSG.LocalAnalysis.EvenBN.Common

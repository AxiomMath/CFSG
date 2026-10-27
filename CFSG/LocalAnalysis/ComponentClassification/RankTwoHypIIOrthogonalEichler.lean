module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.ComponentClassification.RankTwoHypIIOrthogonal

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_mul_comm {x : V ≃ₗ[K] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {u a : V} (hu : u ∈ fixSpace x) (ha : a ∈ fixSpace x) :
    eichler Q u a * x = x * eichler Q u a := by
  have h := eichler_conj hxO u a
  rw [mem_fixSpace.mp hu, mem_fixSpace.mp ha] at h
  calc eichler Q u a * x = (x * eichler Q u a * x⁻¹) * x := by rw [h]
    _ = x * eichler Q u a := by group

variable [CharP K 2]

theorem le_commSpace_of_eichler [Finite K] [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) {x : V ≃ₗ[K] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxx : x * x = 1) {a : V}
    (ha : a ∈ commSpace x) (hQa : Q a ≠ 0) {W : Submodule K V} (hWx : W ≤ fixSpace x)
    (hW : ∀ w₁ ∈ W, ∀ w₂ ∈ W, polar Q w₁ w₂ = 0)
    (hinv : ∀ u ∈ fixSpace x, Q u = 0 → ∀ w ∈ W, eichler Q u a w ∈ W) :
    W ≤ commSpace x := by
  intro w hw
  by_contra hwc
  have hperp := fixSpace_eq_orthogonal_commSpace hQ hxO hxx
  have hcomm : commSpace x = LinearMap.BilinForm.orthogonal Q.polarBilin (fixSpace x) := by
    rw [hperp, LinearMap.BilinForm.orthogonal_orthogonal hQ (isSymm_polarBilin Q).isRefl]
  rw [hcomm, LinearMap.BilinForm.mem_orthogonal_iff] at hwc
  push Not at hwc
  obtain ⟨v, hv, hvw⟩ := hwc
  have hvw' : polar Q w v ≠ 0 := by
    rw [polar_comm]
    exact hvw
  have horth : ∀ y ∈ fixSpace x, polar Q y a = 0 := by
    intro y hy
    rw [hperp, LinearMap.BilinForm.mem_orthogonal_iff] at hy
    have h1 : Q.polarBilin a y = 0 := hy a ha
    rw [polarBilin_apply_apply, polar_comm] at h1
    exact h1
  have haF : a ∈ fixSpace x := commSpace_le_fixSpace hxx ha
  obtain ⟨c, hc⟩ := isSquare_of_charTwo' (Q v / Q a)
  set u := v + c • a with hudef
  have hQu : Q u = 0 := by
    rw [hudef, map_add_eq, QuadraticMap.map_smul, polar_smul_right, horth v hv, smul_zero,
      add_zero, smul_eq_mul, ← hc, div_mul_cancel₀ _ hQa, CharTwo.add_self_eq_zero]
  have huF : u ∈ fixSpace x := (fixSpace x).add_mem hv ((fixSpace x).smul_mem c haF)
  have hua : polar Q u a = 0 := horth u huF
  have hwu : polar Q w u = polar Q w v := by
    rw [hudef, polar_add_right, polar_smul_right, horth w (hWx hw), smul_zero, add_zero]
  have key : polar Q w (eichler Q u a w) = -(Q a * (polar Q w u * polar Q w u)) := by
    rw [eichler_apply hQu hua, polar_sub_right, polar_add_right, polar_smul_right,
      polar_smul_right, CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero,
      horth w (hWx hw), smul_eq_mul, smul_eq_mul]
    ring
  have hEw := hW w hw _ (hinv u huF hQu w hw)
  rw [key, neg_eq_zero, hwu] at hEw
  exact hvw' (by
    rcases mul_eq_zero.mp hEw with h | h
    · exact absurd h hQa
    · exact mul_self_eq_zero.mp h)

theorem exists_fixed_ne_zero [Finite K] [FiniteDimensional K V] {F : Subgroup (V ≃ₗ[K] V)}
    (hF2 : IsPGroup 2 F) {U : Submodule K V} (hU : ∀ f ∈ F, ∀ u ∈ U, f u ∈ U) (hne : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ f ∈ F, f u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Module.finite_of_finite K
  let _ : MulAction F U :=
    { smul := fun f u => ⟨(f : V ≃ₗ[K] V) u, hU f f.2 u u.2⟩
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hord : addOrderOf (⟨u, hu⟩ : U) = 2 := by
    refine addOrderOf_eq_prime ?_ ?_
    · ext
      simp only [Submodule.coe_zero, two_nsmul]
      exact CFSG.RankThree.OrthogonalInvolutions.add_self_vec K u
    · intro h
      exact hu0 (congrArg Subtype.val h)
  have hcard : 2 ∣ Nat.card U := hord ▸ addOrderOf_dvd_natCard _
  have h0 : (0 : U) ∈ MulAction.fixedPoints F U := fun f =>
    Subtype.ext (map_zero (f : V ≃ₗ[K] V))
  obtain ⟨b, hb, hb0⟩ := hF2.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hcard h0
  refine ⟨b, b.2, fun h => hb0 (Subtype.ext h.symm), fun f hf => ?_⟩
  exact congrArg Subtype.val (hb ⟨f, hf⟩)

end CFSG.ComponentClassification.RankTwoHypIIOrthogonal

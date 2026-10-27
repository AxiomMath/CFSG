module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness
public import CFSG.Open.StatedDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.Open

theorem threeTwoWitness_statedProj_klein {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {H : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (d1 d2 c : Matrix.GeneralLinearGroup ι K) (h1 : d1 ∈ H) (h2 : d2 ∈ H) (hc : c ∈ H)
    (hd1 : d1 * d1 = 1) (hd2 : d2 * d2 = 1) (hcomm : d1 * d2 = d2 * d1)
    (hd1ns : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u ≠ d1) (hc3 : c ^ 3 = 1)
    (hcns : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u ≠ c) (hcd1 : c * d1 * c⁻¹ = d2)
    (hcd2 : c * d2 * c⁻¹ = d1 * d2) : ThreeTwoWitness (StatedProj H) := by
  let N : Subgroup H := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  let a : H := ⟨d1, h1⟩
  let b : H := ⟨d2, h2⟩
  let c' : H := ⟨c, hc⟩
  have hmem : ∀ g : H, π g = 1 →
      ∃ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u = (g : Matrix.GeneralLinearGroup ι K) :=
    fun g hg => (QuotientGroup.eq_one_iff g).1 hg
  have haa : a * a = 1 := Subtype.ext hd1
  have hbb : b * b = 1 := Subtype.ext hd2
  have hab : a * b = b * a := Subtype.ext hcomm
  have hc3' : c' ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hc3)
  have hca : c' * a * c'⁻¹ = b := Subtype.ext hcd1
  have hcb : c' * b * c'⁻¹ = a * b := Subtype.ext hcd2
  refine ThreeTwoWitness.of_klein (π a) (π b) (π c') ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, haa, map_one]
  · rw [← map_mul, hbb, map_one]
  · rw [← map_mul, ← map_mul, hab]
  · intro h
    obtain ⟨u, hu⟩ := hmem a h
    exact hd1ns u hu
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hc3', map_one]
    · intro h
      obtain ⟨u, hu⟩ := hmem c' h
      exact hcns u hu
  · rw [← map_inv, ← map_mul, ← map_mul, hca]
  · rw [← map_inv, ← map_mul, ← map_mul, hcb, map_mul]

theorem threeTwoWitness_statedProj_klein_mod {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {H : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (d1 d2 c : Matrix.GeneralLinearGroup ι K) (h1 : d1 ∈ H) (h2 : d2 ∈ H) (hc : c ∈ H)
    (hd1 : ∃ u : Kˣ, d1 * d1 = Matrix.GeneralLinearGroup.scalar ι u)
    (hd2 : ∃ u : Kˣ, d2 * d2 = Matrix.GeneralLinearGroup.scalar ι u)
    (hcomm : ∃ u : Kˣ, d1 * d2 = Matrix.GeneralLinearGroup.scalar ι u * (d2 * d1))
    (hd1ns : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u ≠ d1)
    (hc3 : ∃ u : Kˣ, c ^ 3 = Matrix.GeneralLinearGroup.scalar ι u)
    (hcns : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u ≠ c)
    (hcd1 : ∃ u : Kˣ, c * d1 * c⁻¹ = Matrix.GeneralLinearGroup.scalar ι u * d2)
    (hcd2 : ∃ u : Kˣ, c * d2 * c⁻¹ = Matrix.GeneralLinearGroup.scalar ι u * (d1 * d2)) :
    ThreeTwoWitness (StatedProj H) := by
  let N : Subgroup H := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  let a : H := ⟨d1, h1⟩
  let b : H := ⟨d2, h2⟩
  let c' : H := ⟨c, hc⟩
  have hmem : ∀ g : H, π g = 1 →
      ∃ u : Kˣ, Matrix.GeneralLinearGroup.scalar ι u = (g : Matrix.GeneralLinearGroup ι K) :=
    fun g hg => (QuotientGroup.eq_one_iff g).1 hg
  have hone : ∀ (g : H) (u : Kˣ), (g : Matrix.GeneralLinearGroup ι K) =
      Matrix.GeneralLinearGroup.scalar ι u → π g = 1 := fun g u hg =>
    (QuotientGroup.eq_one_iff g).2 ⟨u, hg.symm⟩
  have heq : ∀ (g g' : H) (u : Kˣ), (g : Matrix.GeneralLinearGroup ι K) =
      Matrix.GeneralLinearGroup.scalar ι u * (g' : Matrix.GeneralLinearGroup ι K) → π g = π g' := by
    intro g g' u hg
    change QuotientGroup.mk g = (QuotientGroup.mk g' : StatedProj H)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨u⁻¹, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hcen : ∀ g : Matrix.GeneralLinearGroup ι K, g * (Matrix.GeneralLinearGroup.scalar ι u)⁻¹ =
        (Matrix.GeneralLinearGroup.scalar ι u)⁻¹ * g := fun g => by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute u g,
        inv_mul_cancel_left]
    rw [hg, mul_inv_rev, hcen, mul_assoc, inv_mul_cancel, mul_one, map_inv]
  obtain ⟨u1, hu1⟩ := hd1
  obtain ⟨u2, hu2⟩ := hd2
  obtain ⟨u3, hu3⟩ := hcomm
  obtain ⟨u4, hu4⟩ := hc3
  obtain ⟨u5, hu5⟩ := hcd1
  obtain ⟨u6, hu6⟩ := hcd2
  have hπc : ∀ g g' : H, (g : Matrix.GeneralLinearGroup ι K) =
      Matrix.GeneralLinearGroup.scalar ι u3 * (g' : Matrix.GeneralLinearGroup ι K) →
        π g = π g' := fun g g' hg => heq g g' u3 hg
  refine ThreeTwoWitness.of_klein (π a) (π b) (π c') ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul]
    exact hone _ u1 hu1
  · rw [← map_mul]
    exact hone _ u2 hu2
  · rw [← map_mul, ← map_mul]
    exact heq _ _ u3 hu3
  · intro h
    obtain ⟨u, hu⟩ := hmem a h
    exact hd1ns u hu
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      exact hone _ u4 hu4
    · intro h
      obtain ⟨u, hu⟩ := hmem c' h
      exact hcns u hu
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact heq _ _ u5 hu5
  · rw [← map_inv, ← map_mul, ← map_mul, map_mul]
    exact heq _ _ u6 hu6

end CFSG.HardMathSupport.Timmesfeld.Tables.Census

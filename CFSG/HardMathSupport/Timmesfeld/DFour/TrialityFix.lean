module

public import CFSG.RankThree.SteinbergR3ECAEvenD4Centralizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open QuadraticMap Module
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveImage matrixProjectiveProjection)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus projectivePointFamily projectivePointFamilyAut
    mem_projectivePointFamilyAut_iff plusIndexEquiv)
open scoped Pointwise

variable {K : Type} [Field K] [Finite K]

theorem card_maximal_eq_two_mul_card_lines
    (hEA : projectivePointFamilyAut (coordinateQuadPlus 4 K) =
      matrixProjectiveImage (coordinateQuadPlus 4 K))
    {t : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))} (ht3 : t ^ 3 = 1)
    (htE : t ∉ matrixProjectiveImage (coordinateQuadPlus 4 K))
    (A : StatedOmega (StatedQuadPlus 4 K))
    (hfix : t (matrixProjectiveProjection (coordinateQuadPlus 4 K)
        (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) =
      matrixProjectiveProjection (coordinateQuadPlus 4 K)
        (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) :
    Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map (toLinEquiv _ K A.val).toLinearMap = M} =
      2 * Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (toLinEquiv _ K A.val).toLinearMap = L} := by
  set x := matrixProjectiveProjection (coordinateQuadPlus 4 K)
    (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A) with hx
  set F := projectivePointFamily (coordinateQuadPlus 4 K) with hFdef
  have hcomm : ∀ {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}, α x = x →
      α * MulAut.conj x = MulAut.conj x * α := by
    intro α hα
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hα]
  have ht2x : (t ^ 2) x = x := by rw [pow_two, MulAut.mul_apply, hfix, hfix]
  have hE : ∀ {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}, α • F = F →
      α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    intro α h
    rw [← hEA, mem_projectivePointFamilyAut_iff]
    exact h
  have hO : ∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      α • F = F ∨ α • F = plusCX 4 K ∨ α • F = plusCXstar 4 K (by norm_num) := by
    intro α
    have h := coordinate_plus_pointFamily_orbit_subset (K := K) (n := 4) rfl
      (MulAction.mem_orbit F α)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have ht1 : t • F ≠ F := fun h => htE (hE h)
  have ht2 : (t ^ 2) • F ≠ F := by
    intro h
    apply htE
    have h2 := hE h
    have e : t = (t ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, ht3, one_mul]
    rw [e]
    exact pow_mem h2 2
  have h12 : t • F ≠ (t ^ 2) • F := by
    intro h
    apply ht1
    rw [pow_two, mul_smul] at h
    exact (MulAction.injective t h).symm
  have hN1 := ThreeFamily.card_fixed_smul_set (hcomm hfix) F
  have hN2 := ThreeFamily.card_fixed_smul_set (hcomm ht2x) F
  have hXX : Nat.card {U // U ∈ plusCX 4 K ∧ MulAut.conj x • U = U} =
        Nat.card {U // U ∈ F ∧ MulAut.conj x • U = U} ∧
      Nat.card {U // U ∈ plusCXstar 4 K (by norm_num) ∧ MulAut.conj x • U = U} =
        Nat.card {U // U ∈ F ∧ MulAut.conj x • U = U} := by
    rcases hO t with h1 | h1 | h1
    · exact absurd h1 ht1
    · rcases hO (t ^ 2) with h2 | h2 | h2
      · exact absurd h2 ht2
      · exact absurd (h1.trans h2.symm) h12
      · rw [← h1, ← h2]
        exact ⟨hN1, hN2⟩
    · rcases hO (t ^ 2) with h2 | h2 | h2
      · exact absurd h2 ht2
      · rw [← h1, ← h2]
        exact ⟨hN2, hN1⟩
      · exact absurd (h1.trans h2.symm) h12
  obtain ⟨cP, cX, cXs⟩ := CFSG.RankThree.EvenD4Centralizer.card_fixed_coordinate_families A
  have hsum := ThreeFamily.card_fixed_maximal (K := K) (n := 4) (by norm_num)
    (toLinEquiv _ K A.val)
  rw [← hsum, ← cX, ← cXs, hXX.1, hXX.2, cP]
  ring

end CFSG.HardMathSupport.Timmesfeld.DFour

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUGL
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LULift

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatLeafProof.X10Lin (ModelIn)
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  isComponentOf_map_of_injective)

theorem inner_psl_modelIn {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hadm : StatedLieAdmissible .PSL n p f)
    (A : GL (Fin n) K) (hA : orderOf (innerDiagonalAction n K A) = 2)
    {L : Subgroup (fixedSubgroup (innerDiagonalAction n K A))} (hL : IsComponent L) :
    ModelIn p (luLinTuples n f) L := by
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · right
      have hn2 : n = 2 := by omega
      have h3' : p ^ f ≠ 3 := fun h => hadm.2.2.2.2 (by rw [hn2, h])
      rw [hK]
      exact OddInner.five_le_pow hp hp2 hf h3'
    · exact Or.inl h3
  have hne : innerDiagonalAction n K A ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hsq2 : innerDiagonalAction n K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  obtain ⟨hmk, -, c, hc⟩ :=
    CatalogueBHigherLinearInner.inner_involution_projective_data n K hn hparameter A hne hsq2
  set Z := center (SpecialLinearGroup (Fin n) K)
  set ψ := slConjugation n K A
  have hcen : GeneralLinearGroup.scalar (Fin n) c ∈ center (GL (Fin n) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hψ : ∀ x, ψ (ψ x) = x := by
    intro x
    apply SpecialLinearGroup.toGL_injective
    have e : A * (A * SpecialLinearGroup.toGL x * A⁻¹) * A⁻¹ =
        A ^ 2 * SpecialLinearGroup.toGL x * (A ^ 2)⁻¹ := by
      simp only [pow_two, _root_.mul_inv_rev, mul_assoc]
    rw [toGL_slConjugation, toGL_slConjugation, e, hc,
      ← Subgroup.mem_center_iff.mp hcen (SpecialLinearGroup.toGL x), mul_inv_cancel_right]
  have hα : ∀ s, innerDiagonalAction n K A (innerDiagonalAction n K A s) = s := fun s => by
    rw [← MulAut.mul_apply, ← pow_two, hsq2, MulAut.one_apply]
  have hK' : (QuotientGroup.mk' Z).ker ≤ center (SpecialLinearGroup (Fin n) K) := by
    rw [QuotientGroup.ker_mk']
  refine modelIn_of_centralLift (QuotientGroup.mk'_surjective Z) hK' hψ hα
    (fun x => (innerDiagonalAction_mk n K A x).symm) (fun Q hQ => ?_) hL
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ⊓
        CatalogueBGeneralLinear.specialLinearRange n K := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [toGL_slConjugation] at h1
      calc SpecialLinearGroup.toGL g * A =
          (A * SpecialLinearGroup.toGL g * A⁻¹) * A := by rw [h1]
        _ = A * SpecialLinearGroup.toGL g := by group
    · intro hy
      obtain ⟨hyC, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [toGL_slConjugation, ← Subgroup.mem_centralizer_singleton_iff.mp hyC,
        mul_inv_cancel_right]
  have hMF : Assembly.IsComponentOf (Q.map (fixedSubgroup ψ).subtype) (fixedSubgroup ψ) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le Q)).2 ?_
    have hQQ : (Q.map (fixedSubgroup ψ).subtype).subgroupOf (fixedSubgroup ψ) = Q :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) Q
    rw [hQQ]
    exact hQ
  have h1 := isComponentOf_map_of_injective hMF SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective
  rw [hmap] at h1
  have hnormal : ((Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ⊓
      CatalogueBGeneralLinear.specialLinearRange n K).subgroupOf
        (Subgroup.centralizer ({A} : Set (GL (Fin n) K)))).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (CatalogueBGeneralLinear.specialLinearRangeNormal n K).conj_mem _ hxS (g : GL (Fin n) K)
  have h2 := OddClassSelector.isComponentOf_of_normal_le h1 inf_le_left hnormal
  have h3 := (isComponentOf_iff_isComponent_subgroupOf h2.1).1 h2
  set M := (Q.map (fixedSubgroup ψ).subtype).map SpecialLinearGroup.toGL with hMdef
  let eQM : Q ≃* M.subgroupOf (Subgroup.centralizer ({A} : Set (GL (Fin n) K))) :=
    ((Q.equivMapOfInjective (fixedSubgroup ψ).subtype (subtype_injective _)).trans
      ((Q.map (fixedSubgroup ψ).subtype).equivMapOfInjective SpecialLinearGroup.toGL
        SpecialLinearGroup.toGL_injective)).trans (Subgroup.subgroupOfEquivOfLe h2.1).symm
  exact (glCentralizer_modelIn hp hp2 hf hK hn A hmk c hc h3).of_mulEquiv eQM

end CFSG.OddStandard.HigherRank.LinUnit

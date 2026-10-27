module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.CoverLift
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeCentralizer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartTwo.KFacts CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PerfectCover
open scoped commutatorElement

section Abstract

variable {Y P : Type} [Group Y] [Group P]

noncomputable abbrev descendTo (e : (Y ⧸ Subgroup.center Y) ≃* P) : MulAut Y →* MulAut P :=
  (MulAut.congr e).toMonoidHom.comp (centerDescend Y)

theorem descendTo_apply (e : (Y ⧸ Subgroup.center Y) ≃* P) (τ : MulAut Y) :
    descendTo e τ = MulAut.congr e (centerDescend Y τ) := rfl

theorem mem_innAutDerived_of_inverting_lift [Group.IsPerfect Y] (e : (Y ⧸ Subgroup.center Y) ≃* P)
    {α τ : MulAut Y} (h3 : α ^ 3 = 1)
    (hinn : IsInnerAut (descendTo e τ * descendTo e α * (descendTo e τ)⁻¹ * descendTo e α)) :
    α ∈ innAutDerived Y := by
  have hc : ⁅τ, α⁆ ∈ commutator (MulAut Y) := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hprod : ⁅τ, α⁆ * α ^ 2 = τ * α * τ⁻¹ * α := by
    rw [commutatorElement_def]
    group
  have hinn' : IsInnerAut (⁅τ, α⁆ * α ^ 2) := by
    rw [hprod]
    have h1 : IsInnerAut (MulAut.congr e (centerDescend Y (τ * α * τ⁻¹ * α))) := by
      have : MulAut.congr e (centerDescend Y (τ * α * τ⁻¹ * α)) =
          descendTo e τ * descendTo e α * (descendTo e τ)⁻¹ * descendTo e α := by
        simp only [descendTo_apply, map_mul, map_inv]
      rw [this]
      exact hinn
    exact isInnerAut_of_isInnerAut_centerDescend ((isInnerAut_congr e _).1 h1)
  have hinner : ⁅τ, α⁆ * α ^ 2 ∈ innAutDerived Y := innerAut_le_innAutDerived Y hinn'
  have hα2 : α ^ 2 ∈ innAutDerived Y := by
    have hα2eq : α ^ 2 = (⁅τ, α⁆)⁻¹ * (⁅τ, α⁆ * α ^ 2) := by group
    rw [hα2eq]
    exact (innAutDerived Y).mul_mem ((innAutDerived Y).inv_mem
      (commutator_le_innAutDerived Y hc)) hinner
  have : α = (α ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
  rw [this]
  exact (innAutDerived Y).pow_mem hα2 2

end Abstract

section Psu

variable {ℓ f n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def barAut (h : UnitaryFieldData ℓ f K) : K ≃+* K :=
  RingEquiv.ofRingHom h.bar h.bar (RingHom.ext h.bar_bar) (RingHom.ext h.bar_bar)

theorem det_glAut_bar_mul (h : UnitaryFieldData ℓ f K)
    (M : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ((glAut (barAut h) (M : GL (Fin n) K) * (M : GL (Fin n) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det = 1 := by
  have hM : (((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have hM' : (((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := M.2
    simpa using hM'
  rw [Units.val_mul, Matrix.det_mul, coe_glAut]
  have h1 := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  exact h1

theorem isInnerAut_field_conj_mul (h : UnitaryFieldData ℓ f K)
    (M : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    IsInnerAut (primeFormFieldHom h (isPrimeFormGram_one (n := n)) (barAut h) *
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M *
      (primeFormFieldHom h (isPrimeFormGram_one (n := n)) (barAut h))⁻¹ *
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M) := by
  rw [primeFormField_conj_eq, ← map_mul]
  set A := primeFormFieldU h (isPrimeFormGram_one (n := n)) (barAut h) M * M with hA
  have hAmem : (A : GL (Fin n) K) ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ⟨A.2, det_glAut_bar_mul h M⟩
  refine ⟨((⟨(A : GL (Fin n) K), hAmem⟩ : gramSU h ((1 : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), ?_⟩
  rw [← primeFormConjHom_liftUnitary]
  rfl

theorem mem_innAutDerived_of_diag {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (h : UnitaryFieldData ℓ f K)
    (e : (Y ⧸ Subgroup.center Y) ≃*
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hM : IsCyclic (hopfMultiplier (Y ⧸ Subgroup.center Y))) {α : MulAut Y} (h3 : α ^ 3 = 1)
    (hD : descendTo e α ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    α ∈ innAutDerived Y := by
  classical
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  haveI : Finite (Y ⧸ Subgroup.center Y) := inferInstance
  haveI : Group.IsPerfect (Y ⧸ Subgroup.center Y) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center Y))
      (QuotientGroup.mk'_surjective _)
  set π : Y →* (Y ⧸ Subgroup.center Y) := QuotientGroup.mk' (Subgroup.center Y) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker ≤ Subgroup.center Y := (QuotientGroup.ker_mk' _).le
  set fφ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) (barAut h) with hfφ
  obtain ⟨τY, hτY⟩ := exists_lift_aut_of_cyclic_multiplier hM π hπ hπker
    (MulAut.congr e.symm fφ)
  refine mem_innAutDerived_of_inverting_lift e h3 (τ := τY) ?_
  have hρτ : descendTo e τY = fφ := by
    refine MulEquiv.ext fun p => ?_
    obtain ⟨y, rfl⟩ : ∃ y : Y, e (QuotientGroup.mk y) = p := by
      obtain ⟨q, rfl⟩ := e.surjective p
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨y, rfl⟩
    rw [descendTo_apply, ← descend_compat e τY y]
    have h1 := hτY y
    have h2 : (QuotientGroup.mk (τY y) : Y ⧸ Subgroup.center Y) =
        e.symm (fφ (e (QuotientGroup.mk y))) := by
      simpa [hπdef, MulAut.congr_apply] using h1
    rw [h2]
    simp
  rw [hρτ]
  obtain ⟨M, hMα⟩ := hD
  rw [← hMα]
  exact isInnerAut_field_conj_mul h M

end Psu

end CFSG.HardMathSupport.Dickson.Sec6.I923

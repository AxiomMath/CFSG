module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreAct
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.Front.SpAut
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CentralProd
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5Sp4

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsSp4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem proj_lift (A : gsp 2 K) (σ : K ≃+* K) (x : ↥(StatedSp 2 K)) :
    (SymplecticHigher.conjAut 2 K A * fieldAut 2 K σ) (proj 2 K x) =
      proj 2 K ((conjSp 2 K A * fieldSp 2 K σ) x) := rfl

theorem lift_fix_of_perfect (τ : MulAut ↥(StatedSp 2 K)) (β : MulAut (StatedProj (StatedSp 2 K)))
    (hτ : ∀ x, β (proj 2 K x) = proj 2 K (τ x)) (M : Subgroup ↥(StatedSp 2 K)) [Group.IsPerfect M]
    (hfix : ∀ m ∈ M, β (proj 2 K m) = proj 2 K m) : ∀ m ∈ M, τ m = m := by
  have hc : ∀ m ∈ M, m⁻¹ * τ m ∈ Subgroup.center ↥(StatedSp 2 K) := fun m hm => by
    have h := hfix m hm
    rw [hτ] at h
    have := QuotientGroup.eq.mp h.symm
    rw [← GH74.Generic.spScalars_eq_center]
    exact this
  let χ : M →* Subgroup.center ↥(StatedSp 2 K) :=
    { toFun := fun m => ⟨(m : ↥(StatedSp 2 K))⁻¹ * τ m, hc m m.2⟩
      map_one' := by ext; simp
      map_mul' := fun m m' => by
        apply Subtype.ext
        have hz := Subgroup.mem_center_iff.mp (hc m m.2)
        show ((m : ↥(StatedSp 2 K)) * m')⁻¹ * τ (m * m') =
          (m : ↥(StatedSp 2 K))⁻¹ * τ m * ((m' : ↥(StatedSp 2 K))⁻¹ * τ m')
        rw [map_mul, mul_inv_rev]
        calc (m' : ↥(StatedSp 2 K))⁻¹ * (m : ↥(StatedSp 2 K))⁻¹ * (τ m * τ m') =
            (m' : ↥(StatedSp 2 K))⁻¹ * ((m : ↥(StatedSp 2 K))⁻¹ * τ m) * τ m' := by group
          _ = (m : ↥(StatedSp 2 K))⁻¹ * τ m * ((m' : ↥(StatedSp 2 K))⁻¹ * τ m') := by
            rw [hz (m' : ↥(StatedSp 2 K))⁻¹]; group }
  have : Group.IsSolvable (Subgroup.center ↥(StatedSp 2 K)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  have hχ := eq_one_of_isPerfect_of_isSolvable χ
  intro m hm
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hχ ⟨m, hm⟩)
  have h2 : m⁻¹ * τ m = 1 := h1
  rw [inv_mul_eq_one] at h2
  exact h2.symm

end CFSG.ClassicalInvolution.Q3.TA3.Q5Sp4

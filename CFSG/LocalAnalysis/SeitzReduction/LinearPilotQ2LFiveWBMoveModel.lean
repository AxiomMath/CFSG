module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBLevi

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type*} [Field K]

theorem col_eq_of_mul_pointRadMat_comm (hK : Nat.card K = 2) {c : Fin n} {r : Fin n → K}
    (hr : Function.update r c 0 ≠ 0) {B : SpecialLinearGroup (Fin n) K}
    (hB : (B : Matrix (Fin n) (Fin n) K) * pointRadMat c r =
      pointRadMat c r * (B : Matrix (Fin n) (Fin n) K)) :
    ∀ i, (B : Matrix (Fin n) (Fin n) K) i c = (1 : Matrix (Fin n) (Fin n) K) i c := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hr
  have hj1 : Function.update r c 0 j = 1 :=
    (eq_zero_or_eq_one_of_natCard_eq_two hK _).resolve_left hj
  have hN : vecMulVec ((B : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single c 1) (Function.update r c 0) =
      vecMulVec (Pi.single c 1) (Function.update r c 0 ᵥ* (B : Matrix (Fin n) (Fin n) K)) := by
    have h := hB
    simp only [pointRadMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      mul_vecMulVec, vecMulVec_mul] at h
    exact add_left_cancel h
  have hcol : ∀ i, (B : Matrix (Fin n) (Fin n) K) i c =
      (Pi.single c (1 : K) : Fin n → K) i *
        (Function.update r c 0 ᵥ* (B : Matrix (Fin n) (Fin n) K)) j := by
    intro i
    have h := congrFun (congrFun hN i) j
    simp only [vecMulVec_apply, hj1, mul_one, mulVec_single_one] at h
    exact h
  have hμ : (Function.update r c 0 ᵥ* (B : Matrix (Fin n) (Fin n) K)) j ≠ 0 := by
    intro h0
    have hdet := Matrix.det_eq_zero_of_column_eq_zero c (A := (B : Matrix (Fin n) (Fin n) K))
      (fun i => by rw [hcol i, h0, mul_zero])
    rw [B.2] at hdet
    exact one_ne_zero hdet
  have hμ1 := (eq_zero_or_eq_one_of_natCard_eq_two hK _).resolve_left hμ
  intro i
  rw [hcol i, hμ1, mul_one, Matrix.one_apply, Pi.single_apply]

theorem centralizer_le_normalizer_pointRadical (hK : Nat.card K = 2) {c : Fin n}
    {v : LinearFlag.projectiveSL n K} (hv : v ∈ pointRadical (K := K) c) (hv1 : v ≠ 1) :
    centralizer ({v} : Set (LinearFlag.projectiveSL n K)) ≤
      normalizer (pointRadical (K := K) c : Set (LinearFlag.projectiveSL n K)) := by
  obtain ⟨r, -, rfl⟩ := mem_pointRadical_iff_exists_pointRadElem.1 hv
  have hr : Function.update r c 0 ≠ 0 := by
    intro h0
    apply hv1
    have h1 : pointRadElem c r = 1 := by
      apply Subtype.ext
      rw [coe_pointRadElem, pointRadMat, h0, vecMulVec_zero, add_zero]
      rfl
    rw [h1, map_one]
  have key : ∀ g ∈ centralizer ({LinearFlag.proj n K (pointRadElem c r)} :
      Set (LinearFlag.projectiveSL n K)), ∀ w ∈ pointRadical (K := K) c,
      g * w * g⁻¹ ∈ pointRadical (K := K) c := by
    intro g hg w hw
    obtain ⟨B, rfl⟩ := LinearFlag.proj_surjective n K g
    obtain ⟨s, -, rfl⟩ := mem_pointRadical_iff_exists_pointRadElem.1 hw
    have hcomm : B * pointRadElem c r = pointRadElem c r * B := by
      apply proj_injective_of_natCard_eq_two hK
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.1 hg
    have hBm : (B : Matrix (Fin n) (Fin n) K) * pointRadMat c r =
        pointRadMat c r * (B : Matrix (Fin n) (Fin n) K) := by
      have h := congrArg (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K))
        hcomm
      simpa only [SpecialLinearGroup.coe_mul, coe_pointRadElem] using h
    have hcol := col_eq_of_mul_pointRadMat_comm hK hr hBm
    have hinv : (B : Matrix (Fin n) (Fin n) K) *
        ((B⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
    have hBe : (B : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single c 1 = Pi.single c 1 := by
      rw [mulVec_single_one, col_eq_single_of_forall_apply_eq_one_apply hcol]
    have hB'e : ((B⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        Pi.single c 1 = Pi.single c 1 := by
      conv_lhs => rw [← hBe]
      rw [mulVec_mulVec, ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one,
        one_mulVec]
    have hcol' : ∀ i, ((B⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i c =
        (1 : Matrix (Fin n) (Fin n) K) i c := by
      intro i
      have h := congrFun hB'e i
      rw [mulVec_single_one] at h
      rw [show ((B⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i c =
        (((B⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).col c) i from rfl, h,
        Matrix.one_apply, Pi.single_apply]
    have hconj : B * pointRadElem c s * B⁻¹ =
        pointRadElem c (Function.update s c 0 ᵥ*
          ((B⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      apply Subtype.ext
      rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_pointRadElem,
        coe_pointRadElem]
      exact mul_pointRadMat_mul_of_col_eq hinv hcol hcol' s
    rw [← map_mul, ← map_inv, ← map_mul, hconj]
    exact proj_pointRadElem_mem_pointRadical c _
  intro g hg
  rw [mem_normalizer_iff]
  intro w
  refine ⟨key g hg w, fun h => ?_⟩
  have h2 := key g⁻¹ (inv_mem hg) _ h
  rwa [show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at h2

end CFSG.SeitzReduction.LinearPilot

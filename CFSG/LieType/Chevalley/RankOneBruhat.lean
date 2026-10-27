module

public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.WeylRoots

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {R : Type*} [CommRing R]

theorem weylElt_one_mul_weylElt
    (i : Fin τ.rank) (c : Rˣ) :
    weylElt τ R i 1 * weylElt τ R i c = torusElt τ R i (-c⁻¹) := by
  rw [← torusElt_mul_weylElt_one τ R i c, ← mul_assoc, weylElt_mul_torusElt τ R i i 1 c,
    mul_assoc, weylElt_one_mul_self, τ.cartan_self, ← torusElt_mul, ← torusElt_mul]
  congr 1
  rw [mul_neg_one, zpow_neg, zpow_two, mul_inv_rev, mul_inv_cancel_left]

theorem weylElt_one_mul_xUnit
    (i : Fin τ.rank) (c : Rˣ) :
    weylElt τ R i 1 * xUnit τ R i c =
      xUnit τ R i (-((c⁻¹ : Rˣ) : R)) * torusElt τ R i (-c⁻¹) * yUnit τ R i ((c⁻¹ : Rˣ) : R) := by
  have hx : xOp τ R i c = yOp τ R i ((c⁻¹ : Rˣ) : R) *
      (weylElt τ R i c : Module.End R (RootModule τ R)) * yOp τ R i ((c⁻¹ : Rˣ) : R) := by
    rw [coe_weylElt_eq_yOp_mul, ← mul_assoc, ← mul_assoc,
      yOp_mul_yOp_neg (downTransport τ), one_mul, mul_assoc,
      yOp_neg_mul_yOp (downTransport τ), mul_one]
  have hy := weylElt_mul_yOp (τ := τ) (R := R) i 1 ((c⁻¹ : Rˣ) : R)
  rw [Units.val_one, one_pow, mul_one] at hy
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_xUnit, coe_xUnit, coe_yUnit, hx,
    ← mul_assoc, ← mul_assoc, hy, mul_assoc (xOp τ R i _), ← Units.val_mul,
    weylElt_one_mul_weylElt]

theorem simple_rank_one_bruhat_identity
    (τ : Tag) (R : Type*) [CommRing R] :
    (∀ (i : Fin τ.rank) (c : Rˣ),
      weylElt τ R i 1 * xUnit τ R i c =
        xUnit τ R i (-((c⁻¹ : Rˣ) : R)) * torusElt τ R i (-c⁻¹) * yUnit τ R i ((c⁻¹ : Rˣ) : R)) ∧
    ∀ (K : Type*) [Field K] (i : Fin τ.rank) (c : K), c ≠ 0 →
      ∃ b ∈ borelGroup τ K, weylElt τ K i 1 * xUnit τ K i c = b * yUnit τ K i c⁻¹ := by
  refine ⟨weylElt_one_mul_xUnit, fun K _ i c hc => ⟨xUnit τ K i (-((Units.mk0 c hc)⁻¹ : Kˣ) : K) *
      torusElt τ K i (-(Units.mk0 c hc)⁻¹), ?_, ?_⟩⟩
  · refine mul_mem (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left (torusElt_mem_torusGroup i _))
    rw [← pinnedX_single]
    exact Subgroup.mem_iSup_of_mem (Pi.single i 1) (Subgroup.mem_iSup_of_mem
      ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩ (Subgroup.subset_closure ⟨_, rfl⟩))
  · have h := weylElt_one_mul_xUnit (τ := τ) i (Units.mk0 c hc)
    rw [Units.val_mk0] at h
    rw [h, Units.val_inv_eq_inv_val (Units.mk0 c hc), Units.val_mk0]

end CFSG.LieType.Chevalley

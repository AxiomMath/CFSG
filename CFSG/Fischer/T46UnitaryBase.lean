
module

public import CFSG.Fischer.T46Base
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native Matrix

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

noncomputable abbrev piSU : SU0 →* Equiv.Perm (Fin 693) :=
  piGU.comp (Subgroup.inclusion SU0_le_GU0)

theorem piSU_apply (g : SU0) (i : Fin 693) :
    (piSU g i).val = ptIdx (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec (uVec i)) :=
  smul_val _ i

theorem t46G_mem_range (z : ℤ) : t46G z ∈ piSU.range :=
  ⟨⟨tvGL _ (tvGens_get_iso _), tvGL_mem_SU0 (tvGens_get_iso _)⟩, rfl⟩

theorem T46_le_range : T46 ≤ piSU.range := by
  unfold T46 t46lvl levelGroup lettersGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨l, -, rfl⟩
  have hw : ∀ j, t46gs j ∈ piSU.range := fun j => by
    unfold t46gs wordG
    exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
      exact t46G_mem_range z
  unfold pairG
  split_ifs
  · exact hw _
  · exact Subgroup.inv_mem _ (hw _)

theorem isIsom_inv {g : GL (Fin 6) F4} (hg : IsIsom (g : Matrix (Fin 6) (Fin 6) F4)) :
    IsIsom ((g⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) :=
  (GU0.inv_mem (show g ∈ GU0 from hg) : _)

theorem mulVec_inv_mulVec (g : GL (Fin 6) F4) (x : W) :
    (g : Matrix (Fin 6) (Fin 6) F4).mulVec
      (((g⁻¹ : GL (Fin 6) F4) : Matrix _ _ F4).mulVec x) = x := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem conj_tvM {g : GL (Fin 6) F4} (hg : IsIsom (g : Matrix (Fin 6) (Fin 6) F4)) (v x : W) :
    (g : Matrix (Fin 6) (Fin 6) F4).mulVec
      ((tvM v).mulVec (((g⁻¹ : GL (Fin 6) F4) : Matrix _ _ F4).mulVec x)) =
      (tvM ((g : Matrix (Fin 6) (Fin 6) F4).mulVec v)).mulVec x := by
  rw [tvM_mulVec, tvM_mulVec, mulVec_add, mulVec_smul, mulVec_inv_mulVec]
  congr 2
  have := hg (((g⁻¹ : GL (Fin 6) F4) : Matrix _ _ F4).mulVec x) v
  rw [mulVec_inv_mulVec, herm_eq_std, herm_eq_std] at this
  exact this.symm

theorem herm_single_left (j : Fin 6) (v : W) : hermStd (Pi.single j 1) v = (v j) ^ 2 := by
  unfold hermStd
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · simp

private theorem sq_ne_zero' : ∀ c : F4, c ≠ 0 → c ^ 2 ≠ 0 := by decide

theorem ptIdx_eq_of_tvM_eq {v w : W} (hv : v ≠ 0) (h : tvM v = tvM w) : ptIdx v = ptIdx w := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.1 hv
  have hx : hermStd (Pi.single j 1) v • v = hermStd (Pi.single j 1) w • w := by
    have := congrArg (fun M => M.mulVec (Pi.single j 1)) h
    simpa only [tvM_mulVec, add_right_inj] using this
  rw [herm_single_left, herm_single_left] at hx
  have hα : v j ^ 2 ≠ 0 := sq_ne_zero' _ hj
  have hβ : w j ^ 2 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hx
    apply hv
    have := congrArg (fun u => (v j ^ 2)⁻¹ • u) hx
    simpa [smul_smul, inv_mul_cancel₀ hα] using this
  have hvw : v = ((v j ^ 2)⁻¹ * w j ^ 2) • w := by
    rw [← smul_smul, ← hx, smul_smul, inv_mul_cancel₀ hα, one_smul]
  rw [hvw, ptIdx_smul (mul_ne_zero (inv_ne_zero hα) hβ)]

theorem center_le_ker : Subgroup.center SU0 ≤ piSU.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  ext i
  rw [piSU_apply, Equiv.Perm.one_apply]
  have hv := uVec_ne_zero ptsFacts i.2
  have hiso := uVec_iso ptsFacts i.2
  have hc : ((z : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * tvM (uVec i) =
      tvM (uVec i) * ((z : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
    have := congrArg (fun g : SU0 => ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))
      (Subgroup.mem_center_iff.1 hz ⟨tvGL (uVec i) hiso, tvGL_mem_SU0 hiso⟩)
    simp only [Subgroup.coe_mul, Units.val_mul, tvGL_val] at this
    exact this.symm
  have hzI : IsIsom ((z : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := SU0_le_GU0 z.2
  have heq : tvM (((z : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec (uVec i)) =
      tvM (uVec i) := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [← conj_tvM hzI, mulVec_mulVec, hc, ← mulVec_mulVec, mulVec_inv_mulVec]
  rw [ptIdx_eq_of_tvM_eq (mulVec_ne_zero _ hv) heq, ptIdx_uVec ptsFacts i.2]

theorem card_SU0_eq : Nat.card SU0 = Nat.card piSU.range * Nat.card piSU.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup piSU.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange piSU).toEquiv]

theorem card_range_ker_le :
    Nat.card piSU.range * Nat.card piSU.ker ≤ 9196830720 * Nat.card piSU.ker := by
  rw [← card_SU0_eq, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SU0)]
  exact Nat.mul_le_mul card_psu_le (Subgroup.card_le_of_le center_le_ker)

theorem card_range_le : Nat.card piSU.range ≤ 9196830720 :=
  Nat.le_of_mul_le_mul_right card_range_ker_le Nat.card_pos

end CFSG.Fischer

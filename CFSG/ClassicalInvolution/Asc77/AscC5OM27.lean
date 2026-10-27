module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Asc77.AscC5OM23

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

@[expose] def slConj (g : GL (Fin 2) F) (b : SL(2, F)) : SL(2, F) :=
  ⟨(g : Matrix (Fin 2) (Fin 2) F) * b * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_mul, Matrix.det_mul, b.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]⟩

theorem slg_slConj (g : GL (Fin 2) F) (b : SL(2, F)) :
    Matrix.SpecialLinearGroup.toGL (slConj g b) = g * Matrix.SpecialLinearGroup.toGL b * g⁻¹ :=
  Units.ext rfl

theorem longInv_of_map_le [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (α : MulAut (StatedSp 2 F)) (k : Fin 2)
    (h : ∀ r ∈ longRootSp2 F 2 0, α r ∈ longRootSp2 F 2 k ⊔ spScalars 2 F) :
    α (longInv F 2 0) = longInv F 2 k := by
  have : Group.IsPerfect (longRootSp2 F 2 0) := (isClassicalSL2_longRootSp2 h2 0).isPerfect h4
  have : Group.IsPerfect ((longRootSp2 F 2 0).map α.toMonoidHom) :=
    Group.IsPerfect.map α.toMonoidHom
  have hHle : (longRootSp2 F 2 0).map α.toMonoidHom ≤ longRootSp2 F 2 k ⊔ spScalars 2 F := by
    rintro _ ⟨r, hr, rfl⟩
    exact h r hr
  have hle := le_of_perfect_of_le_sup_center Subgroup.commutator_eq_self spScalars_le_center hHle
  have hi : α (longInv F 2 0) ∈ longRootSp2 F 2 k := hle ⟨_, longInv_mem_longRootSp2 0, rfl⟩
  have hsq : α (longInv F 2 0) * α (longInv F 2 0) = 1 := by
    rw [← map_mul, longInv_mul_self, map_one]
  rcases sq_eq_one_of_mem_L h2 k hi hsq with h' | h'
  · exfalso
    apply longInv_ne_one h2 0
    exact α.injective (by rw [h', map_one])
  · exact h'

theorem sw_conj_longBlock (k : Fin 2) (b : SL(2, F)) :
    sw F * longBlock F 2 k b * (sw F)⁻¹ = longBlock F 2 (Fin.rev k) b := by
  rw [sw_inv]
  apply mat_injective
  rw [map_mul, map_mul, mat_longBlock_eq_bd, mat_longBlock_eq_bd, mat_sw]
  ext x y
  rcases x with i | i <;> rcases y with j | j <;> fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [swMat, perm2, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks]

theorem conjSp_of_sp (g : StatedSp 2 F) (x : StatedSp 2 F) :
    conjSp 2 F ⟨g, statedSp_le_gsp g.2⟩ x = g * x * g⁻¹ :=
  Subtype.ext rfl

theorem fieldSp_refl (x : StatedSp 2 F) : fieldSp 2 F (RingEquiv.refl F) x = x := by
  rw [show RingEquiv.refl F = 1 from rfl, map_one]
  rfl

theorem exists_swap_block (h2 : (2 : F) ≠ 0) (N : gsp 2 F)
    (hN : conjSp 2 F N (longInv F 2 0) = longInv F 2 1) :
    ∃ g : GL (Fin 2) F, ∀ b : SL(2, F),
      conjSp 2 F N (longBlock F 2 0 b) = longBlock F 2 1 (slConj g b) := by
  set s : gsp 2 F := ⟨sw F, statedSp_le_gsp (sw F).2⟩ with hs
  have hcs : ∀ x, conjSp 2 F s x = sw F * x * (sw F)⁻¹ := fun x => conjSp_of_sp (sw F) x
  have hss2 : s * s = 1 := Subtype.ext (by
    change ((sw F : GL (Fin 2 ⊕ Fin 2) F)) * (sw F : GL (Fin 2 ⊕ Fin 2) F) = 1
    exact congrArg Subtype.val (sw_mul_self (F := F)))
  set B : gsp 2 F := s * N with hB
  have hNB : N = s * B := by
    rw [hB, ← mul_assoc, hss2, one_mul]
  have hBi : conjSp 2 F B (fieldSp 2 F (RingEquiv.refl F) (longInv F 2 0)) = longInv F 2 0 := by
    rw [fieldSp_refl, hB, map_mul, MulAut.mul_apply, hN, hcs, sw_conj_longInv]
    rfl
  have hBD : IsBD (gm B) := isBD_gm_of_conjSp_longInv h2 B (RingEquiv.refl F) hBi
  set gB : Fin 2 → Matrix (Fin 2) (Fin 2) F := fun k => stdBlock k (gm B) with hgB
  have hgm : gm B = bd gB := (bd_stdBlock hBD).symm
  have hdet : (gB 0).det ≠ 0 := by
    rw [det_eq_mu_of_gm_eq_bd B hgm 0]
    exact Units.ne_zero _
  set g := Matrix.GeneralLinearGroup.mkOfDetNeZero (gB 0) hdet with hg
  refine ⟨g, fun b => ?_⟩
  have h1 : conjSp 2 F B (longBlock F 2 0 b) = longBlock F 2 0 (slConj g b) := by
    have h := conjSp_fieldSp_longBlock B hgm (RingEquiv.refl F) 0 b (slConj g b) (by
      change (g : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
      rw [Matrix.coe_units_inv, hg]
      rfl)
    rwa [fieldSp_refl] at h
  rw [hNB, map_mul, MulAut.mul_apply, h1, hcs, sw_conj_longBlock]
  rfl

end CFSG.ClassicalInvolution.Asc77.C5O.M

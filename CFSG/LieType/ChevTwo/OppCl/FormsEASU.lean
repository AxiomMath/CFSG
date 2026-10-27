module

public import CFSG.LieType.ChevTwo.OppCl.Defs
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

variable (r : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
variable (f : ℕ) (hK : Nat.card F = (2 ^ f) ^ 2) (n : ℕ)

theorem ea_SU_aux :
    EA0 (unitaryForm 2 f hK n) (fun v => (unitaryForm 2 f hK n).β v v = 0)
      (natRep (StatedSU n (2 ^ f) F)) ∧
    EA1 (unitaryForm 2 f hK n) (fun v => (unitaryForm 2 f hK n).β v v = 0)
      (natRep (StatedSU n (2 ^ f) F)) ∧
    EA2 (unitaryForm 2 f hK n) (fun v => (unitaryForm 2 f hK n).β v v = 0)
      (natRep (StatedSU n (2 ^ f) F)) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    intro x y hx hy hxy
    have hx' : (unitaryForm 2 f hK n).β x x = 0 := hx
    have hy' : (unitaryForm 2 f hK n).β y y = 0 := hy
    have hc : (0 : F) + unitaryInvolution F 2 f 0 = -(unitaryForm 2 f hK n).β y y := by
      rw [map_zero, zero_add, hy', neg_zero]
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedSU_eichler hK hx' hxy hc
    refine ⟨⟨A, hA⟩, fun v => ?_⟩
    have hv := hAv v
    simp only [zero_smul, add_zero] at hv
    rw [natRep_apply]
    exact hv
  ·
    intro x y hx hxy
    have hx' : (unitaryForm 2 f hK n).β x x = 0 := hx
    have ha : unitaryInvolution F 2 f ((unitaryForm 2 f hK n).β y y) =
        (unitaryForm 2 f hK n).β y y :=
      (unitaryForm_symm hK y y).symm
    obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq hK ha
    have hc' : c + unitaryInvolution F 2 f c = -(unitaryForm 2 f hK n).β y y := by
      rw [hc, CharTwo.neg_eq]
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedSU_eichler hK hx' hxy hc'
    refine ⟨c, ⟨A, hA⟩, fun v => ?_⟩
    rw [natRep_apply]
    exact hAv v
  ·
    intro x c hx hc
    have hx' : (unitaryForm 2 f hK n).β x x = 0 := hx
    have hc' : unitaryInvolution F 2 f c = -c := by
      rw [CharTwo.neg_eq]
      exact hc
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedSU_transvection hK hx' hc'
    refine ⟨⟨A, hA⟩, fun v => ?_⟩
    rw [natRep_apply]
    exact hAv v

end CFSG.LieType.ChevTwo.OppCl

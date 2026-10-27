module

public import CFSG.GF2Type.Widths1112.Co2Module.Assembly
public import CFSG.GF2Type.Widths1112.Co2Module.NormalForm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112

open CFSG.GF2W1112 CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open CFSG.GF2Type.Widths1112.Co2Module

theorem gen_zero_ne_one :
    gen 0 ≠ 1 := by
  have h : w12UCheck1 () = true := Certificates.certificate38957
  unfold w12UCheck1 at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  intro h0
  have h3 : mat2 (gen 0) = rowsMatrix 22 ((w12URows ()).getD 0 #[]) := mat2_gen 0 (by norm_num)
  rw [h0, mat2_one, ← rowsMatrix_idRows 22] at h3
  have h4 := w12UEqR_iff.2 h3.symm
  have h5 : (w12URows ())[0]! = (w12URows ()).getD 0 #[] := Array.getElem!_eq_getD
  rw [h5, h4] at h
  exact absurd h.2 (by decide)

theorem co2Act_injective : Function.Injective co2Act := by
  intro g h e
  have e' : Matrix.mulVecLin (g : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      Matrix.mulVecLin (h : Matrix (Fin 22) (Fin 22) (ZMod 2)) := e
  rw [← Matrix.toLin'_apply', ← Matrix.toLin'_apply'] at e'
  exact Units.ext (Subtype.ext (Matrix.toLin'.injective e'))

theorem iotaE_single_zero :
    iotaE (Pi.single 0 1) = gen 0 := by
  rw [iotaE_single, ee_eq]
  simp

theorem co2ModuleUniqueness_holds :
    Co2ModuleUniqueness := by
  intro V _ _ hV ρ hρ _q _hq _hinv
  have hne : gen 0 ≠ 1 := gen_zero_ne_one
  refine exists_equiv co2BlockData ρ co2Act hV (by simp) ⟨Pi.single 0 1, ?_⟩
    ⟨Pi.single 0 1, ?_⟩
  · rw [iotaE_single_zero]
    intro h
    exact hne (hρ (h.trans (map_one ρ).symm))
  · rw [iotaE_single_zero]
    intro h
    exact hne (co2Act_injective (h.trans (map_one co2Act).symm))

end CFSG.GF2Type.Widths1112

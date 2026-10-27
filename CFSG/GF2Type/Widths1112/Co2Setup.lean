module

public import CFSG.GF2Type.Widths1112.Co2Defs
public import CFSG.Sporadic.Co2
public import Certificates.Data.GF2W1112Co2
import all CFSG.Blueprint.NativeSporadic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2.Native
  CFSG.GF2W1112 Matrix

abbrev Vec22 : Type := Fin 22 → ZMod 2

theorem co2BaseFacts : BaseFacts (co2Data ()) :=
  CFSG.Sporadic.Co2.co2Facts.toBaseFacts

theorem co2Act_def (g : NativeSporadic.Co2) (v : Vec22) :
    co2Act g v = (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) *ᵥ v := rfl

private noncomputable def mat22 : NativeSporadic.Co2 →* Matrix (Fin 22) (Fin 22) (ZMod 2) where
  toFun g := g.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem co2Act_apply_eq_mulVec (g : NativeSporadic.Co2) (v : Vec22) :
    co2Act g v = mat22 g *ᵥ v :=
  co2Act_def g v

theorem co2Act_mul (g h : NativeSporadic.Co2) (v : Vec22) :
    co2Act (g * h) v = co2Act g (co2Act h v) := by
  have hmul : (g * h).val.val = g.val.val * h.val.val := rfl
  rw [co2Act_def (g * h) v, co2Act_def g (co2Act h v), co2Act_def h v, hmul, Matrix.mulVec_mulVec]

theorem co2Act_one (v : Vec22) : co2Act 1 v = v := by
  have h1 : ((1 : NativeSporadic.Co2).val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) = 1 := rfl
  rw [co2Act_def, h1, Matrix.one_mulVec]

theorem co2Act_add (g : NativeSporadic.Co2) (u v : Vec22) :
    co2Act g (u + v) = co2Act g u + co2Act g v := by
  simp only [co2Act_apply_eq_mulVec, Matrix.mulVec_add]

theorem co2Act_smul (g : NativeSporadic.Co2) (a : ZMod 2) (v : Vec22) :
    co2Act g (a • v) = a • co2Act g v := by
  simp only [co2Act_apply_eq_mulVec, Matrix.mulVec_smul]

theorem co2Act_inv_apply (g : NativeSporadic.Co2) (v : Vec22) :
    co2Act g⁻¹ (co2Act g v) = v := by
  rw [← co2Act_mul, inv_mul_cancel, co2Act_one]

theorem co2Act_apply_inv (g : NativeSporadic.Co2) (v : Vec22) :
    co2Act g (co2Act g⁻¹ v) = v := by
  rw [← co2Act_mul, mul_inv_cancel, co2Act_one]

noncomputable def co2Lin (g : NativeSporadic.Co2) : Vec22 →ₗ[ZMod 2] Vec22 :=
  Matrix.mulVecLin (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2))

theorem co2Lin_apply (g : NativeSporadic.Co2) (v : Vec22) : co2Lin g v = co2Act g v := by
  rw [co2Act_def]
  unfold co2Lin
  exact Matrix.mulVecLin_apply _ _

open CFSG.Sporadic

section Seeds

variable {D : VecData} (hB : BaseFacts D)
include hB

theorem seedMonoid_eq_closure_gen :
    NativeSporadic.seedMonoid 2 D.d 1 D.seedA D.seedB =
      Submonoid.closure {((SmallF2.gA D : GL (Fin D.d) (ZMod 2)) :
        Matrix (Fin D.d) (Fin D.d) (ZMod 2)), ((SmallF2.gB D : GL (Fin D.d) (ZMod 2)) :
        Matrix (Fin D.d) (Fin D.d) (ZMod 2))} := by
  have h1 : ((SmallF2.gA D : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) =
      SmallF2.mA D := a_val hB
  have h2 : ((SmallF2.gB D : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) =
      SmallF2.mB D := b_val hB
  rw [h1, h2]
  rfl

@[expose] noncomputable def unitsEquiv_gen :
    (NativeSporadic.seedMonoid 2 D.d 1 D.seedA D.seedB)ˣ ≃* SmallF2.J D :=
  (Units.mapEquiv (MulEquiv.submonoidCongr (seedMonoid_eq_closure_gen hB))).trans
    (NativeSporadic.unitSeedEquiv (SmallF2.gA D) (SmallF2.gB D))

theorem unitsEquiv_val_gen
    (g : (NativeSporadic.seedMonoid 2 D.d 1 D.seedA D.seedB)ˣ) :
    (((unitsEquiv_gen hB g : SmallF2.J D) : GL (Fin D.d) (ZMod 2)) :
      Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = g.val.val := rfl

theorem exists_unit_of_mem_gen (h : SmallF2.J D) :
    ∃ g : (NativeSporadic.seedMonoid 2 D.d 1 D.seedA D.seedB)ˣ,
      g.val.val = ((h : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) := by
  refine ⟨(unitsEquiv_gen hB).symm h, ?_⟩
  have := unitsEquiv_val_gen hB ((unitsEquiv_gen hB).symm h)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end Seeds

set_option maxRecDepth 4000 in
private theorem exists_co2_matA :
    ∃ g : NativeSporadic.Co2, (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      rowsMatrix 22 (w12Co2RowsA ()) := by
  obtain ⟨g, hg⟩ := exists_unit_of_mem_gen co2BaseFacts (SmallF2.a (co2Data ()))
  exact ⟨g, hg.trans ((a_val co2BaseFacts).trans (rowsMatrix_rowsA (co2Data ())).symm)⟩

set_option maxRecDepth 4000 in
private theorem exists_co2_matB :
    ∃ g : NativeSporadic.Co2, (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      rowsMatrix 22 (w12Co2RowsB ()) := by
  obtain ⟨g, hg⟩ := exists_unit_of_mem_gen co2BaseFacts (SmallF2.b (co2Data ()))
  exact ⟨g, hg.trans ((b_val co2BaseFacts).trans (rowsMatrix_rowsB (co2Data ())).symm)⟩

private theorem exists_co2_gen (b : Bool) :
    ∃ g : NativeSporadic.Co2, (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      rowsMatrix 22 (if b then w12Co2RowsA () else w12Co2RowsB ()) := by
  cases b
  · exact exists_co2_matB
  · exact exists_co2_matA

private theorem exists_co2_word_aux (w : List Bool) :
    ∀ acc : Array ℕ, (∃ g : NativeSporadic.Co2,
        (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) = rowsMatrix 22 acc) →
      ∃ g : NativeSporadic.Co2, (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
        rowsMatrix 22 (w.foldl (fun acc b => mulRows 22 acc
          (if b then w12Co2RowsA () else w12Co2RowsB ())) acc) := by
  induction w with
  | nil => intro acc h; exact h
  | cons b w ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨g₀, hg₀⟩ := h
    obtain ⟨x, hx⟩ := exists_co2_gen b
    refine ⟨g₀ * x, ?_⟩
    have hmul : (g₀ * x).val.val = g₀.val.val * x.val.val := rfl
    rw [hmul, hg₀, hx, rowsMatrix_mulRows]

theorem exists_co2_word (w : List Bool) :
    ∃ g : NativeSporadic.Co2, (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      rowsMatrix 22 (w12WordRows (w12Co2RowsA ()) (w12Co2RowsB ()) w) := by
  unfold w12WordRows
  exact exists_co2_word_aux w (idRows 22) ⟨1, (rowsMatrix_idRows 22).symm⟩

end CFSG.GF2Type.Widths1112

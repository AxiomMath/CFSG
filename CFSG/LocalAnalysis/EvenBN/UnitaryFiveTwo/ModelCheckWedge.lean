module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckLevi
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDWedgeData
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag Certificates.U52Yamada
open scoped Matrix

@[expose] def c1 (a : F4) : ZMod 2 := if a = 1 ∨ a = F4.ω + 1 then 1 else 0

@[expose] def cω (a : F4) : ZMod 2 := if a = F4.ω ∨ a = F4.ω + 1 then 1 else 0

theorem c1_add : ∀ a b : F4, c1 (a + b) = c1 a + c1 b := by
  unfold c1
  decide

theorem cω_add : ∀ a b : F4, cω (a + b) = cω a + cω b := by
  unfold cω
  decide

@[expose] def fCoordM (M : Matrix (Fin 5) (Fin 5) F4) : Fin 4 → ZMod 2 :=
  ![c1 (M 4 0), cω (M 3 0), c1 (M 3 0), c1 (M 3 1)]

@[expose] def fCoord (α : SU52) : Fin 4 → ZMod 2 := fCoordM (mat α)

theorem fMat_eq (p : F4 × F4 × F4) :
    fMat p = !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; p.2.1, p.1, 0, 1, 0;
      p.2.2, bar p.2.1, 0, 0, 1] := by
  obtain ⟨a, b, c⟩ := p
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fMat, nfMat, x₁Mat, x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]

theorem fCoordM_fMat (p : F4 × F4 × F4) :
    fCoordM (fMat p) = ![c1 p.2.2, cω p.2.1, c1 p.2.1, c1 p.1] := by
  rw [fMat_eq]
  rfl

theorem fCoord_mul {α β : SU52} (hα : α ∈ Fsub) (hβ : β ∈ Fsub) :
    fCoord (α * β) = fCoord α + fCoord β := by
  obtain ⟨p, -, -, hp⟩ := exists_fMat_of_mem_Fsub hα
  obtain ⟨q, -, -, hq⟩ := exists_fMat_of_mem_Fsub hβ
  have e : fMat p * fMat q = fMat (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2) := by
    rw [fMat_eq, fMat_eq, fMat_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_five, map_add]
  rw [fCoord, fCoord, fCoord, mat_mul, hp, hq, e, fCoordM_fMat, fCoordM_fMat, fCoordM_fMat]
  ext k
  fin_cases k <;> simp [c1_add, cω_add]

theorem fCoord_ker {α : SU52} (hα : α ∈ Fsub) (h : fCoord α = 0) : α = 1 := by
  obtain ⟨⟨a, b, c⟩, ha, hc, hp⟩ := exists_fMat_of_mem_Fsub hα
  rw [fCoord, hp, fCoordM_fMat] at h
  have key : ∀ a b c : F4, ValidPair 0 a → ValidPair 0 c →
      (![c1 c, cω b, c1 b, c1 a] : Fin 4 → ZMod 2) = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
    unfold ValidPair c1 cω
    simp only [bar_apply]
    decide
  obtain ⟨rfl, rfl, rfl⟩ := key a b c ha hc h
  exact ext_mat (by rw [hp, fMat_zero, mat_one])

@[expose] def ofBit (z : ZMod 2) : F4 := if z = 1 then 1 else 0

theorem fCoord_surj (v : Fin 4 → ZMod 2) : ∃ α ∈ Fsub, fCoord α = v := by
  have hv : ∀ z : ZMod 2, ValidPair 0 (ofBit z) := by
    unfold ValidPair ofBit
    simp only [bar_apply]
    decide
  have hshape : ∀ a b c : F4, IsFShape (fMat (a, b, c)) := by
    intro a b c
    rw [fMat_eq]
    revert a b c
    decide +kernel
  have k1 : ∀ z : ZMod 2, c1 (ofBit z) = z := by
    unfold c1 ofBit
    decide
  have k2 : ∀ z z' : ZMod 2, c1 (ofBit z + ofBit z' * F4.ω) = z := by
    unfold c1 ofBit
    decide
  have k3 : ∀ z z' : ZMod 2, cω (ofBit z + ofBit z' * F4.ω) = z' := by
    unfold cω ofBit
    decide
  refine ⟨fSU (ofBit (v 3), ofBit (v 2) + ofBit (v 1) * F4.ω, ofBit (v 0)) (hv _) (hv _),
    mem_Fsub_of_isFShape ?_, ?_⟩
  · rw [mat_fSU]
    exact hshape _ _ _
  · rw [fCoord, mat_fSU, fCoordM_fMat]
    ext k
    fin_cases k
    · exact k1 _
    · exact k3 _ _
    · exact k2 _ _
    · exact k1 _

@[expose] def wgA : Fin 3 → Matrix (Fin 2) (Fin 2) F4 :=
  ![!![1, 0; F4.ω, 1], !![1, 0; 1, 1], !![0, 1; F4.ω + 1, 0]]

theorem isUnit_det_wgA (g : Fin 3) : IsUnit (wgA g).det := by
  refine isUnit_iff_ne_zero.2 ?_
  revert g
  unfold wgA
  decide +kernel

@[expose] noncomputable def wgSU (g : Fin 3) : SU52 := levSU (wgA g) (isUnit_det_wgA g)

@[expose] def wgM : Fin 3 → Matrix (Fin 5) (Fin 5) F4 :=
  ![!![1, F4.ω + 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, F4.ω; 0, 0, 0, 0, 1],
    !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
    !![0, 1, 0, 0, 0; F4.ω + 1, 0, 0, 0, 0; 0, 0, F4.ω + 1, 0, 0; 0, 0, 0, 0, F4.ω + 1;
      0, 0, 0, 1, 0]]

@[expose] def wgN : Fin 3 → Matrix (Fin 5) (Fin 5) F4 :=
  ![wgM 0, wgM 1,
    !![0, F4.ω, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, F4.ω, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, F4.ω, 0]]

@[expose] def wgB : Fin 3 → Matrix (Fin 2) (Fin 2) F4 :=
  ![!![1, F4.ω + 1; 0, 1], !![1, 1; 0, 1], !![0, 1; F4.ω + 1, 0]]

@[expose] def wgD : Fin 3 → F4 := ![1, 1, F4.ω + 1]

theorem mat_wgSU (g : Fin 3) : mat (wgSU g) = wgM g := by
  have hB : barInvT hF4 (wgA g) = wgB g := barInvT_eq (by
    rw [hF4_bar]
    revert g
    unfold wgA wgB
    decide +kernel)
  have hD : hF4.bar (wgA g).det / (wgA g).det = wgD g := by
    have key : ∀ g : Fin 3, (wgA g).det ^ 2 / (wgA g).det = wgD g := by
      unfold wgA wgD
      decide +kernel
    rw [hF4_bar, bar_apply]
    exact key g
  ext i j
  rw [wgSU, mat_levSU, hD, CFSG.ClassicalGroups.UnitaryFlag.oddDiag, hB]
  fin_cases g <;> fin_cases i <;> fin_cases j <;>
    simp [yIdx, blk3, wgA, wgB, wgD, wgM, Matrix.fromBlocks]

theorem mat_wgSU_inv (g : Fin 3) : mat (wgSU g)⁻¹ = wgN g :=
  mat_inv_eq (by
    rw [mat_wgSU]
    revert g
    decide +kernel)

theorem fCoord_conj_wgSU (g : Fin 3) {α : SU52} (hα : α ∈ Fsub) :
    fCoord (wgSU g * α * (wgSU g)⁻¹) =
      CFSG.EvenSmallLie.UnitarySix.YamadaD.wedgeMatW g *ᵥ fCoord α := by
  obtain ⟨⟨a, b, c⟩, h₁, h₄, hp⟩ := exists_fMat_of_mem_Fsub hα
  rw [fCoord, fCoord, mat_mul, mat_mul, mat_wgSU, mat_wgSU_inv, hp, fMat_eq]
  clear hp
  revert g a b c
  unfold ValidPair
  decide +kernel

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

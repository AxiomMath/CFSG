module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessDefs
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Gamma

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def gammaPtLn (F : Type) [Field F] [CharP F 2] : ↥(Pt F) ≃* ↥(Ln F) where
  toFun x := ⟨gammaAut F (x : projectiveSL 3 F), (gammaAut_mem_Pt_iff F).mp x.2⟩
  invFun y := ⟨gammaAut F (y : projectiveSL 3 F), (gammaAut_mem_Ln_iff F).mp y.2⟩
  left_inv x := Subtype.ext (gammaAut_gammaAut F _)
  right_inv y := Subtype.ext (gammaAut_gammaAut F _)
  map_mul' x y := Subtype.ext (map_mul (gammaAut F) _ _)

theorem gammaPtLn_val (F : Type) [Field F] [CharP F 2] (x : ↥(Pt F)) :
    ((gammaPtLn F x : ↥(Ln F)) : projectiveSL 3 F) = gammaAut F (x : projectiveSL 3 F) :=
  rfl

@[expose] noncomputable def gammaConjPt (F : Type) [Field F] [CharP F 2] (a : MulAut ↥(Ln F)) :
    MulAut ↥(Pt F) :=
  (gammaPtLn F).trans (a.trans (gammaPtLn F).symm)

theorem gammaConjPt_val (F : Type) [Field F] [CharP F 2] (a : MulAut ↥(Ln F)) (x : ↥(Pt F)) :
    ((gammaConjPt F a x : ↥(Pt F)) : projectiveSL 3 F) =
      gammaAut F ((a (gammaPtLn F x) : ↥(Ln F)) : projectiveSL 3 F) :=
  rfl

theorem witnessPt_of_witnessLn {F : Type} [Field F] [Finite F] [CharP F 2] (κ : F)
    (h : WitnessLn F κ) : WitnessPt F κ := by
  obtain ⟨a, ha1, ha2⟩ := h
  refine ⟨gammaConjPt F a, ?_, ?_⟩
  ·
    intro m
    rw [gammaConjPt_val]
    have h1 := ha1 (gammaPtLn F m)
    rw [gammaPtLn_val] at h1
    exact (gammaAut_mem_Ln_iff F).trans (h1.trans (gammaAut_mem_Pt_iff F))
  ·
    intro b m hmb
    have hn : ((gammaPtLn F m : ↥(Ln F)) : projectiveSL 3 F) =
        ((gammaB F b : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) := by
      rw [gammaPtLn_val, gammaB_val, hmb]
    have h2 := ha2 (gammaB F b) (gammaPtLn F m) hn
    rw [gammaConjPt_val, h2, ← gammaB_val, gammaB_conj_nuMap]

end CFSG.GH74.QTGen4.DSGen4.L34

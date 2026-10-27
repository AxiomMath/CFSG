module

public import CFSG.HardMathSupport.Foote.E27.LieThree.MatTableP
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Foote.E27.LieTwo.SpData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix TauCeti CFSG.Assembly.LowTwoRank CFSG.Sporadic.He.Native

abbrev SpJP (p r : ℕ) : Type := ↥(GLSymplecticFin r (ZMod p))

@[expose] noncomputable def matJP (p r : ℕ) : SpJP p r →* MP p (r + r) :=
  (Units.coeHom _).comp (GLSymplecticFin r (ZMod p)).subtype

theorem matJP_injective (p r : ℕ) : Function.Injective (matJP p r) := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem exists_of_symplP {p r : ℕ} {M : MP p (r + r)}
    (h : Mᵀ * JFin r (ZMod p) * M = JFin r (ZMod p)) : ∃ x : SpJP p r, matJP p r x = M := by
  have hJ : JFin r (ZMod p) * JFin r (ZMod p) = -1 := JFin_mul_self r (ZMod p)
  have hJ' : JFin r (ZMod p) * (-JFin r (ZMod p)) = 1 := by
    calc JFin r (ZMod p) * (-JFin r (ZMod p)) = -(JFin r (ZMod p) * JFin r (ZMod p)) :=
          Matrix.mul_neg _ _
      _ = 1 := by rw [hJ]; exact neg_neg _
  set N : MP p (r + r) := (-JFin r (ZMod p)) * Mᵀ * JFin r (ZMod p) with hN
  have hNM : N * M = 1 := by
    have h1 : N * M = (-JFin r (ZMod p)) * (Mᵀ * JFin r (ZMod p) * M) := by
      rw [hN, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [h1, h]
    calc (-JFin r (ZMod p)) * JFin r (ZMod p) = -(JFin r (ZMod p) * JFin r (ZMod p)) :=
          Matrix.neg_mul _ _
      _ = 1 := by rw [hJ]; exact neg_neg _
  have hMN : M * N = 1 := mul_eq_one_comm.mpr hNM
  refine ⟨⟨⟨M, N, hMN, hNM⟩, ?_⟩, rfl⟩
  rw [GLSymplecticFin.mem_iff']
  exact h

theorem toMat_trA' (p d : ℕ) (X : AM) : toMat p d (trA d X) = (toMat p d X)ᵀ := by
  ext i j
  rw [toMat_apply, Matrix.transpose_apply, toMat_apply]
  unfold trA
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt]

end CFSG.HardMathSupport.Foote.E27

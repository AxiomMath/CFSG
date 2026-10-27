module

public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4ECent
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

namespace Sp48

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E

variable {K : Type} [Field K] [CharP K 2]

theorem planeMat_pair_mul2 (A B C D : Matrix (Fin 2) (Fin 2) K) :
    planeMat ![A, B] * planeMat ![C, D] = planeMat ![A * C, B * D] := by
  rw [planeMat_mul]
  congr 1
  funext k
  fin_cases k <;> simp

theorem planeMat_one_one : planeMat ![(1 : Matrix (Fin 2) (Fin 2) K), 1] = 1 := by
  rw [planeMat_one]
  congr 1
  funext k
  fin_cases k <;> rfl

@[expose] noncomputable def psiU (p : GL (Fin 2) K × GL (Fin 2) K) : GL Ix K :=
  ⟨planeMat ![(p.1 : Matrix (Fin 2) (Fin 2) K), p.2],
    planeMat ![((p.1⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), ((p.2⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)],
    by rw [planeMat_pair_mul2, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, mul_inv_cancel,
      Units.val_one, planeMat_one_one],
    by rw [planeMat_pair_mul2, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, inv_mul_cancel,
      Units.val_one, planeMat_one_one]⟩

@[expose] noncomputable def psi : GL (Fin 2) K × GL (Fin 2) K →* GL Ix K where
  toFun := psiU
  map_one' := Units.ext (by
    show planeMat ![((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
      ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)] = 1
    rw [Units.val_one, planeMat_one_one])
  map_mul' p q := Units.ext (by
    show planeMat ![((p.1 * q.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
      ((p.2 * q.2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)] =
      planeMat ![(p.1 : Matrix (Fin 2) (Fin 2) K), p.2] *
        planeMat ![(q.1 : Matrix (Fin 2) (Fin 2) K), q.2]
    rw [planeMat_pair_mul2, Units.val_mul, Units.val_mul])

theorem psi_val (p : GL (Fin 2) K × GL (Fin 2) K) :
    ((psi p : GL Ix K) : Matrix Ix Ix K) = planeMat ![(p.1 : Matrix (Fin 2) (Fin 2) K), p.2] :=
  rfl

theorem psi_injective : Function.Injective (psi (K := K)) := by
  intro p q h
  have h' : planeMat ![(p.1 : Matrix (Fin 2) (Fin 2) K), p.2] =
      planeMat ![(q.1 : Matrix (Fin 2) (Fin 2) K), q.2] := by
    rw [← psi_val, ← psi_val, h]
  have hX := planeMat_inj h'
  have h0 := congrFun hX 0
  have h1 := congrFun hX 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

theorem psi_mem {p : GL (Fin 2) K × GL (Fin 2) K} (h1 : (p.1 : Matrix (Fin 2) (Fin 2) K).det = 1)
    (h2 : (p.2 : Matrix (Fin 2) (Fin 2) K).det = 1) : psi p ∈ StatedSp 2 K := by
  rw [mem_statedSp_iff]
  show (planeMat ![(p.1 : Matrix (Fin 2) (Fin 2) K), p.2])ᵀ * JJ K *
    planeMat ![(p.1 : Matrix (Fin 2) (Fin 2) K), p.2] = JJ K
  rw [planeMat_symp_iff]
  intro k
  fin_cases k
  · exact (J2_symp_iff _).2 h1
  · exact (J2_symp_iff _).2 h2

@[expose] def wmat : Matrix Ix Ix K :=
  Matrix.of fun a b => if plane a ≠ plane b ∧ pos a = pos b then 1 else 0

theorem wmat_mul_self : wmat * wmat = (1 : Matrix Ix Ix K) := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [wmat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, plane, pos,
      Matrix.one_apply]

theorem wmat_conj (X Y : Matrix (Fin 2) (Fin 2) K) :
    wmat * planeMat ![X, Y] * wmat = planeMat ![Y, X] := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [wmat, planeMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, plane, pos]

theorem wmat_symp : wmatᵀ * JJ K * wmat = JJ K := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [wmat, JJ, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, plane, pos,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

@[expose] def wU : GL Ix K := ⟨wmat, wmat, wmat_mul_self, wmat_mul_self⟩

theorem wU_mem : wU ∈ StatedSp 2 K := by
  rw [mem_statedSp_iff]
  exact wmat_symp

theorem wU_conj (p : GL (Fin 2) K × GL (Fin 2) K) : wU * psi p * wU⁻¹ = psi (p.2, p.1) :=
  Units.ext (by
    show wmat * planeMat ![(p.1 : Matrix (Fin 2) (Fin 2) K), p.2] * wmat =
      planeMat ![(p.2 : Matrix (Fin 2) (Fin 2) K), p.1]
    exact wmat_conj _ _)

end Sp48

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC

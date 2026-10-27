module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafODiag
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOXpc
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Orth516

open Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C (sq_eq_scalar_of_orderOf det_eq_one_of_mem_commutator)

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem false_of_model_conf
    (hK : ringChar K ≠ 2) {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hKc : Nat.card K = p ^ e)
    (hd : 7 ≤ d) {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (hker : OKer (oQ R)) {g : similarityPairs (oQ R)}
    {P J : Subgroup (StatedProj (matrixDerived (oQ R)))} {x : StatedProj (matrixDerived (oQ R))}
    (h : LeafConf (oκ _ g) P x J) (hPq : IsQuasisimple P) {f : ℕ} (hf : 1 ≤ f)
    (hPm : L4U4Type P p f) : False := by
  obtain ⟨A, rfl⟩ := projH_surjective x
  rcases sq_eq_scalar_of_orderOf hK hR (by omega) h.x2 with hA2 | hA2
  ·
    obtain ⟨w, hw, S, hS, J₂, hJ₂, hxJ, hNF, hNFc⟩ := exists_sign_frame hK hR hA2
    have h' := h.map (oTransport S 1 hS)
    rw [oTransport_kappa, hxJ] at h'
    have hPq' : IsQuasisimple (P.map (oTransport S 1 hS).toMonoidHom) :=
      LocalCores.isQuasisimple_of_mulEquiv
        (P.equivMapOfInjective (oTransport S 1 hS).toMonoidHom (oTransport S 1 hS).injective) hPq
    have hPm' : L4U4Type (P.map (oTransport S 1 hS).toMonoidHom) p f :=
      hPm.of_mulEquiv
        (P.equivMapOfInjective (oTransport S 1 hS).toMonoidHom (oTransport S 1 hS).injective).symm
    exact false_of_diag_conf hw hK hp he hKc hd (hker.transport S 1 hS) hJ₂ hNF hNFc h' hPq' hf
      hPm'
  ·
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | hodd
    · obtain rfl : d = 2 * m := by omega
      exact false_of_x_pc hK hp hKc (by omega) hR hA2 h.JC h.Jc h.J8
    · have hdet := det_eq_one_of_mem_commutator (H := matrixIsometries (oQ R)) A.2
      have h1 := congrArg Matrix.det hA2
      rw [Matrix.det_mul, hdet, mul_one, Matrix.det_neg, Matrix.det_one, mul_one,
        Fintype.card_fin, hodd.neg_one_pow] at h1
      exact Ring.two_ne_zero hK (by linear_combination h1)

end CFSG.ComponentClassification.GSThmB.Orth516

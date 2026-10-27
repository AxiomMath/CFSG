module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Strong
public import Certificates.Certificate12604

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem jsOK_spec :
    fixDimOK jsJn.1 jsJP jsJPinv jsJR 62 = true ∧ fixDimOK jsSn.1 jsSP jsSPinv jsSR 56 = true := by
  have h : jsOK = true := Certificates.certificate12604
  unfold jsOK at h
  exact Bool.and_eq_true_iff.1 h

theorem fixDim_nrm₂_pow_twenty :
    fixDim (nrm₂ ^ 20) = 62 :=
  finrank_rowFix_of_ok (by norm_num) (rep_powP rep_nrm₂ 20).2.2.1 jsOK_spec.1

theorem fixDim_s :
    fixDim ((nrm₁ ^ 2 * nrm₂ ^ 5) ^ 11) = 56 :=
  finrank_rowFix_of_ok (by norm_num)
    (rep_powP (rep_mulP (rep_powP rep_nrm₁ 2) (rep_powP rep_nrm₂ 5)) 11).2.2.1 jsOK_spec.2

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

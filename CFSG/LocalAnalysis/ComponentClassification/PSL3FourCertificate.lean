
module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificateBase
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificateBase

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec
public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import Certificates.Certificate2022
public import Certificates.Certificate2022Base

public section

namespace CFSG.ComponentClassification.PSL3Four

open CFSG.PSL3Four CFSG.PSL3Four.Native

theorem certificate_eq_true : certificate 20160 241920 1963 = true :=
  Certificates.certificate2022

theorem certFacts : CertFacts := by
  have h := certificate_eq_true
  simp only [certificate, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩

end CFSG.ComponentClassification.PSL3Four

module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KBModel
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gSylModel
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Cert
public import Certificates.Certificate5250

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.ComponentClassification.PSL3Four in
theorem kb813_cent_fix :
    (∀ x ∈ R, x ≠ 1 → x ^ 3 = 1 → ∃ d ∈ C₁, d * x ≠ x * d) ∧
    (∀ y ∈ R, y ∉ S → y ^ 3 = 1 → r₄ * y = y * r₄ → ∃ d ∈ C₄, (y * (d * y * d⁻¹)) ^ 3 ≠ 1) :=
  Certificates.certificate5250

open CFSG.ComponentClassification.PSL3Four in
theorem kb813Model_thm :
    KB813Model := by
  obtain ⟨hcent, hfix⟩ := kb813_cent_fix
  obtain ⟨z, hz⟩ := l34Facts
  obtain ⟨P, E, F, hPS, -, hFP, -, -, -, hF16, -, -, -, -, -, -, -, hFcomm, hFsq, -⟩ :=
    P85.exists_sylCfg_model
  exact ⟨⟨F, hFP.trans hPS, hF16, hFcomm, hFsq⟩, hcent, hz.exp27, hfix⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

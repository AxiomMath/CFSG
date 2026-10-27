module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXSound
public import Certificates.Certificate25295

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

theorem axSpec_data : axSpec axMs (fun k => axQs[k]!) := by
  have h := Certificates.certificate25295
  simp only [axCertificate, Bool.and_eq_true] at h
  exact axCheck_sound h.1

theorem axMs_parts :
    axMs.size = 2 ^ 8 ∧ (∀ k < axMs.size, ∀ c < 10, axMs[k]![c]! < 1024) ∧
      ∀ k < axMs.size, ∀ k' < axMs.size, fn axMs[k]! = fn axMs[k']! → k = k' := by
  have h := Certificates.certificate25295
  simp only [axCertificate, Bool.and_eq_true] at h
  exact axCheck_parts h.1

theorem axWords_data :
    (∀ k < axGc.size, ∀ c < 10, axGc[k]![c]! < 1024) ∧ axWs.size = axMs.size ∧
      ∀ j < axMs.size, (∀ k ∈ axWs[j]!, k < axGc.size) ∧
        (∀ i < 10, (axWordCols axGc axWs[j]!)[i]! = axMs[j]![i]!) ∧
        (axQs[j]! = true → ∀ k ∈ axWs[j]!, k < 9) := by
  have h := Certificates.certificate25295
  simp only [axCertificate, Bool.and_eq_true] at h
  exact axWordsOK_spec h.2

end CFSG.EvenSporadicStandard.TwoFi22.DS81

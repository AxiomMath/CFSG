module

public import Certificates.Certificate3372

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model


theorem chainCheck_plus : chainCheck .plus = true := Certificates.certificate3372.1

theorem chainCheck_minus : chainCheck .minus = true := Certificates.certificate3372.2.1

theorem basicCheck_plus : basicCheck .plus = true := Certificates.certificate3372.2.2.1

theorem basicCheck_minus : basicCheck .minus = true :=
  Certificates.certificate3372.2.2.2.1

theorem exists_oSet (ε : Eps) :
    ∃ T, oSetCheckW ε T = true ∧ (ε = .plus → r3CheckW T = true) := by
  cases ε
  · obtain ⟨T, h1, h2⟩ := Certificates.certificate3372.2.2.2.2.1
    exact ⟨T, h1, fun _ => h2⟩
  · obtain ⟨T, h1⟩ := Certificates.certificate3372.2.2.2.2.2.1
    exact ⟨T, h1, fun h => by cases h⟩

theorem exists_s5 (ε : Eps) : ∃ S D, s5CheckW ε S D = true := by
  cases ε
  · exact Certificates.certificate3372.2.2.2.2.2.2.1
  · exact Certificates.certificate3372.2.2.2.2.2.2.2

noncomputable def oOrbitW (ε : Eps) : Array (Array ℕ) := Classical.choose (exists_oSet ε)

noncomputable def uListW (ε : Eps) : Array (Array ℕ) := Classical.choose (exists_s5 ε)

noncomputable def uClsW (ε : Eps) : UCls := Classical.choose (Classical.choose_spec (exists_s5 ε))

@[expose] noncomputable def oMasksW : Array (Array Bool) := (oOrbitW .plus).map (maskOf .plus)

theorem r3CheckW_oOrbitW :r3CheckW (oOrbitW .plus) = true :=
  (Classical.choose_spec (exists_oSet .plus)).2 rfl

theorem modelChecks (ε : Eps) : chainCheck ε = true ∧ basicCheck ε = true ∧
    oSetCheckW ε (oOrbitW ε) = true ∧ s5CheckW ε (uListW ε) (uClsW ε) = true := by
  refine ⟨?_, ?_, (Classical.choose_spec (exists_oSet ε)).1,
    Classical.choose_spec (Classical.choose_spec (exists_s5 ε))⟩
  · cases ε
    · exact chainCheck_plus
    · exact chainCheck_minus
  · cases ε
    · exact basicCheck_plus
    · exact basicCheck_minus

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model

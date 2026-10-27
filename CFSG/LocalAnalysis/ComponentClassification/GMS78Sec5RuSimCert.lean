module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSimCode
public import Certificates.Certificate15092

public section

namespace CFSG.ComponentClassification.GMS78

open CFSG.GMS78Ru CFSG.GMS78RuSim

theorem ruSim0_check : s0Check = true :=
  Certificates.certificate15092.1

theorem ruSim1_check : s1Check = true :=
  Certificates.certificate15092.2.1

theorem ruSim2a_check : s2aCheck = true :=
  Certificates.certificate15092.2.2.1

theorem ruSim2b_check : s2bCheck = true :=
  Certificates.certificate15092.2.2.2

namespace RuSimCode

theorem sqN_nMap {d : SData} (hd : d ∈ steinData) {r : Lin8}
    (hr : r ∈ glList) {w : V3} (hw : w ∈ wList d.1.2.2.1 d.1.2.2.2) :
    sqN d.1.1 d.1.2.1 (nMap d r w) = linApply r (sqN d.1.1 d.1.2.1 w) := by
  have h := ruSim1_check
  simp only [s1Check, List.all_eq_true, beq_iff_eq] at h
  exact h d hd r hr w hw

theorem card_fix_le_four {r₁ r₂ : Lin8} (h₁ : r₁ ∈ invList)
    (h₂ : r₂ ∈ invList) (hne : r₁ ≠ r₂) (hc : linComp r₁ r₂ = linComp r₂ r₁) :
    (all256.filter fun m => maskApply (adMat r₁) m == m && maskApply (adMat r₂) m == m).length ≤
      4 := by
  have h := ruSim2a_check
  simp only [s2aCheck, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  rcases h r₁ h₁ r₂ h₂ with (h | h) | h
  · exact absurd h hne
  · exact absurd hc h
  · exact h

theorem mem_of_commute_four {r₁ r₂ : Lin8} (h₁ : r₁ ∈ invList)
    (h₂ : r₂ ∈ invList) (hne : r₁ ≠ r₂) (hc : linComp r₁ r₂ = linComp r₂ r₁) {r : Lin8}
    (hr : r ∈ glList) (hr₁ : linComp r r₁ = linComp r₁ r) (hr₂ : linComp r r₂ = linComp r₂ r) :
    r ∈ [linId, r₁, r₂, linComp r₁ r₂] := by
  have h := ruSim2b_check
  simp only [s2bCheck, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.contains_iff_mem] at h
  rcases h r₁ h₁ r₂ h₂ with (h | h) | h
  · exact absurd h hne
  · exact absurd hc h
  · rcases h r hr with (h' | h') | h'
    · exact absurd hr₁ h'
    · exact absurd hr₂ h'
    · exact h'

end RuSimCode

end CFSG.ComponentClassification.GMS78

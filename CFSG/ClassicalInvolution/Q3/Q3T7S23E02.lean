module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23E01
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Chain
public import CFSG.ClassicalInvolution.Q3.Q3T7S23H3
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Y06

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open CFSG.ClassicalInvolution.Asc77.B3C (SymplecticPhanPair)


section Assembly


theorem b3Chain23_of_yside
    (hO : OddCoreLayer23Neg3) (hOY : OddCoreLayer23Sp3) : B3Chain23 := by
  intro G _ _ _ Ω K K' W z u e g h hα hE hY5
  have hs : Q3T8.Asc77.Hyp23Setting Ω K K' z := Q3T8.Asc77.Hyp23.setting h.std
  have hd : Hyp23bData Ω K K' W z u e g := Q3T8.Asc77.Hyp23b.data h
  have hπ : piSign 3 1 = false := by decide
  have hE0 : Q3T8.Asc77.LayerOrthType Ω e 6 false := by simpa [hπ] using hE
  have hOE : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω e) = ⊥ :=
    hO G Ω K K' W z u e g h hα hE
  obtain ⟨hex, hpJ, hpJ', hgenE, hKE, hJE, hJ'E, hJJ'⟩ :=
    Q3T8.Asc77.B3C.eSideU3 hs hd hα.1 hOE hE0
  obtain ⟨J₁, K₃, htwin, hSp, -, -, hcommK, hgenY, ⟨hJY, hJ'Y⟩, w, hwK₃, hw1, hw2⟩ :=
    ySide_fields3 hs hd hex (hOY G Ω K K' W z u e g h hα hE hY5 hex hOE) hY5
  set E := Q3T8.Asc77.ExactLayer.exactLayer Ω e with hEdef
  set Y := Q3T8.Asc77.ExactLayer.exactLayer Ω u with hYdef
  have key : ∃ J₁' : Subgroup G, (∃ W', UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W' K J₁) ∧
      conjSub w J₁ = J₁' ∧ Commutes J₁ J₁' ∧ J₁ ≤ E ∧ J₁' ≤ E ∧ J₁ ≤ Y ∧ J₁' ≤ Y ∧
      E ≤ (K ⊔ J₁ ⊔ J₁') := by
    rcases htwin with h1 | h1
    · refine ⟨conjSub g K', hpJ.imp fun W' h => by rw [h1]; exact h, hw1 h1, ?_, ?_, hJ'E, ?_,
        hJ'Y, ?_⟩
      · rw [h1]; exact hJJ'
      · rw [h1]; exact hJE
      · rw [h1]; exact hJY
      · rw [h1]
        calc E ≤ conjSub g K' ⊔ K ⊔ conjSub g K := hgenE
          _ = K ⊔ conjSub g K ⊔ conjSub g K' := by ac_rfl
    · refine ⟨conjSub g K, hpJ'.imp fun W' h => by rw [h1]; exact h, hw2 h1, ?_, ?_, hJE, ?_,
        hJY, ?_⟩
      · rw [h1]; exact fun x hx y hy => (hJJ' y hy x hx).symm
      · rw [h1]; exact hJ'E
      · rw [h1]; exact hJ'Y
      · rw [h1]
        calc E ≤ conjSub g K' ⊔ K ⊔ conjSub g K := hgenE
          _ = K ⊔ conjSub g K' ⊔ conjSub g K := by ac_rfl
  obtain ⟨J₁', hpair, hconj, hcomm, hJ₁E, hJ₁'E, hJ₁Y, hJ₁'Y, hgen⟩ := key
  refine ⟨![K, J₁, K₃], hs.stand.mem, hcommK, hpair, ⟨_, hSp⟩, ?_, ?_⟩
  ·
    have hsup : (⨆ k, (![K, J₁, K₃] : Fin 3 → Subgroup G) k) = K ⊔ J₁ ⊔ K₃ := by
      refine le_antisymm (iSup_le fun k => ?_) (sup_le (sup_le ?_ ?_) ?_)
      · fin_cases k
        · exact le_sup_left.trans le_sup_left
        · exact le_sup_right.trans le_sup_left
        · exact le_sup_right
      · exact le_iSup (fun k => (![K, J₁, K₃] : Fin 3 → Subgroup G) k) 0
      · exact le_iSup (fun k => (![K, J₁, K₃] : Fin 3 → Subgroup G) k) 1
      · exact le_iSup (fun k => (![K, J₁, K₃] : Fin 3 → Subgroup G) k) 2
    have hYH : Y ≤ K ⊔ J₁ ⊔ K₃ :=
      hgenY.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    have hEH : E ≤ K ⊔ J₁ ⊔ K₃ :=
      hgen.trans (sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left))
        (hJ₁'Y.trans hYH))
    rw [hsup]
    refine eq_top_iff.mpr ?_
    rw [← hα.2]
    exact sup_le hEH hYH
  ·
    have hgen' : E ≤ (K ⊔ J₁ ⊔ J₁') ⊔ oddCoreOf E := hgen.trans le_sup_left
    obtain ⟨w', hw', hc', h3⟩ := phanH3_clause hwK₃ hconj hcomm hKE hJ₁E hJ₁'E hgen' hOE
    exact ⟨w', hw', hc', h3⟩

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3T7S23

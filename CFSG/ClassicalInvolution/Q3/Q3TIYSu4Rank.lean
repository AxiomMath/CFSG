module

public import CFSG.ClassicalInvolution.Q3.Q3TIYFinal
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk1
public import CFSG.ClassicalInvolution.Q3.Q3TIYSu4Model
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk2
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.RouteD.TWY CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal

@[expose] def TwinRowSU4 (t : StatedLieTag) (n : ℕ) : Prop := t = .PSU ∧ n = 4

theorem twinYModel3_psu4 : twinYModel 3 .PSU 4 = (.POmegaPlus, 4) := by
  simp [twinYModel]

theorem card_o4_eq_framesPlus3 :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      framesPlus 3 0 := by
  rw [card_o4 (GaloisField 3 1), Q3W.card_gf3]
  rfl

theorem twinRank3Model_psu4 : TwinRank3Model .PSU 4 := by
  intro R R' x x' ã ã' hd hãR hã'R hsq hsq' t' n' hrow hadm hnsmall R₀ hR₀ hcard
  have hY := card_fund_centralizing_psu4 hd hãR hã'R hsq hsq'
  have hO := card_o4_eq_framesPlus3
  rw [twinYModel3_psu4]
  rcases hrow with ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩ |
    ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩
  · obtain ⟨j, hj, hk⟩ := layerCount3_plus hadm hR₀ hcard
    rw [hY] at hk
    have hc : framesPlus 3 j = framesPlus 3 0 := by omega
    have hj0 : j = 0 := framesPlus_inj3 Nat.prime_three (by norm_num) le_rfl (by norm_num)
      (by norm_num) hc
    exact ⟨rfl, by show _ = 4; omega⟩
  · exact (hnsmall (Or.inr (Or.inl ⟨rfl, rfl⟩))).elim
  · obtain ⟨j, -, hk⟩ := layerCount3_odd hadm hR₀ hcard
    rw [hY] at hk
    have hc : cOdd 3 j = framesPlus 3 0 := by omega
    rcases j with _ | j
    · exact (framesPlus_ne_zero (q := 3) (by norm_num) 0 (by rw [← hc]; rfl)).elim
    · exact (framesOdd_ne_framesPlus3 Nat.prime_three (by norm_num) le_rfl (by norm_num)
        (by norm_num) j 0 hc).elim
  · exact (hnsmall (Or.inl ⟨rfl, rfl⟩)).elim
  · obtain ⟨j, -, hk⟩ := layerCount3_minus hadm hR₀ hcard
    rw [hY] at hk
    have hc : cMinus 3 j = framesPlus 3 0 := by omega
    rcases j with _ | j
    · exact (framesPlus_ne_zero (q := 3) (by norm_num) 0 (by rw [← hc]; rfl)).elim
    · exact (framesPlus_ne_framesMinus3 Nat.prime_three (by norm_num) le_rfl (by norm_num)
        (by norm_num) 0 j hc.symm).elim
  · exact (hnsmall (Or.inr (Or.inr ⟨rfl, rfl⟩))).elim

theorem twinYKind3_su4 : TwinYKind3On TwinRowSU4 :=
  Q3TIV.twinYKind3_of_model fun t n _ hP => by
    obtain ⟨rfl, rfl⟩ := hP
    exact twinCentralizingNe3_psu4

theorem twinYRank3_su4 : TwinYRank3On TwinRowSU4 :=
  Q3TIV.twinYRank3_of_model
    (fun t n _ hP => by
      obtain ⟨rfl, rfl⟩ := hP
      exact twinRank3Model_psu4)
    (fun t n _ hP => by
      obtain ⟨rfl, rfl⟩ := hP
      exact twinCentralizingNe3_psu4)
    smallNoThree3

theorem twinYType3On_su4_of_noCentral (h3 : OddThreeFreeInput)
    (hNC : TwinYNoCentral3On TwinRowSU4) : Q3TY.TwinYType3On TwinRowSU4 :=
  twinYType3On_of_inputs h3 hNC twinYKind3_su4 twinYRank3_su4

end CFSG.ClassicalInvolution.Q3.Q3TIY

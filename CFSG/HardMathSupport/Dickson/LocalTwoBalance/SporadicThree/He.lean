module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6Red
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.HeAux.Kit
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.HeAux.ThreeCheck
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.HeAux.Outer
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.HeAux.Delta
public import CFSG.Sporadic.Bridge.HeSurj

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.HardMathSupport.Solomon.Coordinator


theorem sporadicTwoBalanceThree_He : SporadicTwoBalanceThree .He := by
  intro S _ _ hS hnab he
  obtain ⟨e0⟩ := he
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  haveI := hS
  let θ : S ≃* ↥CFSG.Sporadic.HeldB.heP :=
    (e0.trans b.symm).trans CFSG.Sporadic.HeldB.heEquivP
  have hcen : Subgroup.center S = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · obtain ⟨a, c, hac⟩ := hnab
      exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top c)) a) hac
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2 := by
    obtain ⟨-, -, -, -, hO2, -⟩ := CFSG.Sporadic.HeldB.ctbh_full_automorphism_permutation_model
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence θ).toEquiv,
      hO2]
  have hA := HeAux.heS3_centralizers
  exact HeAux.isLocallyBalancedAbs_two_of_autModel_planes Nat.prime_three (by norm_num)
    CFSG.RankThree.PartOne.heAutModel θ hcen hout
    fun E hEP hE hEc H' hPH hHR y hy =>
      HeAux.he_delta_trivial (fun x hx ho => (hA x hx ho).1)
        (fun d hd ho hc => HeAux.heOuterD_central_of_centralizer_le hd ho (hA d hd ho).2 hc)
        E hEP hE hEc H' hPH hHR y hy

end CFSG.HardMathSupport.Dickson.LocalTwoBalance

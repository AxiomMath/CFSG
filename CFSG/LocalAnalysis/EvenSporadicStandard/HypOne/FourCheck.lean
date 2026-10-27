module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.EvenSporadicStandard.HypOne

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover

@[expose] def fourCheck (n : ℕ) (Q : RawSchreierDatum n) (gs : List (Equiv.Perm (Fin n)))
    (words : List (List ℤ)) (cap : ℕ) : Bool :=
  repsOK n (listTables gs) (listTables (gs.map (·⁻¹))) (cosetOrderTables Q 1 4)
      ((words.map (evalCodes gs)).map toTable) cap &&
    (repSizes n (listTables gs) (listTables (gs.map (·⁻¹)))
      ((words.map (evalCodes gs)).map toTable) cap).all (fun k => decide (5 ≤ k)) &&
    ((words.map (evalCodes gs)).map toTable).all (ordTest n 4)

theorem fourClassesLarge_of_fourCheck {n : ℕ} (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) (gs : List (Equiv.Perm (Fin n)))
    (hgs : ∀ g ∈ gs, g ∈ Q.originalSubgroup) (words : List (List ℤ)) (cap : ℕ)
    (h : fourCheck n Q gs words cap = true) : FourClassesLarge Q.originalSubgroup := by
  simp only [fourCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hok, hsz⟩, h4⟩ := h
  refine fourClassesLarge_of_repsOK hn Q hQ gs hgs (words.map (evalCodes gs))
    (fun r hr => ⟨?_, ?_⟩) cap hok fun r hr => ?_
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    exact evalCodes_mem _ hgs w
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 h4 _ (List.mem_map_of_mem hr))
  · exact of_decide_eq_true (List.all_eq_true.1 hsz _
      (List.mem_map_of_mem (List.mem_map_of_mem hr)))

end CFSG.EvenSporadicStandard.HypOne

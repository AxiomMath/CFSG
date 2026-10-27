module

public import CFSG.GF2Type.Aschbacher1976Full.Defs
public import CFSG.GF2Type.Aschbacher1976

public section

namespace CFSG.GF2Type.Aschbacher1976Full

open CFSG CFSG.Blueprint

theorem aschbacher1976Statement_of_inputs (I : Asc76Inputs) : Aschbacher1976Statement := by
  intro G _ _ hsimp hnab z hz hsymp
  have hS : Asc76Setting G z := ⟨hsimp, hnab, hz, hsymp⟩
  rcases I.shape G z hS with ⟨w, hw, hext, hcard⟩ | ⟨n, hn, hH, he⟩ | ⟨n, hn, hH, he⟩ | he |
      ⟨hH, hU⟩ | hB | ⟨w, hw, hZ⟩
  · exact Or.inr (Or.inr (Or.inr ⟨hext, w, hw, hcard⟩))
  · exact Or.inl (I.dihedral G z hS n hn hH he)
  · exact (I.semidihedral G z hS n hn hH he).elim
  · exact Or.inr (Or.inl ((I.q8 G z hS he).elim Or.inl (fun h => Or.inr (Or.inl h))))
  · exact (I.uniqueInvolution G z hS hH hU).elim
  · exact (I.bigCenter G z hS hB).elim
  · rcases Nat.lt_or_ge w 3 with hw3 | hw3
    · interval_cases w
      · exact Or.inr (Or.inl (Or.inr (Or.inr (I.z4q8 G z hS hZ))))
      · exact Or.inr (Or.inr (Or.inl (I.z4q8sq G z hS hZ)))
    · exact (I.widthGeThree G z hS w hw3 hZ).elim

end CFSG.GF2Type.Aschbacher1976Full

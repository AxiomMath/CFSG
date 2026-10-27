module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CentTriv

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

theorem centTrivOK_mono {n : Nat} {s s' : CFSG.Sporadic.Th.Native.Table → Bool}
    {hs : List (CFSG.Sporadic.Th.Native.Table × CFSG.Sporadic.Th.Native.Table)}
    (hss : ∀ T, s T = true → s' T = true) (h : centTrivOK n s hs = true) :
    centTrivOK n s' hs = true := by
  simp only [centTrivOK, Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun i hi => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := h2 i hi
  exact ⟨⟨⟨⟨⟨⟨a1, a2⟩, hss _ a3⟩, hss _ a4⟩, a5⟩, a6⟩, a7⟩

end CFSG.ComponentClassification.HarrisLit.P1

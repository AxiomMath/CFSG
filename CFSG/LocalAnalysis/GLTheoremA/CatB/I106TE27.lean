module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TE27Small
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TE27J3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TE27L2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

theorem i106TE27Fact :
    I106TE27Fact := by
  intro i H _ _ hT hSp _ hZ ⟨φ⟩
  refine E27.E27Lifts.exists_of_quotient_center ?_ φ hZ
  cases i with
  | cyclic p hp => rcases hT with h | h | h <;> first | exact h.elim | cases h
  | alternating n hn =>
    rcases hT with h | h | h
    · have hn9 : n = 9 := h
      subst hn9
      exact E27.e27Lifts_alt9
    · cases h
    · exact h.elim
  | sporadic s =>
    rcases hT with h | h | h
    · exact h.elim
    · have hs : s = TauCeti.SporadicName.J3 := by injection h
      subst hs
      exact E27.e27Lifts_j3
    · exact h.elim
  | lie j =>
    rcases hT with h | h | h
    · cases h
    · cases h
    · rcases j with ⟨d, hv⟩
      cases d with
      | B n q =>
        rcases n with _ | _ | _ | _ | n
        · exact h.elim
        · exact h.elim
        · exact (hSp h).elim
        · obtain ⟨e⟩ := CatB.bridge_sp6two (S := (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group)
            ⟨.lie ⟨.B 3 q, hv⟩, show q.card = 2 from h, ⟨MulEquiv.refl _⟩⟩
          exact E27.E27Lifts.of_mulEquiv (G := CFSG.Open.StatedSp 3 (ZMod 2))
            (G' := (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group) e.symm E27.e27Lifts_sp62
        · exact h.elim
      | A n q =>
        rcases n with _ | _ | n
        · exact h.elim
        · exact E27.e27Lifts_l2_729 q hv h
        · exact h.elim
      | _ => exact h.elim

end CFSG.LocalAnalysis.GLTheoremA.S8.L84

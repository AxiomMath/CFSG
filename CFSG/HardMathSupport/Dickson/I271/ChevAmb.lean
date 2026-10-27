module

public import CFSG.HardMathSupport.Dickson.I271.Support.OuterDefs
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbAlt
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbL2
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbU4

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

theorem chevAmbCase_holds :
    ChevAmbCase := by
  intro X _ _ p K B hH hamb hne
  obtain ⟨i, hi, ⟨e⟩⟩ := hamb
  cases i with
  | cyclic r hr => simp [ambiguousChev] at hi
  | alternating n hn =>
    simp only [ambiguousChev] at hi
    rcases hi with ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩ | ⟨rfl, h⟩
    · exact absurd h hH.odd
    · subst h
      exact Amb.altCore hH.prime hH.odd hH.core hH.comp hH.scp hH.norm (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) e
    · exact absurd h hH.odd
    · subst h
      rcases Amb.a6Case hH.core hH.comp hH.scp hH.norm e with h | ⟨hat, hcard⟩
      · exact h
      · exact absurd ⟨rfl, Or.inr ⟨hat, hcard⟩⟩ hne
    · exact absurd h hH.odd
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    cases ld
    case A r q =>
      rcases r with _ | _ | r
      · simp [ambiguousChev] at hi
      · simp only [ambiguousChev] at hi
        rcases hi with ⟨-, h2⟩ | ⟨hq8, h3⟩
        · exact absurd h2 hH.odd
        · subst h3
          haveI : Fact q.p.Prime := ⟨q.prime_p⟩
          have hF8 : Nat.card (GaloisField q.p q.exponent) = 8 := by
            rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
            exact hq8
          exact Amb.l2EightCase hH.core hH.comp hH.scp hH.norm hF8
            (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv))
      · simp [ambiguousChev] at hi
    case twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · simp [ambiguousChev] at hi
      · simp [ambiguousChev] at hi
      · simp only [ambiguousChev] at hi
        exact absurd hi.2 hH.odd
      · simp only [ambiguousChev] at hi
        obtain ⟨hq2, h3⟩ := hi
        subst h3
        exact Amb.u4Case hq2 hH.core hH.comp hH.scp hH.norm e
      · simp [ambiguousChev] at hi
    all_goals simp [ambiguousChev] at hi
  | sporadic s => simp [ambiguousChev] at hi

end CFSG.HardMathSupport.Dickson.I271

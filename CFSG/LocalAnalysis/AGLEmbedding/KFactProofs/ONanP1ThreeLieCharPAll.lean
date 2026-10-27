module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieCharP
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieBD
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieExc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenG23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenO73
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenU43
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeOut
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.AGLEmbedding.KFactProofs.ThreeWeak (weakGenG23 weakGenO73 weakGenU43)

theorem exists_weak_family_of_odd {d : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp2 : p ≠ 2)
    (hchar : p = d.1.characteristic) (hrank : ¬ IsRankOneLieIndex d.1) (hB2 : ¬ IsSpFourIndex p d)
    (hL3 : ¬ ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 2 q) :
    IsWeakSLIndex d ∨ IsWeakSpIndex d ∨ IsSUIndex d ∨ IsBOddIndex d ∨ IsDIndex d ∨
      IsTwistedDIndex d ∨ IsExceptionalIndex d := by
  rcases exists_family_of_odd hp2 hchar hrank with ⟨r, q, hr, hd⟩ |
    (⟨q, hd⟩ | ⟨r, q, hr, hd⟩) | h | h | h | h | h
  · refine Or.inl ⟨r, q, hr, hd, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hr3, hq2⟩ := hcon
    have hr2 : r = 2 := by omega
    have hq1 : q.exponent = 1 := by
      have := q.exponent_pos
      omega
    have hqp : q.p = p := by
      rw [hd] at hchar
      simpa using hchar.symm
    subst hr2
    exact hL3 ⟨q, hqp, hq1, hd⟩
  · refine Or.inr (Or.inl (Or.inl ⟨q, ?_, hd⟩))
    by_contra hcon
    have hq1 : q.exponent = 1 := by
      have := q.exponent_pos
      omega
    have hqp : q.p = p := by
      rw [hd] at hchar
      simpa using hchar.symm
    exact hB2 ⟨q, Or.inl ⟨hqp, hq1, hd⟩⟩
  · exact Or.inr (Or.inl (Or.inr ⟨r, q, hr, hd⟩))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

section Certified

theorem p1ThreeLieCharP_of_griess (hGA : GriessMultipliersAllModels) : P1ThreeLieCharP :=
  p1ThreeLieCharP_of_weak
    (Fam := fun d => IsWeakSLIndex d ∨ IsWeakSpIndex d ∨ IsSUIndex d ∨ IsBOddIndex d ∨
      IsDIndex d ∨ IsTwistedDIndex d ∨ IsExceptionalIndex d)
    (weakCharPGenAt_or weakCharPGenAt_sl (weakCharPGenAt_or weakCharPGenAt_sp
      (weakCharPGenAt_or weakCharPGenAt_su (weakCharPGenAt_or weakCharPGenAt_bOdd
        (weakCharPGenAt_or weakCharPGenAt_d (weakCharPGenAt_or weakCharPGenAt_twistedD
          weakCharPGenAt_exceptional))))))
    (fun _ _ _ hp2 hchar hrank hB2 hL3 => exists_weak_family_of_odd hp2 hchar hrank hB2 hL3)
    hGA weakGenU43 weakGenO73 weakGenG23 AGLEmbeddingD2.kFactLieCharOut

end Certified

section CertifiedAll

theorem p1ThreeLieCharP : P1ThreeLieCharP :=
  p1ThreeLieCharP_of_griess CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

theorem kFactP1ThreeLie_of_charP_offChar (hoff : P1ThreeLieOffChar) : KFactP1ThreeLie :=
  kFactP1ThreeLie_of_families p1ThreeLieCharP hoff

end CertifiedAll

end CFSG.AGLEmbedding

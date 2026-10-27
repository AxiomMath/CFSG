module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCatSimple
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCatHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCyclic

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem l34CyclicProperFixedCatalog_of_inputs
    (hcomp : ∀ s : TauCeti.SporadicName, s ≠ .J1 → s ≠ .J2 → s ≠ .J3 → s ≠ .M12 → s ≠ .HS →
      s ≠ .He → s ≠ .Suz → s ≠ .ONan → HarrisLit.SporCompData s) :
    L34CyclicProperFixedCatalog := by
  intro Q _ _ hQ hZ hcat σ hσ P hPF hP hPne htype hrank
  have : IsSimpleGroup (Q ⧸ center Q) := hQ.2.1
  obtain ⟨σ', P', h', htype'⟩ := L34R.exists_properFixedComponent hQ hZ hσ hPF hP hPne htype
  rcases cat_of_simple hcomp hQ.2.2 hcat h' htype' with hH | hS | hON | hL
  · exfalso
    obtain ⟨eH⟩ := hH
    have hZ1 : center Q = ⊥ :=
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate Q hQ ⟨eH⟩
    have : IsSimpleGroup Q := UnbalancedCorr.isSimpleGroup_of_isQuasisimple_of_center_eq_bot hQ hZ1
    have eQ : Q ≃* NativeSporadic.He :=
      ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm.trans eH
    have h2 := two_le_pRank_of_he eQ ⟨hσ, hPF, hP, hPne⟩ htype
    omega
  · exact Or.inl hS
  · exact Or.inr (Or.inl hON)
  · exact Or.inr (Or.inr hL)

end CFSG.ComponentClassification.GrSLit.L34Sec5S

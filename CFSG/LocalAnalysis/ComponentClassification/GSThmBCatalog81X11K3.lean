module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11K2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11R
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3f

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem concl81_of_isKGroupCat {v : H} (h11 : GS81Step11Input)
    (hrec : CF81Exit11Recognition) (hRS : RestrictedStandardInput) (I : In81)
    (hst : d.Stage7 v) (hKG : SectionRank.IsKGroupCat H)
    (hLB : Assembly.ComponentType.LocalBProperty H)
    (hJ : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2)
    (hK : Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 3 1) : h.Concl81 := by
  obtain ⟨w, hwU, hwS, hSw⟩ := h11 H h H₁ d v hst hJ hK
  obtain ⟨N, hN, hNc, -, hNa⟩ := exists_normal_asigma hst.isV I hst hJ hwU hwS hSw
  exact hrec H h H₁ d v hst (gsRestricted_components I hst hNc hNa hRS hKG hLB hJ) hJ hK

end Data

end L81Hyp

end Hyp59

theorem gs81Exit11Input_of'
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (h11 : GS81Step11Input) (hrec : CF81Exit11Recognition) :
    In81 → RestrictedStandardInput →
      ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data) (v : H),
        d.Stage7 v → Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2 →
          Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 3 1 →
          layerIn (centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H)) = ⊥ →
          centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H) =
            (oddCoreIn (centralizer ({h.a} : Set H)) ⊓ centralizer ({h.a * d.z} : Set H)) ⊔
              h.S →
          h.Concl81 := by
  intro I hRS H _ _ h H₁ d v hst hJ hK _ _
  rcases H₁.kOrSimple with hKG | hs
  · exact Hyp59.L81Hyp.Data.concl81_of_isKGroupCat h11 hrec hRS I hst hKG
      (Seven.localB_of_isKGroupCat hS hU hheld hKG h.oddCore_eq_bot) hJ hK
  · exact (Hyp59.L81Hyp.Data.false_of_isSimpleGroup hst.isV I hst hJ h11 hK hs).elim

end CFSG.ComponentClassification.GSThmB

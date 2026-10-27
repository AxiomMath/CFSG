module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakMaximalDef

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem gsWeakMaximalComponent_of_held (hS : SchreierFor Blueprint.Catalog)
    (hHN : HeldNotProperFixedInput) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X) {a : X}
    {J : Subgroup X} (ha : orderOf a = 2) (hJa : J ≤ centralizer ({a} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))))
    (hHe : IsHeldType (J ⧸ Open.fusionZStar J)) : GSWeakMaximalComponent J := by
  have hP := properFixedComponents_notHeld hHN
  refine ⟨⟨a, ha, hJa, hJ⟩, fun M hR => ?_⟩
  induction hR with
  | refl => exact ⟨MulEquiv.refl _⟩
  | tail _ hst ih =>
    obtain ⟨c, d, hW⟩ := hst
    obtain ⟨e⟩ := ih
    have hdZ := GSLit.not_mem_center_of_orderOf_eq_two hnonab hW.2.1
    rcases gsWeakCorr_type_dichotomy hS hK hW hdZ with he | ⟨hMa, hTM, hTpc, hlt, ⟨eT⟩⟩
    · obtain ⟨e'⟩ := he
      exact ⟨e.trans e'⟩
    · exfalso
      obtain ⟨hc, hd, hcd, -, -, hMd, hMp, -⟩ := hW
      have hdtop : centralizer ({d} : Set X) ≠ ⊤ := by
        intro htop
        exact hdZ (mem_center_iff.mpr fun g => mem_centralizer_singleton_iff.mp
          (by rw [htop]; exact mem_top g))
      have hcat := catalog_fusionZStar_of_isPComponent hK hdtop hMd hMp
      exact hP X c d _ _ hc hd hcd hMd hMp hMa hTM hTpc hlt hcat
        (hHe.map fun f => (e.trans eT).symm.trans f)

end CFSG.ComponentClassification.GrSLit

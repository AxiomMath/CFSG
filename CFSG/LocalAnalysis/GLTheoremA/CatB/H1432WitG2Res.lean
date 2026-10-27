module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432WitG2
import CFSG.HardMathSupport.Foote.Proving.RootCommute
import CFSG.SignalizerFunctorTheorem.CatalogBridge.RegularLemmaR

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.WitG2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SignalizerFunctorTheorem.NonLocalExc
  CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem g2CommRes_holds :
    G2CommRes := by
  intro K _ _ c d
  have hc : ∀ q ∈ commCandidates,
      RootOps.isRootB Tag.G2 (q.1 • eS + q.2 • thetaG2) = false := by
    decide +kernel
  have hnil : commPairs Tag.G2 eS thetaG2 = [] := by
    refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
    obtain ⟨hp, hr⟩ := mem_commPairs.1 hp
    exact Bool.false_ne_true ((hc p hp).symm.trans (RootOps.isRootB_iff.2 hr))
  exact (CFSG.HardMathSupport.Foote.Proving.commute_pinnedX_of_commPairs_eq_nil isRoot_eS
    isRoot_thetaG2 (by decide : (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) ≠ ![2, 3])
    (by decide : (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) ≠ -![2, 3]) hnil K c d).eq

theorem g2DirectRes_holds :
    G2DirectRes := by
  intro K _ _ c d h
  have h1 : HasCoord i2 (pinnedX Tag.G2 K eS c * pinnedX Tag.G2 K thetaG2 d) (c + 0) :=
    (hasCoord_pinnedX_single i2 c).mul (hasCoord_pinnedX_of_ne isRoot_thetaG2
      (by decide +kernel) (by decide : (![2, 3] : Fin 2 → ℤ) ≠ Pi.single (1 : Fin 2) 1) d)
  rw [h, add_zero] at h1
  have hc : c = 0 := h1.unique ⟨1, one_mem _, by rw [mul_one, xUnit_zero]⟩
  subst hc
  rw [pinnedX_zero, one_mul] at h
  exact ⟨rfl, pinnedX_injective Tag.G2 K thetaG2 (h.trans (pinnedX_zero Tag.G2 K thetaG2).symm)⟩

end CFSG.LocalAnalysis.GLTheoremA.H1420.WitG2

end

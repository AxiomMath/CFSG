module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.StableActionCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.FrattiniAutomorphismKernel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ElementaryLinearActions
public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeCorePreimage

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem primeStableAction_of_frattini_image_stability {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite acted]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime acted)
    (action : actor →* MulAut acted)
    (hstable : PrimeStableAction prime
      ((characteristicQuotientAction (frattini acted)).comp action.range.subtype)) :
    PrimeStableAction prime action := by
  let reduced := (characteristicQuotientAction (frattini acted)).comp action.range.subtype
  have hkernel : IsPGroup prime reduced.ker := by
    have heq : reduced.ker =
        ((characteristicQuotientAction (frattini acted)).ker).comap action.range.subtype := rfl
    rw [heq]
    exact (frattini_automorphism_kernel_isPGroup prime hprime hpgroup).comap_of_injective
      action.range.subtype action.range.subtype_injective
  intro member hquadratic
  have hreducedQuadratic : QuadraticAutomorphism (reduced (action.rangeRestrict member)) :=
    quadratic_characteristic_quotient_action (frattini acted) (action member) hquadratic
  have hcore := hstable (action.rangeRestrict member) hreducedQuadratic
  change action.rangeRestrict member ∈ actionPrimeCore prime reduced at hcore
  rw [actionPrimeCore_eq_primeCore_of_kernel prime reduced hkernel] at hcore
  rw [actionPrimeCore_eq_range_preimage]
  exact hcore

theorem primeStableAction_of_elementary_linear_stability {actor : Type u} {acted : Type v}
    [Group actor] [CommGroup acted] (prime : ℕ) [Fact prime.Prime]
    [Module (ZMod prime) (Additive acted)]
    (action : actor →* MulAut acted)
    (hstable : LinearPrimeStableAction prime ((zmodLinearAutomorphisms prime acted).comp action)) :
    PrimeStableAction prime action := by
  intro member hquadratic
  have hcore := hstable member (quadratic_zmod_linear_action prime acted (action member) hquadratic)
  have hkernel : ((zmodLinearAutomorphisms prime acted).comp action).ker = action.ker :=
    MonoidHom.ker_comp_of_injective action (zmodLinearAutomorphisms prime acted)
      (zmodLinearAutomorphisms_injective prime acted)
  change member ∈ (pCore prime (actor ⧸ ((zmodLinearAutomorphisms prime acted).comp action).ker)).comap
    (QuotientGroup.mk' ((zmodLinearAutomorphisms prime acted).comp action).ker) at hcore
  rw [primeCore_quotient_preimage_congr prime _ _ hkernel] at hcore
  exact hcore

end CFSG.RankThreeEvenClassification.Helpers

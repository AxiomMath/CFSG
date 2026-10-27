module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6Two
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6TwoWit
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIE6
import CFSG.LieType.Chevalley.TwistedE6FieldTwoCyclicKernel
import CFSG.LieType.Chevalley.C2E6StandardLevi
import CFSG.LieType.Chevalley.C2E6A5ExteriorCubeModel
import CFSG.LieType.Chevalley.C2E6D4NaturalOrthogonal
import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
import CFSG.LieType.Chevalley.C2E6FourthResidueMinusEight
import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativeData
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Monster.B.Geometry.CoxeterWords
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoHypIIY

theorem hypII_of_twistedE6Two
    {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤)
    (h : ChevalleyExceptionalModel (A ⧸ center A) .twistedE6 2 1) : HypII A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod : TwistedChevalleyModel (A ⧸ center A) .E6 (2 ^ 1) := h.2
  obtain ⟨L, _, _, σL, hL, hσL, ⟨e₁⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two le_rfl hmod
  obtain ⟨e₂⟩ := nonempty_mulEquiv_stdGroup_of_card_eq_four
    (L := L) (by rw [hL]; rfl) σL.toRingHom fun c => by simpa using hσL c
  have hK' : Nat.card C2E6Overlap.K = (2 ^ 1) ^ 2 := by
    rw [Nat.card_eq_fintype_card, C2E6Overlap.card_K]
    norm_num
  have hσ : ∀ c, C2E6Std.barEquiv c = c ^ 2 ^ 1 := fun c => rfl
  have hσ' : ∀ c, C2E6Std.barEquiv.toRingHom c = c ^ 2 ^ 1 := hσ
  have e : A ⧸ center A ≃*
      graphFixedRootGroup TwistTag.E6 C2E6Overlap.K C2E6Std.barEquiv.toRingHom := e₁.trans e₂
  have : Finite (graphFixedRootGroup TwistTag.E6 C2E6Overlap.K C2E6Std.barEquiv.toRingHom) :=
    Finite.of_equiv _ e.toEquiv
  have : Finite (MulAut
      (graphFixedRootGroup TwistTag.E6 C2E6Overlap.K C2E6Std.barEquiv.toRingHom)) :=
    MulEquiv.finite_left
  obtain ⟨ht, η, hη, -⟩ := (even_E6_graph_full_inner_diagonal_coset_exhaustion 1 le_rfl).2
    C2E6Overlap.K hK' C2E6Std.barEquiv.toRingHom hσ'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, -, -, -, hinv⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two le_rfl
      C2E6Overlap.K hK' C2E6Std.barEquiv hσ
  have hwit := secondGraphWitnessO2_twistedE6Two ht η hη
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 C2E6Overlap.K C2E6Std.barEquiv
  refine hypII_of_secondGraphO2 hZ ?_ Θ ringAut_mul_comm ?_ ?_ hwit hA e
  · intro α hαX hα2
    rcases rigid_or_secondGraph_twistedE6 le_rfl hK' C2E6Std.barEquiv hσ α hαX hα2 with
      h | ⟨_ht, η', hη', φ, hφ⟩
    · exact Or.inl h
    · have e' : η' = η := MulEquiv.ext fun g => Subtype.ext (by rw [hη', hη])
      subst e'
      exact Or.inr ⟨φ, hφ⟩
  · intro α hα hα2
    refine (hinv α hα2).resolve_right fun hσα => ?_
    obtain ⟨d, hd⟩ := exists_ne_fixed le_rfl hK' hσ'
    have h1 : C2E6Std.barEquiv = 1 := hσα.1.symm.trans hα
    exact hd (by rw [show C2E6Std.barEquiv.toRingHom d = C2E6Std.barEquiv d from rfl, h1]; rfl)
  · intro x hx2 hx1
    have hx := orderOf_eq_prime hx2 hx1
    by_cases hxX : x ∈ OuterAutomorphisms.inner
        (graphFixedRootGroup TwistTag.E6 C2E6Overlap.K C2E6Std.barEquiv.toRingHom)
    · have h0 := even_exceptional_inner_involution_full_centralizer_odd_core.2 TwistTag.E6 1
        C2E6Overlap.K C2E6Std.barEquiv le_rfl hK' hσ _ le_rfl x hxX hx
      rwa [← CFSG.RankThree.Chevalley.oddCore_eq_pPrimeCore_two'] at h0
    · exact oddCore_inner_inf_eq_bot
        ((CFSG.RankThree.Chevalley.even_E6_twisted_E6_outer_involution_full_centralizer_odd_core
          le_rfl).2 C2E6Overlap.K hK' C2E6Std.barEquiv.toRingHom hσ' ⊤ le_top x (mem_top x) hxX hx)

theorem twistedE6TwoEvenHypII
    : TwistedE6TwoEvenHypII := by
  intro A _ _ hA h _
  exact hypII_of_twistedE6Two hA h

end CFSG.ComponentClassification.RankTwoExcHypII

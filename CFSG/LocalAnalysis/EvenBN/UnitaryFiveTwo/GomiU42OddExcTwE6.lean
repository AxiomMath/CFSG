module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcE6Gr
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6TwistedOuter
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeafProof

theorem gomi_TwE6_outer_false
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = (p ^ f) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (β : MulAut (graphFixedRootGroup TwistTag.E6 F σ.toRingHom)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ twistedE6Inn F σ)
    (L : Subgroup ↥(β.toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))))
    (hL : CFSG.IsComponent L) (hLd : Nat.card L ∣ 51840) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have : CharP F p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (show 1 ≤ f * 2 by omega) (by rw [hF, ← pow_mul])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have halg := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  obtain ⟨x, hxR, hx2, ⟨Φ⟩⟩ := exists_mulEquiv_twisted_E6_outer_fixed hp2 hf F hF σ hσ β hβ2 hβo
  have hΦL := CFSG.LocalCores.isComponent_map_mulEquiv Φ hL
  have h5 := gomi_pow_dvd_of_isComponent_graphCosetFixed p hp2 hf (AlgebraicClosure F) halg 1
    (Or.inr rfl) hxR hx2 hΦL
  have hc : Nat.card ↥(Subgroup.map Φ.toMonoidHom L) = Nat.card ↥L :=
    Subgroup.card_map_of_injective (f := Φ.toMonoidHom) (K := L) Φ.injective
  rw [hc] at h5
  exact gomi_not_pow_five_dvd hodd (Nat.one_lt_pow (by omega) hp.one_lt) (h5.trans hLd)

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

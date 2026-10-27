module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlockOrdinaryRootObstruction
public import CFSG.LieType.Chevalley.FixedRootCentralizerGeneration

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

variable {G : Type*} [Group G] [Finite G]

theorem commuting_block_fixed_root_quotient_prime_divisor_obstruction {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) (r : ℕ) [Fact r.Prime] (hr : Odd r)
    (k : Type) [Field k] [Finite k] [CharP k r] (t : CFSG.Blueprint.Chevalley.TwistTag)
    (σ : k ≃+* k) (hσ : σ ^ t.order = 1)
    (he : Nonempty (L ⧸ center L ≃*
      CFSG.LieType.Chevalley.graphFixedRootGroup t k σ.toRingHom)) :
    ¬ r ∣ Nat.card J := by
  obtain ⟨e⟩ := he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (L ⧸ center L) := hL.2
  have : IsSimpleGroup (CFSG.LieType.Chevalley.graphFixedRootGroup t k σ.toRingHom) :=
    MulEquiv.isSimpleGroup e.symm
  have hr2 : r ≠ 2 := fun h => by rw [h] at hr; exact (Nat.not_even_iff_odd.2 hr) even_two
  exact not_dvd_card_of_centralizer_generation hq heven hV hJ hΔ hL hML hLH e
    fun A hAC hAe hAcard R hRC hRr hR hAR =>
      have : CFSG.IsElementaryAbelian 2 A := hAe
      CFSG.LieType.Chevalley.fixed_root_invariant_prime_subgroup_centralizer_generation t k r 2
        hr2 σ hσ A hAC hAcard R hRC hRr hR hAR

end CFSG.LocalAnalysis.ComponentInitial

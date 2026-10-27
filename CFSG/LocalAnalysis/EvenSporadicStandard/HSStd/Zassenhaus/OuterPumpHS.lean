module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.HSStd

variable {G : Type} [Group G] [Finite G]

theorem card_sylow_eq_two_of_stdHyp_hs
    (hCTB : CentralTwoBound) (hSol : TwoHS.SolomonTwoHSCentralizer) {M : Subgroup G}
    (h : StdHyp G M) (hHS : IsSporadic (↥M ⧸ center ↥M) .HS)
    (S : Sylow 2 (centralizer (M : Set G))) : Nat.card S = 2 := by
  have hb := (hCTB ↥M h.standard.1 h.centerTwo .HS hHS).1
  have hd : Nat.card (center ↥M) ∣ 2 := by simpa [twoPartBound] using hb
  rcases eq_bot_or_card_eq_two hd with hz | h2
  · exact h.card_sylow_eq_two_hs hsFacts (isSporadic_of_center_eq_bot hz hHS) S
  · exact hSol G M h h2 hHS S

theorem false_of_hs_standard
    (hKG : KGHSA8) (hTab : KGPumpTable) (hsplit : KGHSNoDoubleA8) (hCTB : CentralTwoBound)
    (hSol : TwoHS.SolomonTwoHSCentralizer) (ctx : PumpCtx G) {K₀ M : Subgroup G}
    (hp₀ : PumpType (↥K₀ ⧸ center ↥K₀)) (hch : TransGen LtF K₀ M) (hne : K₀ ≠ M)
    (hstd : StdBare M) (hHS : IsSporadic (↥M ⧸ center ↥M) .HS) (hSH : StdHyp G M) {g : G}
    (hc : ⁅K₀, K₀.map (MulAut.conj g).toMonoidHom⁆ = ⊥) : False := by
  obtain ⟨K, s, t, hl, hA, ⟨e⟩⟩ := a8_partner_simple ctx hTab hsplit hp₀ hch hne hstd hHS
  have hJ : ∀ (r : G), ⁅K, K.map (MulAut.conj r).toMonoidHom⁆ = ⊥ →
      ∃ J : Subgroup G, J ≤ centralizer (K : Set G) ∧ Nonempty (↥J ≃* alternatingGroup (Fin 8)) := by
    intro r hr
    refine ⟨K.map (MulAut.conj r).toMonoidHom, ?_, ⟨?_⟩⟩
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hr
    · exact (K.equivMapOfInjective _ (MulAut.conj r).injective).symm.trans e
  obtain ⟨J, hJc, hJ8⟩ : ∃ J : Subgroup G, J ≤ centralizer (K : Set G) ∧
      Nonempty (↥J ≃* alternatingGroup (Fin 8)) := by
    rcases hA.partner with rfl | ⟨s', t', -, -, -, -, -, hcomm⟩
    · exact hJ g hc
    · exact hJ s' hcomm
  exact false_of_sylow_trick hKG hSH.standard hHS
    (card_sylow_eq_two_of_stdHyp_hs hCTB hSol hSH hHS) hl.le ⟨e⟩ hJc hJ8

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

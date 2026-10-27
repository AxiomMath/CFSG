module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTKill
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTChain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTAlt10
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem false_of_a8_maximal
    (hT : KGPumpTableT) (ctx : PumpCtx G) {K₀ M : Subgroup G}
    (hp₀ : PumpType (↥K₀ ⧸ center ↥K₀)) (hch : TransGen LtF K₀ M) (hne : K₀ ≠ M)
    (hstd : StdBare M) (hA8 : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 8))) :
    False := by
  have hTab := kgPumpTable_of_T hT
  obtain ⟨K, s, t, hl⟩ := exists_last_link hch hne hstd
  have hpK : PumpType (↥K ⧸ center ↥K) := by
    rcases hl.chain with rfl | hTr
    · exact hp₀
    · exact pumpType_of_transGen ctx hTab hTr hp₀
  rcases vertical_table ctx hTab hl.s_order hl.t_order hl.comp_K hl.comp_M hl.conj_eq hl.le hpK
    with h | ⟨-, hn, -⟩
  · exact hl.ne h
  · exact hn hA8

omit [Finite G] in
theorem exists_partner_alt8 {K₀ K : Subgroup G} (hA : A8Partner K₀ K)
    (hK : Nonempty (↥K ≃* alternatingGroup (Fin 8))) {g : G}
    (hc : ⁅K₀, K₀.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    ∃ J : Subgroup G, J ≤ centralizer (K : Set G) ∧
      Nonempty (↥J ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e⟩ := hK
  have hJ : ∀ (r : G), ⁅K, K.map (MulAut.conj r).toMonoidHom⁆ = ⊥ →
      ∃ J : Subgroup G, J ≤ centralizer (K : Set G) ∧ Nonempty (↥J ≃* alternatingGroup (Fin 8)) := by
    intro r hr
    refine ⟨K.map (MulAut.conj r).toMonoidHom, ?_, ⟨?_⟩⟩
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hr
    · exact (K.equivMapOfInjective _ (MulAut.conj r).injective).symm.trans e
  rcases hA.partner with rfl | ⟨s', t', -, -, -, -, -, hcomm⟩
  · exact hJ g hc
  · exact hJ s' hcomm

theorem false_of_a10_standard
    (hT : KGPumpTableT) (hSI : SolomonIAltCentralizer) (hKA : KGA10A8) (ctx : PumpCtx G)
    {K₀ M : Subgroup G} (hp₀ : PumpType (↥K₀ ⧸ center ↥K₀)) (hch : TransGen LtF K₀ M)
    (hne : K₀ ≠ M) (hstd : StdBare M)
    (hA10 : Nonempty (↥M ⧸ center ↥M ≃* alternatingGroup (Fin 10))) (hZ : center ↥M = ⊥)
    (hSH : StdHyp G M) {g : G} (hc : ⁅K₀, K₀.map (MulAut.conj g).toMonoidHom⁆ = ⊥) : False := by
  obtain ⟨K, s, t, hl, hA, -, -⟩ := last_link_of_a10_or_hs ctx hT hp₀ hch hne hstd (Or.inl hA10)
  have eM : ↥M ≃* ↥M ⧸ center ↥M :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center ↥M))
      ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact hZ),
        QuotientGroup.mk'_surjective _⟩
  have hcen : center ↥K = ⊥ :=
    center_eq_bot_of_alt8_le_alt10 ⟨eM.trans hA10.some⟩ hl.le hl.comp_K.isQuasisimple hA.quot
  have hK8 : Nonempty (↥K ≃* alternatingGroup (Fin 8)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans
      hA.quot.some⟩
  obtain ⟨J, hJc, hJ8⟩ := exists_partner_alt8 hA hK8 hc
  exact false_of_a10_of_pair hSI hKA hSH hZ hA10 hl.le hK8 hJc hJ8

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

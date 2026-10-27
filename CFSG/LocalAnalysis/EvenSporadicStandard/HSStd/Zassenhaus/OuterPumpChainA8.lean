module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChain

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd

variable {G : Type} [Group G]

@[expose] def KGHSNoDoubleA8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M K : Subgroup G), CFSG.IsQuasisimple ↥M →
    IsPGroup 2 ↥(center ↥M) → IsSporadic (↥M ⧸ center ↥M) .HS → K ≤ M → CFSG.IsQuasisimple ↥K →
      Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8)) → center ↥K = ⊥

structure A8Partner (K₀ K : Subgroup G) : Prop where
  quot : Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8))
  partner : K = K₀ ∨ ∃ s' t' : G, orderOf s' = 2 ∧ orderOf t' = 2 ∧ s' * t' = t' * s' ∧
    IsCompIn K (centralizer ({t'} : Set G)) ∧ K.map (MulAut.conj s').toMonoidHom ≠ K ∧
    ⁅K, K.map (MulAut.conj s').toMonoidHom⁆ = ⊥

theorem a8_partner [Finite G] (ctx : PumpCtx G) (hTab : KGPumpTable) {K₀ M : Subgroup G}
    (hp₀ : PumpType (↥K₀ ⧸ center ↥K₀)) (hch : TransGen LtF K₀ M) (hne : K₀ ≠ M)
    (hstd : StdBare M) (hHS : IsSporadic (↥M ⧸ center ↥M) .HS) :
    ∃ (K : Subgroup G) (s t : G), LastLink K₀ M K s t ∧ A8Partner K₀ K := by
  obtain ⟨K, s, t, hl⟩ := exists_last_link hch hne hstd
  have hpK : PumpType (↥K ⧸ center ↥K) := by
    rcases hl.chain with rfl | hT
    · exact hp₀
    · exact pumpType_of_transGen ctx hTab hT hp₀
  rcases vertical_table ctx hTab hl.s_order hl.t_order hl.comp_K hl.comp_M hl.conj_eq hl.le hpK
    with h | ⟨-, -, h3⟩
  · exact absurd h hl.ne
  obtain ⟨e⟩ := h3 hHS
  refine ⟨K, s, t, hl, ⟨e⟩, ?_⟩
  by_cases hK0 : K = K₀
  · exact Or.inl hK0
  right
  have hT : TransGen LtF K₀ K := hl.chain.resolve_left hK0
  obtain ⟨K', hK'K, hK'0, s', t', hs', ht', hst', hK's, hKt', hK'le⟩ :=
    exists_pred_of_transGen hT (Ne.symm hK0)
  have hpK' : PumpType (↥K' ⧸ center ↥K') := by
    rcases hK'0 with rfl | hT'
    · exact hp₀
    · exact pumpType_of_transGen ctx hTab hT' hp₀
  have hKs : K.map (MulAut.conj s').toMonoidHom ≠ K := by
    intro hKe
    rcases vertical_table ctx hTab hs' ht' hK's hKt' hKe (le_of_conj_eq hKe hK'le) hpK'
      with h | ⟨-, hn, -⟩
    · exact hK'K h
    · exact hn ⟨e⟩
  exact ⟨s', t', hs', ht', hst', hKt', hKs, commutator_conj_eq_bot_of_ne hst' hKt' hKs⟩

theorem a8_partner_simple [Finite G] (ctx : PumpCtx G) (hTab : KGPumpTable)
    (hsplit : KGHSNoDoubleA8) {K₀ M : Subgroup G} (hp₀ : PumpType (↥K₀ ⧸ center ↥K₀))
    (hch : TransGen LtF K₀ M) (hne : K₀ ≠ M) (hstd : StdBare M)
    (hHS : IsSporadic (↥M ⧸ center ↥M) .HS) :
    ∃ (K : Subgroup G) (s t : G), LastLink K₀ M K s t ∧ A8Partner K₀ K ∧
      Nonempty (↥K ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨K, s, t, hl, hA⟩ := a8_partner ctx hTab hp₀ hch hne hstd hHS
  have hcen : center ↥K = ⊥ :=
    hsplit G M K hl.comp_M.isQuasisimple (ctx.isPGroup_center hl.t_order hl.comp_M) hHS hl.le
      hl.comp_K.isQuasisimple hA.quot
  obtain ⟨e⟩ := hA.quot
  refine ⟨K, s, t, hl, hA, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans e

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

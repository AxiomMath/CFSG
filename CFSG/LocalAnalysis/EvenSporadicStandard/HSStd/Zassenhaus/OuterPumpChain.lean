module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainVertical

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd

variable {G : Type} [Group G]

theorem PumpCtx.fStarSimple [Finite G] (ctx : PumpCtx G) : FStarSimple (⊤ : Subgroup G) := by
  have := ctx.simple
  exact fStarSimple_top G ctx.nonabelian

theorem pumpType_of_ltF [Finite G] (ctx : PumpCtx G) (hTab : KGPumpTable) {K L : Subgroup G}
    (h : LtF K L) (hp : PumpType (↥K ⧸ center ↥K)) : PumpType (↥L ⧸ center ↥L) := by
  obtain ⟨s, t, hs, ht, hst, hK, hL, hKL⟩ := h
  by_cases hLe : L.map (MulAut.conj s).toMonoidHom = L
  · rcases vertical_table ctx hTab hs ht hK hL hLe (le_of_conj_eq hLe hKL) hp with rfl | ⟨hP, -, -⟩
    · exact hp
    · exact hP
  · obtain ⟨e⟩ := nonempty_quotient_center_equiv_of_ltF_ne hs hst hK hL hKL hLe
    exact PumpType.congr e.symm hp

theorem pumpType_of_transGen [Finite G] (ctx : PumpCtx G) (hTab : KGPumpTable) {K L : Subgroup G}
    (h : TransGen LtF K L) (hp : PumpType (↥K ⧸ center ↥K)) : PumpType (↥L ⧸ center ↥L) := by
  induction h with
  | single h => exact pumpType_of_ltF ctx hTab h hp
  | tail _ h ih => exact pumpType_of_ltF ctx hTab h ih

theorem stdBare_of_maximalF_pumpType [Finite G] (ctx : PumpCtx G) (h13 : FS79Thm13UseSec G)
    (hrank : KGPumpRank) {M : Subgroup G} (hM : MaximalF M) (hp : PumpType (↥M ⧸ center ↥M)) :
    StdBare M := by
  refine h13.at ctx.kProper ⊤ ctx.fStarSimple (fun _ _ => le_top) M hM fun h1 => ?_
  obtain ⟨t, ht, hMt⟩ := hM.1
  have h2 := hrank ↥M hMt.isQuasisimple (ctx.isPGroup_center ht hMt) hp
  omega

theorem not_maximalF_of_commute_conj [Finite G] (ctx : PumpCtx G) (h13 : FS79Thm13UseSec G)
    (hrank : KGPumpRank) {M : Subgroup G} (hp : PumpType (↥M ⧸ center ↥M)) (g : G)
    (hc : ⁅M, M.map (MulAut.conj g).toMonoidHom⁆ = ⊥) : ¬ MaximalF M :=
  fun hM => (stdBare_of_maximalF_pumpType ctx h13 hrank hM hp).1 g hc

theorem exists_pred_of_transGen {K₀ M : Subgroup G} (h : TransGen LtF K₀ M) (hne : K₀ ≠ M) :
    ∃ K : Subgroup G, K ≠ M ∧ (K = K₀ ∨ TransGen LtF K₀ K) ∧ LtF K M := by
  revert hne
  induction h with
  | single h => exact fun hne => ⟨K₀, hne, Or.inl rfl, h⟩
  | @tail b c hab hbc ih =>
    intro hne
    by_cases hbc' : b = c
    · subst hbc'
      exact ih hne
    · exact ⟨b, hbc', Or.inr hab, hbc⟩

theorem exists_maximal_pump_above [Finite G] (ctx : PumpCtx G) (hTab : KGPumpTable)
    (h13 : FS79Thm13UseSec G) (hrank : KGPumpRank) {K₀ : Subgroup G} (h₀ : InLF K₀)
    (hp : PumpType (↥K₀ ⧸ center ↥K₀)) (g : G)
    (hc : ⁅K₀, K₀.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    ∃ M : Subgroup G, TransGen LtF K₀ M ∧ K₀ ≠ M ∧ MaximalF M ∧
      PumpType (↥M ⧸ center ↥M) ∧ StdBare M := by
  obtain ⟨M, hM, hmax, -⟩ := exists_maximalF_above h₀
  rcases hM with rfl | hT
  · exact absurd hmax (not_maximalF_of_commute_conj ctx h13 hrank hp g hc)
  · have hpM := pumpType_of_transGen ctx hTab hT hp
    refine ⟨M, hT, ?_, hmax, hpM, stdBare_of_maximalF_pumpType ctx h13 hrank hmax hpM⟩
    rintro rfl
    exact not_maximalF_of_commute_conj ctx h13 hrank hp g hc hmax

structure LastLink (K₀ M K : Subgroup G) (s t : G) : Prop where
  chain : K = K₀ ∨ TransGen LtF K₀ K
  s_order : orderOf s = 2
  t_order : orderOf t = 2
  comm : s * t = t * s
  comp_K : IsCompIn K (centralizer ({s} : Set G))
  comp_M : IsCompIn M (centralizer ({t} : Set G))
  conj_eq : M.map (MulAut.conj s).toMonoidHom = M
  le : K ≤ M
  ne : K ≠ M

theorem exists_last_link [Finite G] {K₀ M : Subgroup G} (hch : TransGen LtF K₀ M) (hne : K₀ ≠ M)
    (hstd : StdBare M) : ∃ (K : Subgroup G) (s t : G), LastLink K₀ M K s t := by
  obtain ⟨K, hKM, hK0, s, t, hs, ht, hst, hKs, hMt, hKle⟩ := exists_pred_of_transGen hch hne
  by_cases hMs : M.map (MulAut.conj s).toMonoidHom = M
  · exact ⟨K, s, t, ⟨hK0, hs, ht, hst, hKs, hMt, hMs, le_of_conj_eq hMs hKle, hKM⟩⟩
  · exact absurd (commutator_conj_eq_bot_of_ne hst hMt hMs) (hstd.1 s)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

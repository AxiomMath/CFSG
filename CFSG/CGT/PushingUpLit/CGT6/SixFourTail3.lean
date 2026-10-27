module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourTail2
public import CFSG.CGT.PushingUpLit.CGT6.SixFourPSL

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.Assembly (KProper InCatalog)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open scoped commutatorElement Pointwise

@[expose] def SLTailU3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G) (R : Subgroup G) [R.Normal], EightCtx Y T R →
      ∀ n : ℕ, 1 ≤ n → IsNaturalSLTwoModule ↥Y n →
        ∀ s : ℕ, 2 ≤ s → ¬ StatedClassicalModel (SLLam R T) StatedLieTag.PSU 3 2 s

@[expose] def SLTailA9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G) (R : Subgroup G) [R.Normal], EightCtx Y T R →
      ∀ n : ℕ, 1 ≤ n → IsNaturalSLTwoModule ↥Y n →
        ¬ Nonempty (SLLam R T ≃* alternatingGroup (Fin 9))

@[expose] def SLTailA67 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G) (R : Subgroup G) [R.Normal], EightCtx Y T R →
      ∀ n : ℕ, 1 ≤ n → IsNaturalSLTwoModule ↥Y n →
        (Nonempty (SLLam R T ≃* alternatingGroup (Fin 6)) ∨
          Nonempty (SLLam R T ≃* alternatingGroup (Fin 7))) →
        ∀ U₀ : Subgroup G, ⁅oTwoIn Y, Y⁆ ≤ U₀ → U₀ ≤ (T : Subgroup G) →
          Y ≤ Subgroup.normalizer (U₀ : Set G) →
          (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal →
          ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X

theorem aschbacherSLTail'_of_parts (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hU3 : SLTailU3) (hA9 : SLTailA9) (hA67 : SLTailA67) : AschbacherSLTail' := by
  intro G _ _ hK hchar Y T R _ hctx n hn hnat hf hsz hM22 hM23 hM24 U₀ hU hU₀T hYU hYs
  obtain ⟨-, -, hlist, -⟩ := eight_sl_ident hctx hn hnat hS h215 hL
  rcases hlist with ⟨m, s, hm2, -, hmodel⟩ | ⟨s, hs2, hmodel⟩ | ⟨s, hsodd, -, hmodel⟩ |
    ⟨k, hk6, hk9, hk⟩ | h22 | h23 | h24
  · rcases Nat.lt_or_ge m 3 with hm | hm
    · obtain rfl : m = 2 := by omega
      exact absurd hmodel (hf s)
    · exact (eight_sl_not_psl_ge3 hctx hn hnat hS h215 hL hm hmodel).elim
  · exact (hU3 G hK hchar Y T R hctx n hn hnat s hs2 hmodel).elim
  · obtain ⟨a, rfl⟩ := hsodd
    exact (hsz a hmodel).elim
  · interval_cases k
    · exact hA67 G hK hchar Y T R hctx n hn hnat (Or.inl hk) U₀ hU hU₀T hYU hYs
    · exact hA67 G hK hchar Y T R hctx n hn hnat (Or.inr hk) U₀ hU hU₀T hYU hYs
    · exact (eight_sl_not_alt8 hctx hn hnat hS h215 hL hk).elim
    · exact (hA9 G hK hchar Y T R hctx n hn hnat hk).elim
  · exact (hM22 h22).elim
  · exact (hM23 h23).elim
  · exact (hM24 h24).elim

end CFSG.CGT.PushingUpLit.CGT6

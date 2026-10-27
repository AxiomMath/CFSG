module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gKinds
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gSec
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eKinds

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

namespace P85

theorem sylCfg_in_G {G : Type} [Group G] [Finite G] (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal]
    (hodd : Odd (Nat.card H₁)) {α : ↥H₀ ⧸ H₁ → ↥H₀ ⧸ H₁} {P E F : Subgroup (↥H₀ ⧸ H₁)}
    (h : SylCfg α P E F) : ∃ P' E' F' : Subgroup G, SylCfg id P' E' F' ∧ IsPGroup 2 P' := by
  obtain ⟨P₀, E₀, F₀, hcfg₀, hP2, -, -, -, -⟩ := lift_sylCfg H₁ hodd h
  exact ⟨P₀.map H₀.subtype, E₀.map H₀.subtype, F₀.map H₀.subtype,
    hcfg₀.map H₀.subtype H₀.subtype_injective (α := id) (α' := id) (fun y => rfl), hP2.map _⟩

end P85

open P85 in
theorem prop85g_thm : Prop85g := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hhyp hL hc hL2
  obtain ⟨hord, htK, P, E, F, hcfg, hPK⟩ :=
    section_sylCfg hctx.orderOf_z H₁ hz hsig.odd hL hc hL2
  have ht2 : zSec z H₀ hz H₁ * zSec z H₀ hz H₁ = 1 := by
    have := pow_orderOf_eq_one (zSec z H₀ hz H₁)
    rwa [hord, sq] at this
  have htP : zSec z H₀ hz H₁ ∉ P := fun h => htK (hPK h)
  obtain ⟨P', E', F', hcfg', hP2'⟩ := sylCfg_in_G H₀ H₁ hsig.odd hcfg
  cases hctx.data with
  | g2 _ => exact (no_sylCfg_rank (hctx.rank_three (Or.inl rfl)) hcfg').elim
  | m12 _ => exact (no_sylCfg_rank (hctx.rank_three (Or.inr rfl)) hcfg').elim
  | psp4 hp =>
    obtain ⟨q, L₁, L₂, hp⟩ := hp
    obtain ⟨x, htwo⟩ := hp.two
    exact (no_sylCfg_two_class hctx (lpairCtx_psp4 hctx) htwo hcfg' hP2').elim
  | l4 ε hl =>
    obtain ⟨q, L₁, L₂, hl⟩ := hl
    rcases hl.fusion with ⟨hq4, -⟩ | ⟨hq4, x, htwo, -, -⟩
    · have hq8 : q % 8 = 3 ∨ q % 8 = 5 := by
        have h1 := hl.mod8
        cases ε <;> simp at hq4 h1 <;> omega
      have hS128 := card_S_le_128 hctx.S_le_Cen hctx.sylow.isPGroup hq8 hl.pair.prod hl.pair.sl₁
        hl.pair.sl₂ hl.index_le
      exact (no_one_class hctx hS128 H₁ hsig.odd hcfg ht2 htP).elim
    · exact (no_sylCfg_two_class hctx (lpairCtx_l4 ε hctx) htwo hcfg' hP2').elim
  | mcl _ => exact Or.inl rfl
  | ly _ => exact Or.inr rfl

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Red
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Prop47R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H X T : Subgroup G) (p : ℕ), Sig4Sub G z H p X → T ≤ H ⊓ S → T4CS z k S T →
      T ≤ normalizer (X : Set G) → ¬ X ≤ Op p H →
      ⁅pCore 2 (Sec H (pCore p ↥H)), xBar p H X⁆ = ⊥

theorem prop47R_of_typeOne {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}
    (ctx : Stage2Ctx G z k S) {H X : Subgroup G} {p : ℕ} (sig : Sig4Sub G z H p X) (hSH : S ≤ H)
    (hnot : ¬ X ≤ Op p H) :
    ⁅pCore 2 (Sec H (pCore p ↥H)), xBar p H X⁆ = ⊥ := by
  have hsig := sig4B_of_sub ctx.orderOf_z sig hnot
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 S H := ctx.sylow_top.of_le hSH le_top
  have hS'syl := Odd87.xBar_isSylowOf_top (p := p) hSsyl
  have hS'n := Odd87.xBar_le_normalizer sig ctx.sylow.le
  exact Odd87.commutator_eq_bot_of_normal_two (pCore_isPGroup (p := 2) (G := Sec H (pCore p ↥H)))
    sig.A.prime sig.A.odd hsig.A.pgroup ((Odd87.pCore_two_le_sylow hS'syl).trans hS'n)

end CFSG.GH74.GLS.Stage2.Signalizer

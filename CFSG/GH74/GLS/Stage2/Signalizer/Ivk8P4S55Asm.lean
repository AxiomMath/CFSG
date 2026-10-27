module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem core55_of_cells (h : Cells55) {k : Kind} {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} {a : Γ} {P R : Subgroup Γ}
    (hf : Frame55 k p ρ K a P R) : Concl55 p K := by
  rcases ghList_cases hf.gh with
    hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF
  · exact h.alt k p Γ V ρ K a P R hf hF
  · exact h.spor k p Γ V ρ K a P R hf hF
  · exact h.mcly k p Γ V ρ K a P R hf hF
  · exact h.two k p Γ V ρ K a P R hf hF
  · exact h.l2 k p Γ V ρ K a P R hf hF
  · exact h.l3 k p Γ V ρ K a P R hf hF
  · exact h.u3 k p Γ V ρ K a P R hf hF
  · exact h.sp4 k p Γ V ρ K a P R hf hF
  · exact h.g2 k p Γ V ρ K a P R hf hF
  · exact h.d4 k p Γ V ρ K a P R hf hF
  · exact h.l4 k p Γ V ρ K a P R hf hF
  · exact h.u4 k p Γ V ρ K a P R hf hF
  · exact h.l5 k p Γ V ρ K a P R hf hF
  · exact h.u5 k p Γ V ρ K a P R hf hF
  · exact h.ree k p Γ V ρ K a P R hf hF

theorem lemma5_5m_of (hA : Frame55Thm) (hB : Case55B) (hC : Cells55) : Lemma5_5m := by
  intro G _ _ z k S ctx T Tstar p H P hc hnot l52 g X Y hs53
  by_cases h1 : TypeOneCase G k
  · obtain ⟨Γ, _, _, V, _, _, _, ρ, K, a, P', R, hf, hl⟩ :=
      hA G z k S ctx T Tstar p H P hc hnot l52 g X Y hs53 h1
    exact hl (core55_of_cells hC hf)
  · exact (hB G z k S ctx T Tstar p H P hc hnot l52 g X Y hs53 h1).elim

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

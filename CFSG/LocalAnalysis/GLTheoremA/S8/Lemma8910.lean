module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma810

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace S8

structure Inputs8910 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop extends L89.Inputs89 G p

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem cfg_extraspecial (hc : S8Ctx G p) (hin : Inputs8910 G p) {x : G} {L : Subgroup G} {row : Row}
    (hx : orderOf x = p) (hL : GLAPComponent p (cx x) L) (hrow : RowL row p L)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p (cx x)))) (c : SporCfg G p x L row)
    {M : Subgroup G} (hM : GLAIsMaxTwoLocal M) (hNM : Subgroup.normalizer (c.R : Set G) ≤ M) :
    c.R ≤ pCoreOf 2 M ∧ IsExtraSpec2 (pCoreOf 2 M) ∧ c.R = pCoreOf 2 M ⊓ cx x := by
  obtain ⟨hS, hT⟩ := L89.lemma810 hc hin.toInputs89 hx hL hrow c hM hNM
  refine ⟨?_, hS ▸ hT, ?_⟩
  · rw [hS]
    exact le_sup_left
  · rw [hS]
    exact (L89.T_inf_cx c hNM).symm

end S8

end CFSG.LocalAnalysis.GLTheoremA

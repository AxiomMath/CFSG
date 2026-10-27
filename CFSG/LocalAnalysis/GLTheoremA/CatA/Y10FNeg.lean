module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def I14NegFact : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ) (α : MulAut K) (J : Subgroup K) (labK labJ : GLALabel),
    p.Prime → p ≠ 2 → HasLabel K (fun l : GLALabel => l = labK) →
    HasLabel ↥J (fun l : GLALabel => l = labJ) → α ^ p = 1 →
    GLAPComponent p (fixSubgroup α) J → I14Neg p labK labJ

variable {G : Type} [Group G] [Finite G]

theorem i14NegAt_of_fact (h : I14NegFact) : I14NegAt G := by
  intro p K J y labK labJ hp hp2 _ _ hy hyp hcomp hlK hlJ
  obtain ⟨hJK, hcomp'⟩ := glaPComponent_fixSubgroup_conjAut' hp K hy hcomp
  exact h ↥K p (conjAut' K y hy) (J.subgroupOf K) labK labJ hp hp2 hlK
    ((hasLabel_subgroupOf_iff hJK _).1 hlJ) (conjAut'_pow K hy hyp) hcomp'

end CFSG.LocalAnalysis.GLTheoremA.Y10F

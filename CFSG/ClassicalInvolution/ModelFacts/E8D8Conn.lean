module

public import CFSG.ClassicalInvolution.ModelFacts.E8D8ConnGen
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclLayerStmt

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable (p f : ℕ) [Fact p.Prime]

theorem fund12Connected (hf : 1 ≤ f) : Fund12Connected p f := by
  have hadm : StatedLieAdmissible .POmegaPlus 6 p f := ⟨Fact.out, hf, by norm_num⟩
  intro R R'
  refine ModelFacts.E8D8.reflTransGen_of_generated
    (Fund := fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D)
    (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (ModelFacts.fundamentalSingleClass .POmegaPlus 6 p f Fact.out trivial hadm (by decide)
      (by decide)) ?_ R R'
  rw [← Balance.iSup_rankOneRoot_eq_top .POmegaPlus 6 p f Fact.out trivial hadm 1]
  refine iSup₂_le fun γ hγ => ?_
  exact le_iSup₂_of_le (Balance.rankOneRoot (modelUniv .POmegaPlus 6 p f Fact.out).D 1 γ)
    ⟨1, γ, Or.inl (Balance.isLongestRoot_of_mem_roots_simplyLaced .POmegaPlus 6 p f Fact.out
      trivial hadm (Or.inr (Or.inl rfl)) hγ), rfl⟩ le_rfl

theorem fund12Connected_of_five_le (hq : 5 ≤ p ^ f) : Fund12Connected p f :=
  fund12Connected p f (by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h)

end CFSG.ClassicalInvolution.RouteD.TypeE8

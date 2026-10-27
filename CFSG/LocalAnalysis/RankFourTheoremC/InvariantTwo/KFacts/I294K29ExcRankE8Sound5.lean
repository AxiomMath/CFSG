module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankE8Sound1

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC.ExcRank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg

def eigSub {τ : Tag} {p : ℕ} (ω : List (Fin τ.rank)) (q : ZMod p) :
    Submodule (ZMod p) (Fin τ.rank → ZMod p) where
  carrier := {z | pAct ω z = q • z}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [pAct_add, ha, hb, smul_add]
  zero_mem' := by simp [pAct_zero]
  smul_mem' := fun c a ha => by
    simp only [Set.mem_setOf_eq] at *
    rw [pAct_smul, ha, smul_comm]

theorem mem_eigSub {τ : Tag} {p : ℕ} {ω : List (Fin τ.rank)} {q : ZMod p}
    {z : Fin τ.rank → ZMod p} : z ∈ eigSub ω q ↔ pAct ω z = q • z := Iff.rfl

end CFSG.LocalAnalysis.RankFourTheoremC.ExcRank

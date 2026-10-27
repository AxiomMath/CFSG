module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB1Comm
public import CFSG.Sporadic.Bridge.TwoGen

public noncomputable section

namespace CFSG.EvenSporadicStandard.Induction.RuSz

open Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.RuSchreier
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
open CFSG.Sporadic.Th (Rep)
open CFSG.EvenSporadicStandard.TwoRu.HypOne (lGens lGensInv letterG)

@[expose] def ggL : ℕ → Equiv.Perm (Fin 4060) := fun l => ruLGens.getD l 1

@[expose] def lElt (w : List ℤ) : Equiv.Perm (Fin 4060) :=
  CFSG.Sporadic.Th.wordG (letterG ggL) w

@[expose] def sG : Equiv.Perm (Fin 4060) := lElt sWord

@[expose] def tG : Equiv.Perm (Fin 4060) := lElt tWord

@[expose] def bG : Equiv.Perm (Fin 4060) := lElt bWord

@[expose] def kG (w : String) : Equiv.Perm (Fin 4060) := wordProd (img2 sG tG) (parseW w)

theorem lGens_size : lGens.size = 3 := by
  simp [CFSG.EvenSporadicStandard.TwoRu.HypOne.lGens, ruLGensA_size]

section Reps


theorem rep_lTab {w : List ℤ} (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ lGens.size) :
    Rep 4060 (lTab w) (lElt w) ∧ lElt w ∈ ruL := by
  have hn : (4060 : ℕ) < 2 ^ 32 := by norm_num
  have hg := CFSG.EvenSporadicStandard.RuStd.lGens_rep
  have hl : ∀ z ∈ w, Rep 4060 (CFSG.EvenSporadicStandard.TwoRu.HypOne.letterTab lGens lGensInv z)
      (letterG ggL z) ∧ letterG ggL z ∈ ruL := by
    intro z hz
    obtain ⟨hz0, hzs⟩ := hw z hz
    by_cases hpos : 0 < z
    · obtain ⟨h1, -, h3⟩ := hg (z.toNat - 1) (by omega)
      simp only [CFSG.EvenSporadicStandard.TwoRu.HypOne.letterTab, letterG, hpos, ite_true]
      exact ⟨h1, h3⟩
    · obtain ⟨-, h2, h3⟩ := hg ((-z).toNat - 1) (by omega)
      simp only [CFSG.EvenSporadicStandard.TwoRu.HypOne.letterTab, letterG, hpos, ite_false]
      exact ⟨h2, ruL.inv_mem h3⟩
  exact ⟨CFSG.Sporadic.Th.Rep.wordT hn w fun z hz => (hl z hz).1,
    CFSG.EvenSporadicStandard.TwoRu.HypOne.wordG_mem _ fun z hz => (hl z hz).2⟩

end Reps

end CFSG.EvenSporadicStandard.Induction.RuSz

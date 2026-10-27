module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2BridgeData
public import CFSG.Certificates.Kernel.O8KronProved

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage1

theorem kronK_eq (rows : Array ℕ) : kronK rows = kron6K fun i => rows.getD i 0 := by
  apply kronK_eq_proved

theorem stage1Gens_getD (ε : Eps) {j : ℕ} (hj : j < 7) :
    (stage1Gens ε).getD j (0, 0) = if j = 0 then (phiK, phiK) else
      (kronK (genRows ε (j - 1)), kronK (genInvRows ε (j - 1))) := by
  rcases j with _ | j
  · simp [stage1Gens, Array.getD_eq_getD_getElem?]
  · simp [stage1Gens, Array.getD_eq_getD_getElem?, show j < 6 by omega]

theorem size_stage1Gens (ε : Eps) : (stage1Gens ε).size = 7 := by
  simp [stage1Gens]

theorem gensIn_of {gs : Array (ℕ × ℕ)} {E : Enum}
    (h : ∀ j < gs.size, memK E.keys (gs.getD j (0, 0)).1 = true) : gensIn gs E = true := by
  rw [gensIn, Array.all_eq_true]
  intro j hj
  have := h j hj
  rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some] at this

theorem bridgeCheck_of {ε : Eps} {cGens tGens : Array (ℕ × ℕ)} {cE tcE sE : Enum}
    (h1 : ∀ i < 6, memK cE.keys (kronK (genRows ε i)) = true)
    (h2 : enumOK (stage1Gens ε) sE = true) (h3 : gensIn cGens sE = true)
    (h4 : tGens.size = 7) (h5 : (tGens.getD 0 (0, 0)).1 = phiK)
    (h6 : ∀ k < 6, (tGens.getD (k + 1) (0, 0)).1 = kronK (urRows ε k) ∧
      memK tcE.keys (kronK (urRows ε k)) = true) :
    bridgeCheck ε cGens tGens cE tcE sE = true := by
  simp only [bridgeCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

end CFSG.KC.O8

end

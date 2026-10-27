module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Diag
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Levi

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRE7

open CFSG CFSG.Blueprint.Chevalley CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.Burgoyne.E2

@[expose] def leviGamma : List ((Fin (Tag.rank .E7) → ℤ) × ℤ) :=
  [(![1, 0, 0, 0, 0, 0, 0], 5), (![0, 1, 0, 0, 0, 0, 0], 4), (![0, 0, 1, 0, 0, 0, 0], -4),
    (![0, 0, 0, 1, 0, 0, 0], 5), (![0, 0, 0, 0, 1, 0, 0], -1), (![0, 0, 0, 0, 0, 1, 0], 2)]

theorem leviGamma_reg : ∀ α ∈ rootFinset .E7,
    (∑ j, regCoweight leviGamma j * α j) ≠ 0 ∧
      (∑ j, regCoweight leviGamma j * α j).natAbs < 19 := by
  decide +kernel

theorem leviGamma_mem : ∀ y ∈ leviGamma, ∃ k : Fin 6, y.1 = Pi.single (e7LeviE6Node k) 1 := by
  intro y hy
  simp only [leviGamma, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨1, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨2, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨3, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨4, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨5, by funext i; fin_cases i <;> rfl⟩

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRE7

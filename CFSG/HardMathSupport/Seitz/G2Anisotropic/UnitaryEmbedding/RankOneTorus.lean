module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.CubeTorsionRoots
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.GenerationEven
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog

variable {L : Type} [Field L]

theorem rootDiagUnit_cubeTuple3_zero_mem_v {ζ : Lˣ} (j : Fin 3) :
    ∃ C : SL2 L, rootDiagUnit .G2 (cubeTuple3 ζ 0 j) = rootSL2 .G2 L g2v C := by
  obtain ⟨tV, htV, hV⟩ := rootTorusSL2_tuple (L := L) isRoot_g2v (ζ ^ (j : ℕ))
  refine ⟨HSL (ζ ^ (j : ℕ)), ?_⟩
  show _ = rootTorusSL2 .G2 L g2v (ζ ^ (j : ℕ))
  rw [htV]
  congr 1
  have h0 : tV ⟨0, by decide⟩ = (ζ ^ (j : ℕ)) ^ (0 : ℤ) := by rw [hV]; congr 1
  have h1 : tV ⟨1, by decide⟩ = (ζ ^ (j : ℕ)) ^ (1 : ℤ) := by rw [hV]; congr 1
  funext i
  fin_cases i
  · show _ = tV ⟨0, _⟩
    rw [h0, zpow_zero]
    simp only [cubeTuple3, cubeTuple]
    show ζ ^ (((0 : Fin 3) : ℕ) : ℤ) = 1
    simp
  · show _ = tV ⟨1, _⟩
    rw [h1, zpow_one]
    simp only [cubeTuple3, cubeTuple]
    show ζ ^ ((j : ℕ) : ℤ) = _
    simp

theorem rootDiagUnit_cubeTuple3_diag_mem_a {ζ : Lˣ} (hζ : orderOf ζ = 3) (i : Fin 3) :
    ∃ C : SL2 L, rootDiagUnit .G2 (cubeTuple3 ζ i i) = rootSL2 .G2 L g2a C := by
  obtain ⟨tA, htA, hA⟩ := rootTorusSL2_tuple (L := L) isRoot_g2a (ζ ^ (2 * (i : ℤ)))
  refine ⟨HSL (ζ ^ (2 * (i : ℤ))), ?_⟩
  show _ = rootTorusSL2 .G2 L g2a (ζ ^ (2 * (i : ℤ)))
  rw [htA]
  congr 1
  have h0 : tA ⟨0, by decide⟩ = (ζ ^ (2 * (i : ℤ))) ^ (2 : ℤ) := by rw [hA]; congr 1
  have h1 : tA ⟨1, by decide⟩ = (ζ ^ (2 * (i : ℤ))) ^ (-1 : ℤ) := by rw [hA]; congr 1
  have hi := i.2
  have e0 : ζ ^ (((i : ℕ)) : ℤ) = (ζ ^ (2 * (i : ℤ))) ^ (2 : ℤ) := by
    rw [← zpow_mul, zpow_eq_zpow_iff_modEq, hζ]
    simp only [Int.ModEq, Nat.cast_ofNat]
    omega
  have e1 : ζ ^ (((i : ℕ)) : ℤ) = (ζ ^ (2 * (i : ℤ))) ^ (-1 : ℤ) := by
    rw [← zpow_mul, zpow_eq_zpow_iff_modEq, hζ]
    simp only [Int.ModEq, Nat.cast_ofNat]
    omega
  funext k
  fin_cases k
  · show _ = tA ⟨0, _⟩
    rw [h0, ← e0]
    simp only [cubeTuple3, cubeTuple]
    rfl
  · show _ = tA ⟨1, _⟩
    rw [h1, ← e1]
    simp only [cubeTuple3, cubeTuple]
    rfl

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

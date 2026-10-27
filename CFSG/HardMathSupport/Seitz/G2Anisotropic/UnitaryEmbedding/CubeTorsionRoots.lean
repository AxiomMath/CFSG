module

public import CFSG.Quasithin.Background.G2URoots
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation

public section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley CFSG.Quasithin.G2U

@[expose] def cubeExp (i j : ℤ) (α : Fin Tag.G2.rank → ℤ) : ℤ :=
  i * α ⟨0, by decide⟩ + j * α ⟨1, by decide⟩

@[expose] def cubeTuple {K : Type} [Field K] (ζ : Kˣ) (i j : ℤ) : Fin Tag.G2.rank → Kˣ :=
  ![ζ ^ i, ζ ^ j]

@[expose] def cubeTuple3 {K : Type} [Field K] (ζ : Kˣ) (i j : Fin 3) : Fin Tag.G2.rank → Kˣ :=
  cubeTuple ζ (i.val : ℤ) (j.val : ℤ)

variable {K : Type} [Field K]

theorem rootChar_cubeTuple (ζ : Kˣ) (i j : ℤ) (α : Fin Tag.G2.rank → ℤ) :
    rootChar (cubeTuple ζ i j) α = ζ ^ cubeExp i j α := by
  rw [rootChar]
  refine (Fin.prod_univ_two (fun k => cubeTuple ζ i j k ^ α k)).trans ?_
  show (ζ ^ i) ^ α ⟨0, by decide⟩ * (ζ ^ j) ^ α ⟨1, by decide⟩ = _
  rw [← zpow_mul, ← zpow_mul, ← zpow_add]
  rfl

theorem rootChar_cubeTuple_eq_one_iff {ζ : Kˣ} (hζ : orderOf ζ = 3) (i j : ℤ)
    (α : Fin Tag.G2.rank → ℤ) : rootChar (cubeTuple ζ i j) α = 1 ↔ (3 : ℤ) ∣ cubeExp i j α := by
  rw [rootChar_cubeTuple, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  rfl

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Chevalley.FoldedWeylData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.E6.RootLatticeTools

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6

set_option linter.unusedSectionVars false

@[expose] def S₂ : Set (Fin Tag.E6.rank → ℤ) :=
  {Pi.single (e6Index 2) 1, -Pi.single (e6Index 2) 1, Pi.single (e6Index 4) 1,
    -Pi.single (e6Index 4) 1}

@[expose] def S₀ : Set (Fin Tag.E6.rank → ℤ) :=
  {Pi.single (e6Index 0) 1, -Pi.single (e6Index 0) 1, Pi.single (e6Index 5) 1,
    -Pi.single (e6Index 5) 1}

@[expose] def ωwFold : List (Fin TwistTag.E6.foldedTag.rank) := [⟨0, by decide⟩, ⟨1, by decide⟩]

@[expose] def ωwWord : List (Fin Tag.E6.rank) := (ωwFold.map TwistTag.E6.orbitWord).flatten

theorem ωwWord_eq : ωwWord = [e6Index 0, e6Index 5, e6Index 2, e6Index 4] := by
  decide +kernel

section Aux


theorem ωw_smul_e0 :
    (coxeterSystem Tag.E6).wordProd ωwWord • (Pi.single (e6Index 0) 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single (e6Index 2) 1 := by
  simp only [ωwWord_eq, CoxeterSystem.wordProd, List.map, List.prod_cons, List.prod_nil, mul_smul,
    one_smul, simple_smul]
  decide +kernel

theorem ωw_smul_e5 :
    (coxeterSystem Tag.E6).wordProd ωwWord • (Pi.single (e6Index 5) 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single (e6Index 4) 1 := by
  simp only [ωwWord_eq, CoxeterSystem.wordProd, List.map, List.prod_cons, List.prod_nil, mul_smul,
    one_smul, simple_smul]
  decide +kernel

theorem ωw_inv_S₂ : ∀ γ ∈ S₂, IsRoot Tag.E6 γ ∧
    ((coxeterSystem Tag.E6).wordProd ωwWord)⁻¹ • γ ∈ S₀ := by
  have h0 : ((coxeterSystem Tag.E6).wordProd ωwWord)⁻¹ • (Pi.single (e6Index 2) 1 :
      Fin Tag.E6.rank → ℤ) = Pi.single (e6Index 0) 1 :=
    inv_smul_eq_iff.2 ωw_smul_e0.symm
  have h5 : ((coxeterSystem Tag.E6).wordProd ωwWord)⁻¹ • (Pi.single (e6Index 4) 1 :
      Fin Tag.E6.rank → ℤ) = Pi.single (e6Index 5) 1 :=
    inv_smul_eq_iff.2 ωw_smul_e5.symm
  intro γ hγ
  rcases hγ with rfl | rfl | rfl | rfl
  · exact ⟨isRoot_single _ _, by rw [h0]; exact Or.inl rfl⟩
  · exact ⟨isRoot_neg_single _ _, by rw [smul_neg, h0]; exact Or.inr (Or.inl rfl)⟩
  · exact ⟨isRoot_single _ _, by rw [h5]; exact Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨isRoot_neg_single _ _, by rw [smul_neg, h5]; exact Or.inr (Or.inr (Or.inr rfl))⟩

end Aux

end CFSG.HardMathSupport.Lang.AnisoE6

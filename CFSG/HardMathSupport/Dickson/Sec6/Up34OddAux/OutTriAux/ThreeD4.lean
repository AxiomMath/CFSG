module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.ThreeUnip
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.D4Normal

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.OutTri

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
  CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false

section ThreeD4


theorem noL34Layer_of_graphType_three {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) :
    NoL34Layer α := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
    exists_dual_fixEquiv hf K hK α hα3 g a hε hαeq
  haveI := TriD4Aux.finite_graphFixedRootGroup_D4 Fr
  haveI : CharP K₃ 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three (by omega) (by rw [hK₃, ← pow_mul, mul_comm] : Nat.card K₃ = 3 ^ (3 * f))
  exact noL34Layer_of_fixEquiv e (noL34Layer_three_D4_outer_three hf hK₃ Fr hFr φ hφ3 hφout)

theorem noL34Layer_adjointD4_outer_three (hO : LieOrderFormulasInput) {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 3 ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.D4 K)) :
    NoL34Layer α := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ := outer_cube_normal_form_cases α hα3 hα
  rcases hcase with ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩
  · subst hε0
    exact noL34Layer_of_fieldType hO (by norm_num) hf K hK α hα3 g a σ hσ3 hσ1 hαeq
  · exact noL34Layer_of_graphFieldType (by norm_num) hf K hK α hα3 g a σ ε hε hε0 hσ3 hσ1 hαeq
  · subst hσ1
    exact noL34Layer_of_graphType_three hf K hK α hα3 g a (by omega) hαeq

end ThreeD4

end CFSG.HardMathSupport.Dickson.Sec6.OutTri

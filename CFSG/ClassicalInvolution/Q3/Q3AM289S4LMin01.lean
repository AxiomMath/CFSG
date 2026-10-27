module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LSpin
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted QuadraticMap
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


theorem s4LinkModelLeafAt_minus4 : S4LinkModelLeafAt (CompData.model .POmegaMinus 4) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨hp, le_rfl, le_rfl⟩
  have hirr := minusCoeffs_irr 3 1
  have hn4 : 4 ≤ 4 := le_rfl
  have hM : modelUniv .POmegaMinus 4 3 1 hp =
      ⟨spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum 4 (minusCoeffs_irr 3 1)⟩ := rfl
  have hsingle : ModelFacts.FundamentalSingleClass .POmegaMinus
      (modelUniv .POmegaMinus 4 3 1 hp).D :=
    ModelFacts.fundamentalSingleClass .POmegaMinus 4 3 1 hp trivial hadm (by decide) (by decide)
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 3 1 hp).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaMinus)
      trivial hadm (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaMinus 4 3 1 hp).K :=
    ModelFacts.finite_modelUniv (t := .POmegaMinus) (by norm_num) hp trivial hadm
  show S4LinkModelLeafAt ⟨(modelUniv .POmegaMinus 4 3 1 hp).K,
    fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 3 1 hp).D⟩
  generalize modelUniv .POmegaMinus 4 3 1 hp = M at hM hsingle hsl2 hfin ⊢
  subst hM
  have : Finite (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) := hfin
  have hdim : Module.finrank 𝔽₃ (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → 𝔽₃) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have hconj : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1)),
      ∀ g : spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        conjSub g R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1)) := by
    rintro R ⟨g₀, γ, hγ, rfl⟩ g
    refine ⟨g * g₀, γ, hγ, ?_⟩
    change Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map (MulAut.conj g₀).toMonoidHom _) =
      _
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  exact S4L.s4LinkModelLeafAt_of_spin _ _ (nondegenerate_polarBilin_quadMinus_of_finite 4 𝔽₃ hirr)
    (by rw [hdim]; omega) (isPerfect_spinGroup_quadMinus hn4 hirr)
    (range_spinAction_quadMinus hn4 hirr) (Q3TY.centralQuot3_minus hadm) hconj hsingle hsl2
    (fun F₁ F₂ h => ModelFacts.TG3.hproj_minus hirr hn4 F₁ F₂ h)

end CFSG.ClassicalInvolution.Q3.Q3AM

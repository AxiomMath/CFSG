module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Transport
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transfer
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (nonempty_matrixProjective_equiv_adjointGroup)

set_option linter.unusedSectionVars false

section Model


theorem finite_adjointD4 (K : Type) [Field K] [Finite K] : Finite (adjointGroup Tag.D4 K) := by
  haveI : Finite (ModGL Tag.D4 K) := CFSG.LieType.Chevalley.finite_modGL
  infer_instance

theorem lieModel_adjointD4 {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (k : Type) [Field k] [Finite k]
    (hk : Nat.card k = ℓ ^ d) : LieModel (adjointGroup Tag.D4 k) .POmegaPlus 4 ℓ d := by
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup k
  exact (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mpr
    ⟨⟨hℓ, hd, le_rfl⟩, k, inferInstance, inferInstance, hk, ⟨e.symm⟩⟩

theorem isSimple_adjointD4 (k : Type) [Field k] [Finite k] :
    IsSimpleGroup (adjointGroup Tag.D4 k) ∧ ∃ a b : adjointGroup Tag.D4 k, a * b ≠ b * a := by
  obtain ⟨e⟩ := nonempty_matrixProjective_equiv_adjointGroup k
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus (K := k) (n := 4) (by norm_num)
  obtain ⟨hs, a, b, hab⟩ := matrix_simple_nonabelian (by norm_num) hnd hT
  haveI := hs
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

theorem not_typeL2_adjointD4 (hO : LieOrderFormulasInput) {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    (k : Type) [Field k] [Finite k] (hk : Nat.card k = ℓ ^ d) :
    ∀ r : ℕ, 10 ≤ r → ¬ IsTypeL2 r (adjointGroup Tag.D4 k) := by
  intro r hr
  obtain ⟨hs, hnab⟩ := isSimple_adjointD4 k
  exact not_typeL2_of_lieModel hO ⟨hℓ, hd, le_rfl⟩ (lieModel_adjointD4 hℓ hd k hk) (by decide)
    (by simp) (center_eq_bot_of_simple hnab) hr

end Model

theorem noL2Layer_of_fixSubgroup_eq {P : Type} [Group P] {β γ : MulAut P}
    (h : fixSubgroup β = fixSubgroup γ) (hγ : NoL2Layer γ) : NoL2Layer β := by
  unfold NoL2Layer at hγ ⊢
  rw [h]
  exact hγ

end CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux

module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairTwisted

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal
open scoped MatrixGroups

theorem fundPerfect_range_le_commutator {A X : Type} [Group A] [Group X] (hA : Group.IsPerfect A)
    (f : A →* X) : f.range ≤ ⁅f.range, f.range⁆ := by
  have h : ⁅(⊤ : Subgroup A), ⊤⁆ = ⊤ := hA.commutator_eq_top
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

theorem perfect_of_linearBlockStandardPair {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) {X : Type} [Group X] {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) : U ≤ ⁅U, U⁆ ∧ V ≤ ⁅V, V⁆ := by
  have hSL : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect h4
  obtain ⟨θ, c, -, -, hUV⟩ := h
  have key : ∀ (i : ℕ) (hi : i + 2 ≤ 3),
      ((blockSL F 3 2 i hi).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ ≤
        ⁅((blockSL F 3 2 i hi).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ,
          ((blockSL F 3 2 i hi).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ⁆ := by
    intro i hi
    rw [Subgroup.map_map, ← MonoidHom.range_comp]
    exact fundPerfect_range_le_commutator hSL _
  have h12 := key 0 (by omega)
  have h23 := key 1 (by omega)
  rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ h12, h2 ▸ h23⟩
  · exact ⟨h2 ▸ h23, h1 ▸ h12⟩

theorem fundPerfect_map_conj_le_commutator {X : Type*} [Group X] {R : Subgroup X}
    (h : R ≤ ⁅R, R⁆) (g : X) :
    R.map (MulAut.conj g).toMonoidHom ≤
      ⁅R.map (MulAut.conj g).toMonoidHom, R.map (MulAut.conj g).toMonoidHom⁆ := by
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono h

theorem fundPerfect_of_partner (t : StatedLieTag) (n p e : ℕ) [hp : Fact p.Prime]
    (hadm : StatedLieAdmissible t n p e) (h4 : 4 ≤ p ^ e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hpart : ∀ γ, IsLongestRoot (modelUniv t n p e hp.out).D γ → ∃ δ, ∃ W,
      LinearBlockStandardPair (GaloisField p e) W
        ((modelUniv t n p e hp.out).D.rootGroup γ ⊔ (modelUniv t n p e hp.out).D.rootGroup (-γ))
        ((modelUniv t n p e hp.out).D.rootGroup δ ⊔ (modelUniv t n p e hp.out).D.rootGroup (-δ))) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D, R ≤ ⁅R, R⁆ := by
  have h4' : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact h4
  rintro R ⟨g, γ, hγ, rfl⟩
  have hγ' : IsLongestRoot (modelUniv t n p e hp.out).D γ := by
    rcases hγ with h | ⟨ht, -⟩ | ⟨ht, -⟩
    · exact h
    · exact absurd ht hG2
    · exact absurd ht hD4
  obtain ⟨δ, W, hW⟩ := hpart γ hγ'
  exact fundPerfect_map_conj_le_commutator (perfect_of_linearBlockStandardPair h4' hW).1 g

section Tags

variable (n p e : ℕ) [hp : Fact p.Prime] (h4 : 4 ≤ p ^ e)
include h4

theorem fundPerfect_PSL (hadm : StatedLieAdmissible .PSL n p e) (hn : 3 ≤ n) :
    ∀ R ∈ fundamentalSubgroups .PSL (modelUniv .PSL n p e hp.out).D, R ≤ ⁅R, R⁆ :=
  fundPerfect_of_partner .PSL n p e hadm h4 (by simp) (by simp) fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_PSL n p e hadm hn hγ
    exact ⟨δ, W, hW⟩

theorem fundPerfect_POmegaPlus (hadm : StatedLieAdmissible .POmegaPlus n p e) :
    ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p e hp.out).D, R ≤ ⁅R, R⁆ :=
  fundPerfect_of_partner .POmegaPlus n p e hadm h4 (by simp) (by simp) fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_POmegaPlus p e n hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundPerfect_POmegaOdd (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n p e hp.out).D, R ≤ ⁅R, R⁆ :=
  fundPerfect_of_partner .POmegaOdd n p e hadm h4 (by simp) (by simp) fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_POmegaOdd p e n hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundPerfect_POmegaMinus (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p e hp.out).D,
      R ≤ ⁅R, R⁆ :=
  fundPerfect_of_partner .POmegaMinus n p e hadm h4 (by simp) (by simp) fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_POmegaMinus n p e hp2 hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundPerfect_E6 (hadm : StatedLieAdmissible .E6 0 p e) :
    ∀ R ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 p e hp.out).D, R ≤ ⁅R, R⁆ :=
  fundPerfect_of_partner .E6 0 p e hadm h4 (by simp) (by simp) fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_E6 p e hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundPerfect_E7 (hadm : StatedLieAdmissible .E7 0 p e) :
    ∀ R ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p e hp.out).D, R ≤ ⁅R, R⁆ :=
  fundPerfect_of_partner .E7 0 p e hadm h4 (by simp) (by simp) fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_E7 p e hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundPerfect_E8 (hadm : StatedLieAdmissible .E8 0 p e) :
    ∀ R ∈ fundamentalSubgroups .E8 (modelUniv .E8 0 p e hp.out).D, R ≤ ⁅R, R⁆ :=
  fundPerfect_of_partner .E8 0 p e hadm h4 (by simp) (by simp) fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_E8 p e hadm hγ
    exact ⟨δ, W, hW⟩

theorem fundPerfect_F4 (hadm : StatedLieAdmissible .F4 0 p e) :
    ∀ R ∈ fundamentalSubgroups .F4 (modelUniv .F4 0 p e hp.out).D, R ≤ ⁅R, R⁆ :=
  fundPerfect_of_partner .F4 0 p e hadm h4 (by simp) (by simp) fun γ hγ => by
    obtain ⟨δ, -, -, W, hW⟩ := exists_standardPair_partner_F4 p e hadm hγ
    exact ⟨δ, W, hW⟩

end Tags

end CFSG.ClassicalInvolution.ModelFacts

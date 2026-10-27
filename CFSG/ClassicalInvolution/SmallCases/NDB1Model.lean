module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpStd
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpAlg

public section

namespace CFSG.ClassicalInvolution.NDB

structure PSpPair {M : Type*} [Group M] (𝓕 : Set (Subgroup M)) (R₂ R₃ : Subgroup M) (τ₂ τ₃ : M) :
    Prop where
  mem₂ : R₂ ∈ 𝓕
  mem₃ : R₃ ∈ 𝓕
  hτ₂ : τ₂ ∈ R₂
  hτ₃ : τ₃ ∈ R₃
  ne₂ : τ₂ ≠ 1
  ne₃ : τ₃ ≠ 1
  sq₂ : τ₂ * τ₂ = 1
  sq₃ : τ₃ * τ₃ = 1
  comm : ∀ a ∈ R₂, ∀ b ∈ R₃, a * b = b * a
  center : ∀ c ∈ Subgroup.center M, c = 1 ∨ c = τ₂ * τ₃
  perfect : Group.IsPerfect M

namespace Model

open CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem longInv_ne_one (h2 : (2 : F) ≠ 0) (k : Fin 2) : longInv F 2 k ≠ 1 := by
  intro h
  have h1 : longBlock F 2 k (-1) = longBlock F 2 k 1 := by
    rw [map_one]
    exact h
  have h3 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0)
    (longBlock_injective k h1)
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at h3
  exact h2 (by linear_combination -h3)

theorem longInv_sq (k : Fin 2) : longInv F 2 k * longInv F 2 k = 1 := by
  rw [longInv, ← map_mul, neg_mul_neg, mul_one, map_one]

theorem center_eq {c : StatedSp 2 F}
    (hc : c ∈ Subgroup.center (StatedSp 2 F)) : c = 1 ∨ c = longInv F 2 0 * longInv F 2 1 := by
  obtain ⟨u, hu⟩ := Models.SymplecticPairs.exists_scalar_of_mem_center hc
  have hcc := mul_self_eq_one_of_mem_center (by norm_num : 1 ≤ 2) hc
  have hmat : mat 2 F c = Matrix.scalar _ (u : F) := by
    rw [mat_apply, hu, Matrix.GeneralLinearGroup.coe_scalar]
  have huu : (u : F) * u = 1 := by
    have h1 := congrArg (mat 2 F) hcc
    rw [map_mul, map_one, hmat, ← map_mul] at h1
    exact (Matrix.scalar_inj (n := Fin 2 ⊕ Fin 2)).mp (h1.trans (map_one _).symm)
  rcases mul_self_eq_one_iff.mp huu with h | h
  · left
    apply mat_injective
    rw [hmat, h, map_one, map_one]
  · right
    have hz : c = zneg F := by
      apply mat_injective
      rw [hmat, h, mat_zneg, map_neg, map_one]
    rw [hz]
    calc zneg F = zneg F * x0 F * x0 F := by rw [mul_assoc, x0_mul_self, mul_one]
      _ = longInv F 2 1 * longInv F 2 0 := by rw [zneg_mul_x0_eq_longInv]; rfl
      _ = longInv F 2 0 * longInv F 2 1 := (longBlock_comm (-1) (-1)).symm

theorem pspPair_sp [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    PSpPair {R | ∃ P, IsHyperbolicPlane P ∧ R = planeGroup P} (longBlock F 2 0).range
      (longBlock F 2 1).range (longInv F 2 0) (longInv F 2 1) where
  mem₂ := (exists_conj_longBlock_iff 0 _).mp ⟨1, by rw [map_one]; exact Subgroup.map_id _ |>.symm⟩
  mem₃ := (exists_conj_longBlock_iff 1 _).mp ⟨1, by rw [map_one]; exact Subgroup.map_id _ |>.symm⟩
  hτ₂ := ⟨-1, rfl⟩
  hτ₃ := ⟨-1, rfl⟩
  ne₂ := longInv_ne_one h2 0
  ne₃ := longInv_ne_one h2 1
  sq₂ := longInv_sq 0
  sq₃ := longInv_sq 1
  comm := fun _ ha _ hb => R0_comm_R0' ha hb
  center := fun _ hc => center_eq hc
  perfect := isPerfect_statedSp_of_four_le h4

end Model

open CFSG.Assembly.LowTwoRank

theorem exists_pspPair_model {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (t : StatedLieTag) (n e : ℕ)
    (ht : t = .PSp) (hn : n = 2) (hadm : StatedLieAdmissible t n p e) (h4 : 4 ≤ p ^ e) :
    ∃ (R₂ R₃ : Subgroup (Generic.modelUniv t n p e Fact.out).K)
      (τ₂ τ₃ : (Generic.modelUniv t n p e Fact.out).K),
      PSpPair (Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D) R₂ R₃ τ₂
        τ₃ := by
  subst ht hn
  have he : e ≠ 0 := by
    rintro rfl
    simp at h4
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hcard : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    exact h4
  have hset : Generic.fundamentalSubgroups .PSp (Generic.modelUniv .PSp 2 p e Fact.out).D =
      {R | ∃ P, Models.SymplecticPairs.IsHyperbolicPlane P ∧
        R = Models.SymplecticPairs.planeGroup P} :=
    Set.ext fun R => Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hadm R
  refine ⟨(Models.SymplecticPairs.longBlock (GaloisField p e) 2 0).range,
    (Models.SymplecticPairs.longBlock (GaloisField p e) 2 1).range,
    Models.SymplecticPairs.longInv (GaloisField p e) 2 0,
    Models.SymplecticPairs.longInv (GaloisField p e) 2 1, ?_⟩
  rw [hset]
  exact Model.pspPair_sp h2 hcard

end CFSG.ClassicalInvolution.NDB

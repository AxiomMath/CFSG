module

public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.ClassicalInvolution.Phan.CenterScalars

public section

namespace CFSG.ClassicalInvolution.Phan

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary

section Scalar

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_scalar_of_mem_center (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n) {z : SUid σ n}
    (hz : z ∈ Subgroup.center (SUid σ n)) :
    ∃ u : Kˣ, ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) (u : K) := by
  rw [center_SUid_eq hσ hn, Subgroup.mem_subgroupOf, CFSG.Assembly.LowTwoRank.StatedScalars,
    MonoidHom.mem_range] at hz
  obtain ⟨u, hu⟩ := hz
  exact ⟨u, by rw [← hu, Matrix.GeneralLinearGroup.coe_scalar]⟩

theorem scalar_eq_one_of_apply_eq_one {m : ℕ} {u : K} {c : Fin m}
    {M : Matrix (Fin m) (Fin m) K} (hM : M = Matrix.scalar (Fin m) u) (hc : M c c = 1) :
    M = 1 := by
  rw [hM, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hc
  rw [hM, hc]
  ext a b
  simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

end Scalar

section Blocks

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem eq_one_of_blockEmb_mem_center (hK : Nat.card K = (p ^ f) ^ 2) {m k i : ℕ}
    (h : i + k ≤ m) (hk : k < m) (hm : 3 ≤ m) {g : Su K p f k}
    (hg : blockEmb K p f m k i h g ∈ Subgroup.center (Su K p f m)) : g = 1 := by
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center (isUnitaryInvolution_unitaryInvolution hK) hm hg
  obtain ⟨c, hc⟩ : ∃ c : Fin m, ¬ (i ≤ c.val ∧ c.val < i + k) := by
    by_cases hi : 0 < i
    · exact ⟨⟨0, by omega⟩, fun h' => by have h1 := h'.1; dsimp only at h1; omega⟩
    · exact ⟨⟨k, hk⟩, fun h' => by have h1 := h'.2; dsimp only at h1; omega⟩
  have h1 : (((blockEmb K p f m k i h g : Su K p f m) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
      c c = 1 := by
    rw [coe_coe_blockEmb, blockMat_apply_of_not_mem_left _ hc, Matrix.one_apply_eq]
  have h2 := scalar_eq_one_of_apply_eq_one hu h1
  refine blockEmb_injective h ?_
  rw [map_one]
  exact Subtype.ext (Units.ext h2)

theorem center_inf_range_blockEmb (hK : Nat.card K = (p ^ f) ^ 2) {m k i : ℕ} (h : i + k ≤ m)
    (hk : k < m) (hm : 3 ≤ m) :
    Subgroup.center (Su K p f m) ⊓ (blockEmb K p f m k i h).range = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨hz, g, rfl⟩
  rw [Subgroup.mem_bot]
  rw [eq_one_of_blockEmb_mem_center hK h hk hm hz, map_one]

theorem comp_blockEmb_injective (hK : Nat.card K = (p ^ f) ^ 2) {X : Type*} [Group X] {m k i : ℕ}
    {θ : Su K p f m →* X} (hθ : θ.ker ≤ Subgroup.center (Su K p f m)) (h : i + k ≤ m) (hk : k < m)
    (hm : 3 ≤ m) : Function.Injective (θ.comp (blockEmb K p f m k i h)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact eq_one_of_blockEmb_mem_center hK h hk hm (hθ hg)

theorem eq_one_of_embSUid_mem_center (hK : Nat.card K = (p ^ f) ^ 2) (c : Fin 3) {A : Su K p f 2}
    (hA : embSUid (unitaryInvolution K p f) c A ∈ Subgroup.center (Su K p f 3)) : A = 1 := by
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center (isUnitaryInvolution_unitaryInvolution hK)
    (le_refl 3) hA
  have h1 : (((embSUid (unitaryInvolution K p f) c A : Su K p f 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) c c = 1 := by
    rw [coe_embSUid]
    fin_cases c <;> simp [embPair]
  have h2 := scalar_eq_one_of_apply_eq_one hu h1
  refine embSUid_injective _ c ?_
  rw [map_one]
  exact Subtype.ext (Units.ext h2)

theorem comp_embSUid_injective (hK : Nat.card K = (p ^ f) ^ 2) {X : Type*} [Group X]
    {θ : Su K p f 3 →* X} (hθ : θ.ker ≤ Subgroup.center (Su K p f 3)) (c : Fin 3) :
    Function.Injective (θ.comp (embSUid (unitaryInvolution K p f) c)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  exact eq_one_of_embSUid_mem_center hK c (hθ hA)

end Blocks

end CFSG.ClassicalInvolution.Phan

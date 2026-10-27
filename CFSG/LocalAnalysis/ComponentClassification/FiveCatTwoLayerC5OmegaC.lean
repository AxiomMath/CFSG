module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5OmegaProd
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5Basic

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.TwoL5.Omega

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.SolMax.FiveCat.C5PSL (eq_psl_two_one_of_a5)
open CFSG.ComponentClassification.SolMax.FiveCat.C5Omega (le_four_of_modelIn_orthTuples)
open scoped MatrixGroups

section Split

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourSplit

theorem specialRho_neg_one_one_ne_one {K : Type} [Field K] (h2 : (2 : K) ≠ 0) :
    (specialRho (K := K)).comp (MonoidHom.inl _ _) (-1) ≠ 1 := by
  haveI : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  intro h
  have h1 := congrArg (fun g : DeterminantIsometries K =>
    g.val (1 : Matrix (Fin 2) (Fin 2) K)) h
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, specialRho_apply] at h1
  simp at h1
  have h3 := congrFun (congrFun h1 0) 0
  simp at h3
  apply h2
  linear_combination -h3

theorem specialRho_one_neg_one_ne_one {K : Type} [Field K] (h2 : (2 : K) ≠ 0) :
    (specialRho (K := K)).comp (MonoidHom.inr _ _) (-1) ≠ 1 := by
  haveI : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  intro h
  have h1 := congrArg (fun g : DeterminantIsometries K =>
    g.val (1 : Matrix (Fin 2) (Fin 2) K)) h
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, specialRho_apply] at h1
  simp at h1
  have h3 := congrFun (congrFun h1 0) 0
  simp at h3
  apply h2
  linear_combination -h3

theorem neg_one_mem_center_SL {K : Type} [Field K] :
    (-1 : SL(2, K)) ∈ center SL(2, K) := by
  haveI : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by norm_num, ?_⟩
  ext i j
  by_cases hij : i = j <;>
    simp [hij, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem exists_central_involution_of_neg_one {K : Type} [Field K] {H G : Type} [Group H] [Group G]
    (g : SL(2, K) →* H) (e : H ≃* G) (hne : g (-1) ≠ 1) :
    ∃ z ∈ g.range.map e.toMonoidHom, (∀ y ∈ g.range.map e.toMonoidHom, z * y = y * z) ∧
      z * z = 1 ∧ z ≠ 1 := by
  haveI : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  refine ⟨e (g (-1)), Subgroup.mem_map.2 ⟨g (-1), ⟨-1, rfl⟩, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    change e (g (-1)) * e (g t) = e (g t) * e (g (-1))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
      (Subgroup.mem_center_iff.mp (neg_one_mem_center_SL (K := K)) t).symm]
  · rw [← map_mul, ← map_mul, neg_one_mul, neg_neg, map_one, map_one]
  · intro h1
    exact hne (e.injective (by rw [h1, map_one]))

open CatLeafProof in
theorem exists_central_involution_split_four {K W : Type} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3)
    (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    ∃ z ∈ M, (∀ y ∈ M, z * y = y * z) ∧ z * z = 1 ∧ z ≠ 1 := by
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, -, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hdim hS
  have hMD : M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    calc M = ⁅M, M⁆ := (Subgroup.isPerfect_iff.mp hM.1.1).symm
      _ ≤ commutator _ := Subgroup.commutator_mono le_top le_top
  rcases eq_or_eq_of_isComponent_le_sup hsup hq₁ hq₂ hn₁ hn₂ hM hMD with h | h
  · rw [h]
    exact exists_central_involution_of_neg_one ((specialRho (K := K)).comp (MonoidHom.inl _ _))
      e'.symm (specialRho_neg_one_one_ne_one h2)
  · rw [h]
    exact exists_central_involution_of_neg_one ((specialRho (K := K)).comp (MonoidHom.inr _ _))
      e'.symm (specialRho_one_neg_one_ne_one h2)

end Split

section Orthogonal

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem finrank_eq_three_of_litLayer {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : LitLayer M) :
    Module.finrank K W = 3 ∧ M = commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  obtain ⟨hcomp, hA, hz⟩ := hM
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (Nat.prime_five.odd_of_ne_two (by norm_num)).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  have hK3 : Nat.card K ≠ 3 := by
    intro h3
    have h5 : 5 ∣ Nat.card K := by
      rw [hK]
      exact dvd_pow_self 5 (by omega)
    rw [h3] at h5
    omega
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have h3 : 3 ≤ Module.finrank K W := by
    by_contra hlt
    have hsol : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
      ((CatalogueBOrthogonalAssembly.odd_orthogonal_all_dimensional_isometry_p_components hodd Q
        hQ).2 (by omega)).1
    exact LocalAnalysis.ComponentInitial.not_isComponent_of_isSolvable _ hcomp
  have hmodel := orthogonal_component_models Nat.prime_five (by norm_num) hf hK Q hQ h3 hcomp
  obtain ⟨hd4, -⟩ := le_four_of_modelIn_orthTuples hmodel hA
  rcases (show Module.finrank K W = 3 ∨ Module.finrank K W = 4 by omega) with hd | hd
  · obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ :=
      LocalAnalysis.ComponentInitial.orthogonal_three_derived hodd hK3 Q hQ hd
    exact ⟨hd, CatLeafProof.eq_commutator_of_isComponent hq hcomp⟩
  · exfalso
    by_cases hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
    · obtain ⟨z, hzM, hzc, hzz, hz1⟩ :=
        exists_central_involution_split_four hK2 hK3 h2 Q hQ hd hS hcomp
      exact hz1 (hz z hzM hzc hzz)
    · have hmodel' := centralModel_orthogonal_nonsplit_four Nat.prime_five (by norm_num) hf hK Q
        hQ hd hS hcomp
      obtain ⟨-, -, h3'⟩ := eq_psl_two_one_of_a5 (Or.inl rfl) hmodel'.1 hmodel'.2 hA
      omega

end Orthogonal

end CFSG.ComponentClassification.SolMax.FiveCat.TwoL5.Omega

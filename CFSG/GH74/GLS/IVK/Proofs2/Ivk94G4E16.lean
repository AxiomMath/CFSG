module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExSp
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem exists_E16_of_commuting_involutions {G : Type*} [Group G] (u : Fin 4 → G)
    (hsq : ∀ i, u i ^ 2 = 1) (hcomm : ∀ i j, Commute (u i) (u j))
    (hker : ∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1) :
    ∃ E : Subgroup G, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  obtain ⟨f, hf⟩ := CFSG.GH74.Filter.exists_injective_of_commuting_involutions u hsq hcomm hker
  refine ⟨f.range, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := by
      funext i
      rw [Pi.pow_apply, Pi.one_apply]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      generalize Multiplicative.toAdd (a i) = z
      revert z
      decide
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm,
      CFSG.GH74.Filter.card_pi_zmod_two]
    norm_num

theorem exists_E16_quotient {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g : Fin 4 → G)
    (hsq : ∀ i, g i ^ 2 ∈ N) (hcomm : ∀ i j, ⁅g i, g j⁆ ∈ N)
    (hind : ∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => g i ^ (a i : ℕ)).prod ∉ N) :
    ∃ E : Subgroup (G ⧸ N), (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  refine exists_E16_of_commuting_involutions (fun i => (QuotientGroup.mk (g i) : G ⧸ N)) ?_ ?_ ?_
  · intro i
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hsq i
  · intro i j
    show (QuotientGroup.mk (g i) : G ⧸ N) * QuotientGroup.mk (g j) =
      QuotientGroup.mk (g j) * QuotientGroup.mk (g i)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 := (inferInstance : N.Normal).conj_mem _ (N.inv_mem (hcomm i j)) (g i * g j)⁻¹
    have h2 : (g i * g j)⁻¹ * ⁅g i, g j⁆⁻¹ * ((g i * g j)⁻¹)⁻¹ = (g i * g j)⁻¹ * (g j * g i) := by
      simp only [commutatorElement_def]
      group
    rwa [h2] at h1
  · intro a ha hprod
    apply hind a ha
    have h1 : (List.ofFn fun i => (QuotientGroup.mk (g i) : G ⧸ N) ^ (a i : ℕ)).prod =
        QuotientGroup.mk' N (List.ofFn fun i => g i ^ (a i : ℕ)).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [h1] at hprod
    exact (QuotientGroup.eq_one_iff _).1 hprod

theorem mem_statedScalars_of_matrix {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type}
    [Field K] {A : GL ι K} {c : K} (h : (A : Matrix ι ι K) = c • (1 : Matrix ι ι K)) :
    A ∈ StatedScalars ι K := by
  have hc : c ≠ 0 := by
    rintro rfl
    have h1 : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h, zero_smul, zero_mul] at h1
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := congrFun (congrFun h1 i) i
    simp at this
  refine ⟨Units.mk0 c hc, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

theorem matrix_of_mem_statedScalars {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {A : GL ι K} (h : A ∈ StatedScalars ι K) : ∃ c : K, (A : Matrix ι ι K) = c • (1 : Matrix ι ι K) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨u, ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

theorem exists_E16_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type}
    [Field K] {H : Subgroup (GL ι K)} (g : Fin 4 → GL ι K) (hH : ∀ i, g i ∈ H)
    (hsq : ∀ i, ∃ c : K, (g i : Matrix ι ι K) * (g i : Matrix ι ι K) = c • (1 : Matrix ι ι K))
    (hcomm : ∀ i j, ∃ c : K, (g i : Matrix ι ι K) * (g j : Matrix ι ι K) =
      c • ((g j : Matrix ι ι K) * (g i : Matrix ι ι K)))
    (hind : ∀ a : Fin 4 → Fin 2, a ≠ 0 → ∀ c : K,
      ((List.ofFn fun i => g i ^ (a i : ℕ)).prod : Matrix ι ι K) ≠ c • (1 : Matrix ι ι K)) :
    ∃ E : Subgroup (StatedProj H), (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  let g' : Fin 4 → ↥H := fun i => ⟨g i, hH i⟩
  refine exists_E16_quotient ((StatedScalars ι K).subgroupOf H) g' ?_ ?_ ?_
  · intro i
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨c, hc⟩ := hsq i
    refine mem_statedScalars_of_matrix (c := c) ?_
    show (((g i) ^ 2 : GL ι K) : Matrix ι ι K) = _
    rw [pow_two, Units.val_mul]
    exact hc
  · intro i j
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨c, hc⟩ := hcomm i j
    refine mem_statedScalars_of_matrix (c := c) ?_
    show ((g i * g j * (g i)⁻¹ * (g j)⁻¹ : GL ι K) : Matrix ι ι K) = _
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hc, smul_mul_assoc, smul_mul_assoc]
    congr 1
    calc (g j : Matrix ι ι K) * (g i : Matrix ι ι K) * ((g i)⁻¹ : GL ι K) * ((g j)⁻¹ : GL ι K)
        = (g j : Matrix ι ι K) * ((g i : Matrix ι ι K) * ((g i)⁻¹ : GL ι K)) *
            ((g j)⁻¹ : GL ι K) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, Units.mul_inv]
  · intro a ha hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨c, hc⟩ := matrix_of_mem_statedScalars hmem
    apply hind a ha c
    have key : ((((List.ofFn fun i => g' i ^ (a i : ℕ)).prod : ↥H)) : GL ι K) =
        (List.ofFn fun i => g i ^ (a i : ℕ)).prod := by
      have h := map_list_prod H.subtype (List.ofFn fun i => g' i ^ (a i : ℕ))
      rw [List.map_ofFn] at h
      exact h
    rw [← key]
    exact hc

theorem k94Excl_of_E16 {P : (K : Type) → [Group K] → Prop}
    (hP : ∀ (K : Type) [Group K] [Finite K], P K →
      ∃ E : Subgroup K, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16) : K94Excl P := by
  intro K _ _ hs hnab hgen htwo hPK z I₁ I₂ F₁ F₂ _ _ _ _ cfg
  obtain ⟨E, hE2, hcard⟩ := hP K hPK
  exact false_of_E16 htwo E hE2 hcard

@[expose] def involGL {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (M : Matrix ι ι F) (h : M * M = 1) : GL ι F :=
  ⟨M, M, h, h⟩

@[simp] theorem coe_involGL {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (M : Matrix ι ι F) (h : M * M = 1) : ((involGL M h : GL ι F) : Matrix ι ι F) = M := rfl

theorem exists_E16_of_equiv {K G : Type} [Group K] [Group G] (e : K ≃* G)
    (h : ∃ E : Subgroup G, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16) :
    ∃ E : Subgroup K, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  obtain ⟨E, hE2, hcard⟩ := h
  refine ⟨E.map e.symm.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hcard]

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94

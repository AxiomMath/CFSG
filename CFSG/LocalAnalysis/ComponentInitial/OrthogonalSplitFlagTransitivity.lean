module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitRootData
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule

section Defs

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def singularFlags (Q : QuadraticForm K V) (k : ℕ) : Set (Fin k → Submodule K V) :=
  {W | (∀ i, finrank K (W i) = i + 1) ∧ Monotone W ∧ ∀ i, ∀ x ∈ W i, Q x = 0}

@[expose] def singularSubspaces (Q : QuadraticForm K V) (k : ℕ) : Set (Submodule K V) :=
  {X | finrank K X = k ∧ ∀ x ∈ X, Q x = 0}

theorem mem_singularFlags {Q : QuadraticForm K V} {k : ℕ} {W : Fin k → Submodule K V} :
    W ∈ singularFlags Q k ↔
      (∀ i, finrank K (W i) = i + 1) ∧ Monotone W ∧ ∀ i, ∀ x ∈ W i, Q x = 0 :=
  Iff.rfl

theorem mem_singularSubspaces {Q : QuadraticForm K V} {k : ℕ} {X : Submodule K V} :
    X ∈ singularSubspaces Q k ↔ finrank K X = k ∧ ∀ x ∈ X, Q x = 0 :=
  Iff.rfl

@[expose] def natFlag {k : ℕ} (W : Fin k → Submodule K V) (i : ℕ) : Submodule K V :=
  if h : 0 < i ∧ i ≤ k then W ⟨i - 1, by omega⟩ else ⊥

theorem natFlag_succ {k : ℕ} (W : Fin k → Submodule K V) (i : Fin k) :
    natFlag W (i + 1) = W i := by
  rw [natFlag, dite_eq_left ⟨by omega, by omega⟩]
  congr 1

theorem natFlag_zero {k : ℕ} (W : Fin k → Submodule K V) : natFlag W 0 = ⊥ := by
  rw [natFlag, dite_eq_right (by omega)]

theorem natFlag_of_pos {k : ℕ} (W : Fin k → Submodule K V) {i : ℕ} (hi : 0 < i) (hik : i ≤ k) :
    natFlag W i = W ⟨i - 1, by omega⟩ := by
  rw [natFlag, dite_eq_left ⟨hi, hik⟩]

theorem natFlag_of_not_pos {k : ℕ} (W : Fin k → Submodule K V) {i : ℕ} (hi : ¬0 < i) :
    natFlag W i = ⊥ := by
  rw [natFlag, dite_eq_right fun h => hi h.1]

theorem exists_mem_singularFlags_eq [FiniteDimensional K V] {Q : QuadraticForm K V} {k : ℕ}
    {X : Submodule K V} (hX : X ∈ singularSubspaces Q k) (hk : 0 < k) :
    ∃ W ∈ singularFlags Q k, W ⟨k - 1, by omega⟩ = X := by
  obtain ⟨hXk, hXs⟩ := hX
  set u : Basis (Fin k) K X := Module.finBasisOfFinrankEq K X hXk
  have hli : LinearIndependent K (fun j : Fin k => (u j : V)) :=
    u.linearIndependent.map' X.subtype (ker_subtype X)
  set W : Fin k → Submodule K V := fun i =>
    span K ((fun j : Fin k => (u j : V)) '' {j | (j : ℕ) < i.val + 1}) with hW
  have hWX : ∀ i, W i ≤ X := fun i => span_le.2 (by rintro _ ⟨j, -, rfl⟩; exact (u j).2)
  have hWd : ∀ i, finrank K (W i) = i + 1 := fun i =>
    SymplecticFlag.finrank_span_image_lt hli (by omega)
  refine ⟨W, ⟨hWd, fun i j hij => span_mono (Set.image_mono fun l (hl : (l : ℕ) < i.val + 1) =>
    show (l : ℕ) < j.val + 1 by have := Fin.le_def.1 hij; omega), fun i x hx => hXs x (hWX i hx)⟩,
    eq_of_le_of_finrank_eq (hWX _) ?_⟩
  rw [hWd, hXk]
  simp only
  omega

end Defs

section Standard

variable {r : ℕ} {K : Type*} [Field K]

theorem finrank_split : finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]

theorem flag_eq_span_basisFun (i : ℕ) :
    flag r K i =
      span K (Pi.basisFun K (Fin r ⊕ Fin r) '' (Sum.inl '' {j : Fin r | (j : ℕ) < i})) := by
  rw [flag, ← Set.image_comp]
  congr 2
  funext j
  rw [Function.comp_apply, Pi.basisFun_apply]

theorem flag_zero : flag r K 0 = ⊥ := by
  rw [flag, span_eq_bot]
  rintro _ ⟨j, hj, rfl⟩
  exact absurd hj (Nat.not_lt_zero _)

theorem finrank_flag {i : ℕ} (hi : i ≤ r) : finrank K (flag r K i) = i := by
  rw [flag_eq_span_basisFun]
  exact SymplecticFlag.finrank_span_inl_image _ hi

theorem quadPlus_eq_zero_of_mem_flag {i : ℕ} {x : Fin r ⊕ Fin r → K} (hx : x ∈ flag r K i) :
    quadPlus r K x = 0 :=
  map_eq_zero_of_mem_span (by rintro _ ⟨j, -, rfl⟩; exact quadPlus_single _)
    (by rintro _ ⟨j, -, rfl⟩ _ ⟨l, -, rfl⟩; exact polar_single_single (by simp)) hx

theorem flag_mem_singularSubspaces {i : ℕ} (hi : i ≤ r) :
    flag r K i ∈ singularSubspaces (quadPlus r K) i :=
  ⟨finrank_flag hi, fun _ hx => quadPlus_eq_zero_of_mem_flag hx⟩

theorem map_mul_linearEquiv {M : Type*} [AddCommGroup M] [Module K M] (g h : M ≃ₗ[K] M)
    (W : Submodule K M) :
    W.map ((g * h : M ≃ₗ[K] M) : M →ₗ[K] M) = (W.map (h : M →ₗ[K] M)).map (g : M →ₗ[K] M) := by
  rw [← Submodule.map_comp]
  rfl

end Standard

section Orthogonal

variable {r : ℕ} {K : Type*} [Field K]

theorem exists_isometry_map_flag_eq {k : ℕ} (hk : k ≤ r)
    {W : Fin k → Submodule K (Fin r ⊕ Fin r → K)} (hW : W ∈ singularFlags (quadPlus r K) k) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K),
      ∀ i : Fin k,
        (flag r K (i + 1)).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = W i := by
  obtain ⟨hWd, hWm, hWs⟩ := hW
  have hd : ∀ i ≤ k, finrank K (natFlag W i) = i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [natFlag_zero, finrank_bot]
    · rw [natFlag_of_pos W hi0 hi, hWd]
      simp only
      omega
  have hm : ∀ i < k, natFlag W i ≤ natFlag W (i + 1) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [natFlag_zero]
      exact bot_le
    · rw [natFlag_of_pos W hi0 hi.le, natFlag_of_pos W (by omega) hi]
      exact hWm (Fin.le_def.2 (by simp only; omega))
  have hs : ∀ x ∈ natFlag W k, quadPlus r K x = 0 := by
    intro x hx
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [natFlag_of_not_pos W (by omega), mem_bot] at hx
      rw [hx, map_zero]
    · rw [natFlag_of_pos W hk0 le_rfl] at hx
      exact hWs _ x hx
  obtain ⟨b, -, -, -, hbW, hbQ⟩ := (orthogonal_geometry_split_Witt_flags
    (nondegenerate_polarBilin_quadPlus r K) finrank_split
    ⟨flag r K r, finrank_flag le_rfl, fun _ hx => quadPlus_eq_zero_of_mem_flag hx⟩).1 k hk
    (natFlag W) hd hm hs
  refine ⟨b.equivFun.symm, ?_, fun i => ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [Basis.equivFun_symm_apply, Fintype.sum_sum_type, hbQ, quadPlus_apply]
  · rw [flag_eq_span_basisFun, Submodule.map_span, ← natFlag_succ W i, hbW (i + 1) (by omega),
      ← Set.image_comp]
    congr 1
    refine Set.image_congr fun c _ => ?_
    rw [Function.comp_apply, Pi.basisFun_apply, LinearEquiv.coe_coe, Basis.equivFun_symm_single]

theorem exists_isometry_map_eq {k : ℕ} (hk : k ≤ r) {X : Submodule K (Fin r ⊕ Fin r → K)}
    (hX : X ∈ singularSubspaces (quadPlus r K) k) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K),
      (flag r K k).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = X := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [Submodule.finrank_eq_zero.1 hX.1, flag_zero]
    exact Submodule.map_bot _
  · obtain ⟨W, hW, hWX⟩ := exists_mem_singularFlags_eq hX hk0
    obtain ⟨g, hg, hgW⟩ := exists_isometry_map_flag_eq hk hW
    refine ⟨g, hg, ?_⟩
    have h := hgW ⟨k - 1, by omega⟩
    rw [hWX, show (⟨k - 1, by omega⟩ : Fin k).val + 1 = k by simp only; omega] at h
    exact h

end Orthogonal

section Elementary

variable {r : ℕ} {K : Type*} [Field K]

theorem exists_elementary_map_flag_eq (hr : 1 ≤ r)
    {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) :
    ∃ a ∈ orthElementaryGroup (quadPlus r K), ∀ m ≤ r - 1,
      (flag r K m).map (a : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) =
        (flag r K m).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) := by
  have hr0 : 0 < r := by omega
  obtain ⟨a, ha, hfix⟩ := exists_mem_elementaryGroup_fix (plusFamily_orth (K := K) hr0)
    (nondegenerate_polarBilin_quadPlus r K) hg (j := r - 1) (by omega)
  have hag : ∀ m ≤ r - 1,
      (flag r K m).map ((a * g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
        (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = flag r K m := by
    intro m hm
    rw [flag, Submodule.map_span, ← Set.image_comp]
    congr 1
    refine Set.image_congr fun j hj => ?_
    have h := (hfix j.val (by simp only [Set.mem_ofPred_eq] at hj; omega)).1
    rw [plusFamily_of_lt hr0 j.isLt, plusPair_e] at h
    rw [Function.comp_apply, LinearEquiv.coe_coe, h]
  refine ⟨a⁻¹, inv_mem ha, fun m hm => ?_⟩
  rw [show g = a⁻¹ * (a * g) by group, map_mul_linearEquiv, hag m hm]

end Elementary


theorem orthogonal_geometry_split_partial_flag_transitivity {K : Type*} [Field K] {r : ℕ}
    (hr : 1 ≤ r) {k : ℕ} (hk : k ≤ r - 1) :
    (∀ W ∈ singularFlags (quadPlus r K) k, ∀ W' ∈ singularFlags (quadPlus r K) k,
      ∃ g ∈ orthElementaryGroup (quadPlus r K),
        ∀ i, (W i).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = W' i) ∧
    ∀ X ∈ singularSubspaces (quadPlus r K) k, ∀ X' ∈ singularSubspaces (quadPlus r K) k,
      ∃ g ∈ orthElementaryGroup (quadPlus r K),
        X.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = X' := by
  have hflag : ∀ W ∈ singularFlags (quadPlus r K) k, ∃ a ∈ orthElementaryGroup (quadPlus r K),
      ∀ i : Fin k,
        (flag r K (i + 1)).map (a : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = W i := by
    intro W hW
    obtain ⟨g, hg, hgW⟩ := exists_isometry_map_flag_eq (by omega) hW
    obtain ⟨a, ha, hag⟩ := exists_elementary_map_flag_eq hr hg
    exact ⟨a, ha, fun i => by rw [hag _ (by omega), hgW i]⟩
  have hsub : ∀ X ∈ singularSubspaces (quadPlus r K) k,
      ∃ a ∈ orthElementaryGroup (quadPlus r K),
        (flag r K k).map (a : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = X := by
    intro X hX
    obtain ⟨g, hg, hgX⟩ := exists_isometry_map_eq (by omega) hX
    obtain ⟨a, ha, hag⟩ := exists_elementary_map_flag_eq hr hg
    exact ⟨a, ha, by rw [hag k hk, hgX]⟩
  refine ⟨fun W hW W' hW' => ?_, fun X hX X' hX' => ?_⟩
  · obtain ⟨a, ha, haW⟩ := hflag W hW
    obtain ⟨a', ha', haW'⟩ := hflag W' hW'
    refine ⟨a' * a⁻¹, mul_mem ha' (inv_mem ha), fun i => ?_⟩
    rw [← haW i, ← haW' i, ← map_mul_linearEquiv, mul_assoc, inv_mul_cancel, mul_one]
  · obtain ⟨a, ha, haX⟩ := hsub X hX
    obtain ⟨a', ha', haX'⟩ := hsub X' hX'
    refine ⟨a' * a⁻¹, mul_mem ha' (inv_mem ha), ?_⟩
    rw [← haX, ← haX', ← map_mul_linearEquiv, mul_assoc, inv_mul_cancel, mul_one]

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

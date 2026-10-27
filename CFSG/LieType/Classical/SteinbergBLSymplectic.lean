module

public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LieType.Classical

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic

variable {K : Type} [Field K]

theorem scalar_mem_statedSp_iff {n : ℕ} (hn : 1 ≤ n) (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ StatedSp n K ↔ c ^ 2 = 1 :=
  CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hn c

theorem scalar_injective {n : ℕ} (hn : 1 ≤ n) :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) : Kˣ → _) := by
  intro c d h
  have h1 := congrArg (fun A : GL (Fin n ⊕ Fin n) K =>
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inl ⟨0, hn⟩) (Sum.inl ⟨0, hn⟩)) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

theorem card_statedSp_inf_statedScalars {n : ℕ} (hn : 1 ≤ n) :
    Nat.card ↥(StatedSp n K ⊓ StatedScalars (Fin n ⊕ Fin n) K) =
      Nat.card {c : Kˣ // c ^ 2 = 1} := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun c : {c : Kˣ // c ^ 2 = 1} =>
      (⟨Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (c : Kˣ),
        Subgroup.mem_inf.2 ⟨(scalar_mem_statedSp_iff hn (c : Kˣ)).2 c.2, ⟨(c : Kˣ), rfl⟩⟩⟩ :
        ↥(StatedSp n K ⊓ StatedScalars (Fin n ⊕ Fin n) K))) ⟨fun c d h => ?_, fun A => ?_⟩)).symm
  · exact Subtype.ext (scalar_injective hn (congrArg Subtype.val h))
  · obtain ⟨hAS, c, hc⟩ := Subgroup.mem_inf.1 A.2
    rw [← hc] at hAS
    exact ⟨⟨c, (scalar_mem_statedSp_iff hn c).1 hAS⟩, Subtype.ext hc⟩

theorem card_sq_eq_one_units [Finite K] :
    Nat.card {c : Kˣ // c ^ 2 = 1} = Nat.gcd 2 (Nat.card K - 1) := by
  classical
  let _ := Fintype.ofFinite K
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  by_cases h2 : ringChar K = 2
  ·
    have hK2 : (2 : K) = 0 := by
      have := ringChar.spec K 2
      exact_mod_cast (this.2 (by rw [h2]))
    have hone : ∀ c : {c : Kˣ // c ^ 2 = 1}, c = ⟨1, one_pow 2⟩ := by
      intro c
      refine Subtype.ext (Units.ext ?_)
      have hc : ((c : Kˣ) : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, c.2, Units.val_one]
      have hsq : (((c : Kˣ) : K) - 1) ^ 2 = 0 := by
        linear_combination hc + (1 - ((c : Kˣ) : K)) * hK2
      rw [Units.val_one]
      exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 hsq)
    have hcard1 : Nat.card {c : Kˣ // c ^ 2 = 1} = 1 :=
      Nat.card_eq_one_iff_exists.2 ⟨⟨1, one_pow 2⟩, hone⟩
    have heven : Nat.card K % 2 = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.even_card_of_char_two h2
    have hodd : Odd (Nat.card K - 1) := by
      rw [Nat.odd_iff]
      omega
    rw [hcard1]
    exact Eq.symm (Nat.coprime_two_left.2 hodd)
  ·
    have hne : (-1 : Kˣ) ≠ 1 := by
      intro h
      exact Ring.neg_one_ne_one_of_char_ne_two h2 (by simpa using congrArg Units.val h)
    have hcard2 : Nat.card {c : Kˣ // c ^ 2 = 1} = 2 := by
      rw [Nat.card_eq_two_iff]
      refine ⟨⟨1, one_pow 2⟩, ⟨-1, by rw [neg_one_sq]⟩, fun h => hne.symm
        (congrArg Subtype.val h), ?_⟩
      ext c
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      have hc : ((c : Kˣ) : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, c.2, Units.val_one]
      rcases (mul_self_eq_one_iff (a := ((c : Kˣ) : K))).1 (by rw [← pow_two]; exact hc)
        with h | h
      · exact Or.inl (Subtype.ext (Units.ext (by rw [h, Units.val_one])))
      · exact Or.inr (Subtype.ext (Units.ext (by rw [h, Units.val_neg, Units.val_one])))
    have hodd : Nat.card K % 2 = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.odd_card_of_char_ne_two h2
    rw [hcard2, Nat.gcd_eq_left (by omega : 2 ∣ Nat.card K - 1)]

theorem symplectic_scalar_kernel (K : Type) [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) :
    (∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ StatedSp n K ↔ c ^ 2 = 1) ∧
      Nat.card ↥(StatedSp n K ⊓ StatedScalars (Fin n ⊕ Fin n) K) =
        Nat.gcd 2 (Nat.card K - 1) :=
  ⟨scalar_mem_statedSp_iff hn, (card_statedSp_inf_statedScalars hn).trans card_sq_eq_one_units⟩

theorem transpose_neg_single (n : ℕ) (i : Fin n) :
    (-(Matrix.single i i (1 : K)))ᵀ = -(Matrix.single i i (1 : K)) := by
  rw [Matrix.transpose_neg, Matrix.transpose_single]

theorem symplectic_projective_nontrivial (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    Nontrivial (StatedProj (StatedSp n K)) ∧
      ∃ T : StatedSp n K, (∀ x : Fin n ⊕ Fin n → K,
          ((T : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x =
            x + (x ⬝ᵥ (fromBlocks 0 1 (-1) 0 *ᵥ
                Pi.single (Sum.inl (⟨0, hn⟩ : Fin n) : Fin n ⊕ Fin n) (1 : K))) •
              Pi.single (Sum.inl (⟨0, hn⟩ : Fin n) : Fin n ⊕ Fin n) (1 : K)) ∧
        (T : StatedProj (StatedSp n K)) ≠ 1 := by
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  set T₀ := upperUnipotent (transpose_neg_single (K := K) n i₀)
  have hT₀ : ((T₀ : TauCeti.GLSymplectic (Fin n) K) : GL (Fin n ⊕ Fin n) K) ∈ StatedSp n K := by
    rw [statedSp_eq_GLSymplectic]
    exact T₀.2
  set T : StatedSp n K := ⟨T₀, hT₀⟩ with hT
  have hmat : ((T : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      fromBlocks 1 (-(Matrix.single i₀ i₀ 1)) 0 1 := coe_upperUnipotent _
  have hne : (T : StatedProj (StatedSp n K)) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨c, hc⟩ := h
    have h1 := congrArg (fun A : GL (Fin n ⊕ Fin n) K =>
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inl i₀) (Sum.inr i₀)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1
    rw [hmat, Matrix.diagonal_apply_ne _ (by simp), fromBlocks_apply₁₂] at h1
    simp at h1
  refine ⟨nontrivial_of_ne _ _ hne, T, fun x => ?_, hne⟩
  rw [hmat]
  funext j
  rcases j with j | j
  · simp only [fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i₀
    · subst hj
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.single_apply, Pi.single_apply,
        Fintype.sum_sum_type]
    · simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, Fintype.sum_sum_type,
        hj, Ne.symm hj]
  · simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply]

end CFSG.LieType.Classical

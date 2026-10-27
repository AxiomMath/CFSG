module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviLayer

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Matrices

variable {K : Type} [Field K] [CharP K 2] {k : ℕ}

omit [CharP K 2] in
theorem det_scalar_fin (ν : K) : (scalar (Fin k) ν).det = ν ^ k := by
  rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

omit [CharP K 2] in
theorem exists_scalar_of_commute_trn {M : Matrix (Fin k) (Fin k) K}
    (h : ∀ (i j : Fin k), i ≠ j → M * (1 + single i j 1) = (1 + single i j 1) * M) :
    ∃ ν : K, M = scalar (Fin k) ν := by
  obtain ⟨ν, hν⟩ := mem_range_scalar_of_commute_single (M := M) fun i j hij => by
    have h1 := h i j hij
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h1
    exact (add_left_cancel h1).symm
  exact ⟨ν, hν.symm⟩

theorem blkSL₂_trn_sq (i j : Fin k) (hij : i ≠ j) :
    (blkSL₂ (trn i j hij (1 : K)) : SpecialLinearGroup (Fin (2 + k)) K) ^ 2 = 1 := by
  rw [← map_pow, trn_sq, map_one]

theorem false_of_inner_mod_center (hk : 1 ≤ k) (hν : ∀ ν : K, ν ≠ 0 → ν ^ k = 1)
    {g : SpecialLinearGroup (Fin (2 + k)) K} {c : K} {D : Matrix (Fin k) (Fin k) K}
    (hg : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk (c • 1) D) (hD : D.det ≠ 1)
    (S : SpecialLinearGroup (Fin k) K)
    (h : ∀ (i j : Fin k) (hij : i ≠ j) (i' j' : Fin k) (hij' : i' ≠ j'),
      proj (2 + k) K g * proj (2 + k) K (blkSL₂ (trn i j hij 1)) * (proj (2 + k) K g)⁻¹ *
          (proj (2 + k) K (blkSL₂ S) * proj (2 + k) K (blkSL₂ (trn i j hij 1)) *
            (proj (2 + k) K (blkSL₂ S))⁻¹)⁻¹ * proj (2 + k) K (blkSL₂ (trn i' j' hij' 1)) =
        proj (2 + k) K (blkSL₂ (trn i' j' hij' 1)) *
          (proj (2 + k) K g * proj (2 + k) K (blkSL₂ (trn i j hij 1)) * (proj (2 + k) K g)⁻¹ *
            (proj (2 + k) K (blkSL₂ S) * proj (2 + k) K (blkSL₂ (trn i j hij 1)) *
              (proj (2 + k) K (blkSL₂ S))⁻¹)⁻¹)) : False := by
  obtain ⟨hc, E, hE, hDE, hED⟩ := exists_inv_blk hg
  have hSS : ((S⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) * S = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hT : ∀ (i j : Fin k), i ≠ j →
      (((S⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) * D) *
          (1 + single i j 1) =
        (1 + single i j 1) * (((S⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix _ _ K) * D) := by
    intro i j hij
    set X := trn (K := K) i j hij 1 with hX
    have hX'det : (D * (X : Matrix (Fin k) (Fin k) K) * E).det = 1 := by
      rw [det_mul, det_mul, X.2, mul_one, ← det_mul, hDE, det_one]
    set X' : SpecialLinearGroup (Fin k) K := ⟨D * (X : Matrix _ _ K) * E, hX'det⟩ with hX'
    have hgX : g * blkSL₂ X * g⁻¹ = blkSL₂ X' := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, hE,
        coe_blkSL₂, coe_blkSL₂, blk_mul, blk_mul, Matrix.mul_one, smul_one_mul_smul_one,
        mul_inv_cancel₀ hc, one_smul]
    set Z := S * X * S⁻¹ with hZ
    set N := X' * Z⁻¹ with hN
    have hNeq : proj (2 + k) K g * proj (2 + k) K (blkSL₂ X) * (proj (2 + k) K g)⁻¹ *
        (proj (2 + k) K (blkSL₂ S) * proj (2 + k) K (blkSL₂ X) *
          (proj (2 + k) K (blkSL₂ S))⁻¹)⁻¹ = proj (2 + k) K (blkSL₂ N) := by
      rw [← map_inv, ← map_mul, ← map_mul, hgX, ← map_inv, ← map_mul, ← map_mul, ← map_inv,
        ← map_mul, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
    have hNc : ∀ (i' j' : Fin k), i' ≠ j' →
        (N : Matrix (Fin k) (Fin k) K) * (1 + single i' j' (1 : K)) =
          (1 + single i' j' (1 : K)) * (N : Matrix (Fin k) (Fin k) K) := by
      intro i' j' hij'
      have h1 := h i j hij i' j' hij'
      rw [hNeq] at h1
      have h2 := commute_of_proj_commute (blkSL₂_trn_sq i' j' hij') h1
      rw [← map_mul, ← map_mul] at h2
      have h3 := congrArg Subtype.val (blkSL₂_injective h2)
      rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_trn] at h3
    obtain ⟨μ, hμ⟩ := exists_scalar_of_commute_trn hNc
    have hNZ : N ∈ center (SpecialLinearGroup (Fin k) K) := by
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨μ, ?_, hμ.symm⟩
      have := N.2
      rw [hμ, det_scalar_fin] at this
      rwa [Fintype.card_fin]
    have hX'2 : X' ^ 2 = 1 := by
      apply blkSL₂_injective
      rw [map_pow, ← hgX, conj_pow, blkSL₂_trn_sq, mul_one, mul_inv_cancel, map_one]
    have hZ2 : Z ^ 2 = 1 := by rw [hZ, conj_pow, trn_sq, mul_one, mul_inv_cancel]
    have hN2 : N ^ 2 = 1 := by
      have hcomm : Commute N Z := (mem_center_iff.mp hNZ Z).symm
      have h1 := hcomm.mul_pow 2
      rw [hN, inv_mul_cancel_right, hX'2, hZ2, mul_one] at h1
      exact h1.symm
    have hN1 : N = 1 := eq_one_of_mem_scalars_of_sq ((scalars_eq_center k K).ge hNZ) hN2
    have hXZ : X' = Z := mul_inv_eq_one.mp hN1
    have hm : D * (X : Matrix (Fin k) (Fin k) K) * E =
        (S : Matrix (Fin k) (Fin k) K) * (X : Matrix (Fin k) (Fin k) K) *
          ((S⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) :=
      congrArg Subtype.val hXZ
    rw [← coe_trn i j hij, ← hX]
    calc ((S⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) * D * X
        = ((S⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) *
            (D * X * E) * D := by simp only [Matrix.mul_assoc, hED, Matrix.mul_one]
      _ = X * (((S⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) * D) := by
          rw [hm]
          simp only [← Matrix.mul_assoc, hSS, Matrix.one_mul]
  obtain ⟨ν, hνT⟩ := exists_scalar_of_commute_trn hT
  have hDν : D = (S : Matrix (Fin k) (Fin k) K) * scalar (Fin k) ν := by
    rw [← hνT, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  have hν0 : ν ≠ 0 := by
    rintro rfl
    have h1 := congrArg det hDE
    rw [hDν, map_zero, Matrix.mul_zero, Matrix.zero_mul, det_one] at h1
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact zero_ne_one (by rwa [det_zero] at h1)
  apply hD
  rw [hDν, det_mul, S.2, one_mul, det_scalar_fin, hν ν hν0]

end Matrices

section Element

variable {K : Type} [Field K]

@[expose] noncomputable def diagD (ω : K) : Matrix (Fin 3) (Fin 3) K := diagonal ![ω, 1, 1]

theorem det_diagD (ω : K) : (diagD ω).det = ω := by
  simp [diagD, det_diagonal, Fin.prod_univ_three]

theorem blk_pow {k : ℕ} (X : Matrix (Fin 2) (Fin 2) K) (D : Matrix (Fin k) (Fin k) K) (n : ℕ) :
    blk X D ^ n = blk (X ^ n) (D ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, blk_one]
  | succ n ih => rw [pow_succ, ih, blk_mul, ← pow_succ, ← pow_succ]

@[expose] noncomputable def diagG (ω : K) (hω : ω ^ 3 = 1) : SpecialLinearGroup (Fin (2 + 3)) K :=
  ⟨blk (ω • (1 : Matrix (Fin 2) (Fin 2) K)) (diagD ω), by
    rw [det_blk, det_smul, det_one, Fintype.card_fin, mul_one, det_diagD, ← pow_succ, hω]⟩

theorem coe_diagG (ω : K) (hω : ω ^ 3 = 1) :
    ((diagG ω hω : SpecialLinearGroup (Fin (2 + 3)) K) : Matrix (Fin (2 + 3)) (Fin (2 + 3)) K) =
      blk (ω • (1 : Matrix (Fin 2) (Fin 2) K)) (diagD ω) :=
  rfl

theorem diagG_pow_three (ω : K) (hω : ω ^ 3 = 1) : diagG ω hω ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagG, blk_pow, smul_pow, one_pow, hω, one_smul,
    diagD, diagonal_pow, Matrix.SpecialLinearGroup.coe_one, ← blk_one]
  congr 1
  rw [← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [hω]

theorem diagG_commute_barW [CharP K 2] (ω : K) (hω : ω ^ 3 = 1)
    {w : projectiveSL (2 + 3) K} (hw : w ∈ barW K 3) :
    proj (2 + 3) K (diagG ω hω) * w = w * proj (2 + 3) K (diagG ω hω) := by
  obtain ⟨X, rfl⟩ := hw
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagG, coe_blkSL₁,
    blk_mul, blk_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_one, Matrix.one_mul]

end Element

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {A : Subgroup G} {θ : ↥A →* projectiveSL (2 + 3) K}

theorem mul_self_mod_three {r : ℕ} (hr : ¬ 3 ∣ r) : r * r % 3 = 1 := by
  have h : r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases h with h | h <;> simp [Nat.mul_mod, h]

theorem diag_five_four (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    (h4 : ∃ s : Finset K, s.card = 4) (hK : Nat.card K = 4) :
    ∃ y ∈ A ⊓ centralizer (leviW θ : Set G), (∃ j : ℕ, y ^ 3 ^ j = 1) ∧
      ¬ ∃ l ∈ leviL θ, ∀ x ∈ leviL θ,
        y * x * y⁻¹ * (l * x * l⁻¹)⁻¹ ∈ (center ↥(leviL θ)).map (leviL θ).subtype := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have h1 := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK] at h1
    omega
  have hcube : ∀ ν : K, ν ≠ 0 → ν ^ 3 = 1 := fun ν hν => by
    have := FiniteField.pow_card_sub_one_eq_one ν hν
    rwa [← Nat.card_eq_fintype_card, hK] at this
  have hω3 := hcube ω hω0
  set g₀ := diagG ω hω3 with hg₀
  obtain ⟨a, ha⟩ := hθ (proj (2 + 3) K g₀)
  obtain ⟨e, r, hr3, hr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a).ne' 3 (by norm_num)
  set y : ↥A := a ^ (r * r) with hy
  have hy3 : y ^ 3 ^ e = 1 := by
    rw [hy, ← pow_mul, show r * r * 3 ^ e = orderOf a * r by rw [hr]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]
  have hyθ : θ y = proj (2 + 3) K g₀ := by
    rw [hy, map_pow, ha, ← map_pow, pow_eq_pow_mod _ (diagG_pow_three ω hω3),
      mul_self_mod_three hr3, pow_one]
  have hyW : (y : G) ∈ centralizer (leviW θ : Set G) := by
    have hle := levLift_le_centralizer hker y.2 (S := barW K 3) fun s hs => by
      rw [hyθ]
      exact diagG_commute_barW ω hω3 hs
    rw [mem_centralizer_iff]
    intro w hw
    exact mem_centralizer_singleton_iff.mp (hle hw)
  refine ⟨y, ⟨y.2, hyW⟩, ⟨e, by rw [← Subgroup.coe_pow, hy3, Subgroup.coe_one]⟩, ?_⟩
  rintro ⟨l, hl, hinner⟩
  obtain ⟨S, hS⟩ := theta_mem_of_mem_levLift hl
  simp only [MonoidHom.comp_apply] at hS
  refine false_of_inner_mod_center (k := 3) (by norm_num) hcube (coe_diagG ω hω3)
    (by rw [det_diagD]; exact hω1) S fun i j hij i' j' hij' => ?_
  obtain ⟨x, hx, hxθ⟩ := exists_mem_levLift hθ (commutator_barL (by norm_num) h4)
    (⟨trn i j hij 1, rfl⟩ : proj (2 + 3) K (blkSL₂ (trn i j hij 1)) ∈ barL K 3)
  obtain ⟨x', hx', hx'θ⟩ := exists_mem_levLift hθ (commutator_barL (by norm_num) h4)
    (⟨trn i' j' hij' 1, rfl⟩ : proj (2 + 3) K (blkSL₂ (trn i' j' hij' 1)) ∈ barL K 3)
  obtain ⟨u, hu, hueq⟩ := hinner x hx
  have hc := mem_center_iff.mp hu ⟨x', hx'⟩
  have hc' : x' * (u : G) = u * x' := congrArg Subtype.val hc
  rw [Subgroup.coe_subtype] at hueq
  rw [hueq] at hc'
  set lA : ↥A := ⟨l, levLift_le hl⟩
  set xA : ↥A := ⟨x, levLift_le hx⟩
  set x'A : ↥A := ⟨x', levLift_le hx'⟩
  have hcA : x'A * (y * xA * y⁻¹ * (lA * xA * lA⁻¹)⁻¹) =
      y * xA * y⁻¹ * (lA * xA * lA⁻¹)⁻¹ * x'A := Subtype.ext hc'
  have h2 := congrArg θ hcA
  simp only [map_mul, map_inv] at h2
  rw [hyθ, hxθ, hx'θ, show θ lA = proj (2 + 3) K (blkSL₂ S) from hS.symm] at h2
  exact h2.symm

end Lift

end CFSG.ComponentClassification.RankTwoClassical

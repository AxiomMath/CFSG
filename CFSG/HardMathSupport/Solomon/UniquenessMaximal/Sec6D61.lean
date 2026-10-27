module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance Matrix

section Center

variable {K : Type} [Field K]

theorem statedSL_eq_range_toGL (n : ℕ) (K : Type) [Field K] :
    StatedSL n K = (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range :=
  CFSG.Open.StatedAPI.statedSL_eq_range_toGL n K

theorem center_statedSL_two_eq_bot [CharP K 2] :
    Subgroup.center ↥(StatedSL 2 K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzr : (z : GL (Fin 2) K) ∈ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range := by
    rw [← statedSL_eq_range_toGL]; exact z.2
  obtain ⟨s, hs⟩ := hzr
  have hsc : s ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, hs]
    have hg : (SpecialLinearGroup.toGL g : GL (Fin 2) K) ∈ StatedSL 2 K := by
      rw [statedSL_eq_range_toGL]; exact ⟨g, rfl⟩
    have := Subgroup.mem_center_iff.mp hz ⟨_, hg⟩
    exact congrArg (fun w : ↥(StatedSL 2 K) => (w : GL (Fin 2) K)) this
  obtain ⟨r, hr, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hsc
  rw [Fintype.card_fin] at hr
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hr0 : (r + 1) ^ 2 = 0 := by linear_combination hr + (r + 1) * h2
  have hr1 : r = 1 := by
    have h := pow_eq_zero_iff (two_ne_zero) |>.mp hr0
    have : r = -1 := eq_neg_of_add_eq_zero_left h
    rw [this, CharTwo.neg_eq]
  rw [hr1, map_one] at hrs
  have h1 : s = 1 := Subtype.ext hrs.symm
  rw [h1, map_one] at hs
  rw [Subgroup.mem_bot]
  exact Subtype.ext hs.symm

theorem charP_two_of_card_eq_two_pow [Finite K] {n : ℕ} (h : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have := hp
  have := Fintype.ofFinite K
  obtain ⟨m, hpp, hm⟩ := FiniteField.card K p
  have hpd : p ∣ 2 ^ n := by
    rw [← h, Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self p m.ne_zero
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hpd)
  rw [hp2] at hp
  exact hp

theorem exists_central_ne_one_of_scalar_mem {H : Subgroup (GL (Fin 3) K)} {ω : Kˣ} (hω : ω ≠ 1)
    (hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ H) :
    ∃ c ∈ Subgroup.center ↥H, c ≠ 1 := by
  refine ⟨⟨_, hmem⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext
    (Matrix.GeneralLinearGroup.scalar_commute ω (g : GL (Fin 3) K)).symm, fun h => hω ?_⟩
  have h' := congrArg (fun z : ↥H =>
      (((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0)) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at h'
  exact Units.ext h'

theorem exists_units_orderOf_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ ω : Kˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])

theorem exists_central_ne_one_statedSL_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ c ∈ Subgroup.center ↥(StatedSL 3 K), c ≠ 1 := by
  obtain ⟨ω, hω⟩ := exists_units_orderOf_three h3
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := fun h => by rw [h, orderOf_one] at hω; omega
  refine exists_central_ne_one_of_scalar_mem hω1 ?_
  apply Subgroup.subset_closure
  change (((Matrix.GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).det = 1
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val, hω3,
    Units.val_one]

theorem exists_central_ne_one_statedSU_three [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (h3 : 3 ∣ q + 1) : ∃ c ∈ Subgroup.center ↥(StatedSU 3 q K), c ≠ 1 := by
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · have := Finite.one_lt_card (α := K); rw [hK, h] at this; simp at this
    · exact h
  have hq : q ≠ 0 := by omega
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      apply Nat.sub_eq_of_eq_add
      ring
    rw [this]
    exact Dvd.dvd.mul_left h3 _
  obtain ⟨ω, hω⟩ := exists_units_orderOf_three h3K
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := fun h => by rw [h, orderOf_one] at hω; omega
  refine exists_central_ne_one_of_scalar_mem hω1 ?_
  have hc' : (ω : K) ^ q * ω = 1 := by
    obtain ⟨m, hm⟩ := h3
    rw [← pow_succ, hm, pow_mul, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hω3,
      one_pow, Units.val_one]
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val, hω3,
      Units.val_one]
  · change ((Matrix.scalar (Fin 3) (ω : K)).map (· ^ q))ᵀ * Matrix.scalar (Fin 3) (ω : K) = 1
    rw [Matrix.scalar_apply, diagonal_map (f := fun x : K => x ^ q) (zero_pow hq),
      diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hc'

end Center

theorem not_isLTwoOddPow_of_central {X : Type*} [Group X] (hc : ∃ c ∈ Subgroup.center X, c ≠ 1) :
    ¬ IsLTwoOddPow X := by
  rintro ⟨K', _, _, n, -, -, hK, ⟨e⟩⟩
  have : CharP K' 2 := charP_two_of_card_eq_two_pow hK
  obtain ⟨c, hcz, hc1⟩ := hc
  have hz : e c ∈ Subgroup.center ↥(StatedSL 2 K') := by
    rw [Subgroup.mem_center_iff] at hcz ⊢
    intro g
    apply e.symm.injective
    rw [map_mul, map_mul, e.symm_apply_apply]
    exact hcz _
  rw [center_statedSL_two_eq_bot, Subgroup.mem_bot] at hz
  exact hc1 (e.injective (hz.trans e.map_one.symm))

theorem not_isLTwoOddPow_of_isSLThreeExc {X : Type*} [Group X] (h : IsSLThreeExc X) :
    ¬ IsLTwoOddPow X := by
  obtain ⟨K, _, _, hK9, ⟨e⟩⟩ := h
  have h3 : 3 ∣ Nat.card K - 1 := by omega
  obtain ⟨c, hc, hc1⟩ := exists_central_ne_one_statedSL_three (K := K) h3
  refine not_isLTwoOddPow_of_central ⟨e.symm c, ?_, fun h' => hc1 ?_⟩
  · rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hc _
  · apply e.symm.injective
    rw [h', map_one]

theorem not_isLTwoOddPow_of_isSUThreeExc {X : Type*} [Group X] (h : IsSUThreeExc X) :
    ¬ IsLTwoOddPow X := by
  obtain ⟨K, _, _, q, hK, hq9, ⟨e⟩⟩ := h
  have h3 : 3 ∣ q + 1 := by omega
  obtain ⟨c, hc, hc1⟩ := exists_central_ne_one_statedSU_three hK h3
  refine not_isLTwoOddPow_of_central ⟨e.symm c, ?_, fun h' => hc1 ?_⟩
  · rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hc _
  · apply e.symm.injective
    rw [h', map_one]

theorem prop61_of_lemma62 (h62 : Lemma62Stmt) (h24 : Lemma24) :
    ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
      ∀ B : Subgroup G, IsExtremal B → IsWeaklyBalancedWrt 3 2 B := by
  intro G _ _ m hS hC B hB
  have hB1 : IsBOneMax 3 B := hB.1
  by_contra hnot
  have hex : ∃ D : Subgroup G, IsEkIn 3 2 B D ∧ ∃ b ∈ B, b ≠ 1 ∧
      ¬ delta2At 3 B D b ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    by_contra hcon
    push Not at hcon
    exact hnot fun D hD b hb hb1 => hcon D hD b hb hb1
  obtain ⟨D, hD, b, hb, hb1, hX⟩ := hex
  obtain ⟨-, ⟨L, hL, hXL⟩, hall⟩ := h24 G m 3 hS B hB1 hnot D hD b hb hb1 hX
  obtain ⟨hi, hii, -⟩ := hall L ⟨hB1, hD, hb, hb1, hX, hL, hXL⟩
  rcases h62 G m hS hC B hB b hb hb1 L hL with hnorm | hL2
  · have h1 : (Subgroup.normalizer (L : Set G)).relIndex B = 1 := Subgroup.relIndex_eq_one.2 hnorm
    omega
  · exact hii.elim (fun h => not_isLTwoOddPow_of_isSLThreeExc h hL2)
      (fun h => not_isLTwoOddPow_of_isSUThreeExc h hL2)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

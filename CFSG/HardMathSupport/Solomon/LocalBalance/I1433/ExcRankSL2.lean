module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankLift
public import CFSG.RankThree.PartTwo.Census.Exceptional.Basic

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank

open CFSG.RankThree.CentralCover CFSG.Assembly.RankThreeEven CFSG.Open
open scoped MatrixGroups

section Odd

variable {S : Type*} [Group S] {F : Type*} [Field F] [Fintype F]

theorem three_dvd_card_sq_sub_one (h3 : ringChar F ≠ 3) : 3 ∣ Fintype.card F ^ 2 - 1 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hnd : ¬ 3 ∣ Fintype.card F := by
    intro hd
    rw [hn] at hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow hd)
    exact h3 this.symm
  have hq : Fintype.card F % 3 = 1 ∨ Fintype.card F % 3 = 2 := by omega
  have h : Fintype.card F ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hq with h | h <;> simp [h]
  omega

theorem liftDatum_of_commuting_SL2_odd (hF2 : ringChar F ≠ 2) (hF3 : ringChar F ≠ 3) {m : ℕ}
    (φ : Fin (m + 1) → SL(2, F) →* S) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, F), φ i A * φ j B = φ j B * φ i A) :
    LiftDatum S m := by
  obtain ⟨h₀, w₀, hord₀, hinv₀⟩ := exists_inverted_of_dvd_card_sq_sub_one hF2 Nat.prime_three
    (by norm_num) (three_dvd_card_sq_sub_one hF3)
  set i₀ : Fin (m + 1) := 0
  set z : S := φ i₀ (sl2Diag (-1)) with hz
  have hzo : orderOf z = 2 := by
    rw [hz, orderOf_injective _ (hφ i₀), orderOf_sl2Diag_neg_one hF2]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo
    omega
  have hzh : ∀ i, Commute z (φ i h₀) := fun i => by
    by_cases hi : i = i₀
    · rw [hi]
      exact (sl2Diag_neg_one_commute h₀).map (φ i₀)
    · exact hcomm i₀ i (Ne.symm hi) _ _
  refine ⟨fun i => φ i h₀, fun i => φ i w₀, Subgroup.zpowers z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · rw [hij]
    · exact hcomm i j hij h₀ h₀
  · intro i
    rw [orderOf_injective _ (hφ i), hord₀]
  · intro i
    dsimp only
    rw [← map_inv, ← map_mul, ← map_mul, hinv₀, map_inv]
  · intro i j hij _
    dsimp only
    rw [hcomm i j hij w₀ h₀, mul_inv_cancel_right]
  · rwa [Ne, Subgroup.zpowers_eq_bot]
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  · intro i
    exact centralizer_le_normalizer_zpowers z
      (Subgroup.mem_centralizer_singleton_iff.2 (hzh i).eq.symm)

end Odd

section Even

variable {S : Type*} [Group S] {F : Type*} [Field F] [Fintype F]

theorem liftDatum_of_commuting_SL2_even (hF : ringChar F = 2) (h3 : 3 ∣ Fintype.card F - 1)
    {m : ℕ} (φ : Fin (m + 1) → SL(2, F) →* S) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, F), φ i A * φ j B = φ j B * φ i A) :
    LiftDatum S m := by
  classical
  have hcard : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact h3
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 hcard
  set i₀ : Fin (m + 1) := 0
  set U : Subgroup S := (sl2UpperHom F).range.map (φ i₀) with hU
  have hmemU : ∀ x ∈ U, ∃ c : F, x = φ i₀ (sl2Upper c) := by
    intro x hx
    obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨Multiplicative.toAdd c, rfl⟩
  have hUmem : ∀ c : F, φ i₀ (sl2Upper c) ∈ U := fun c =>
    Subgroup.mem_map.2 ⟨_, ⟨Multiplicative.ofAdd c, rfl⟩, rfl⟩
  have htwo : (2 : F) = 0 := by
    have := ringChar.Nat.cast_ringChar (R := F)
    rwa [hF, Nat.cast_ofNat] at this
  have hU1 : U ≠ ⊥ := by
    intro h
    have h1 := hUmem 1
    rw [h, Subgroup.mem_bot, ← map_one (φ i₀)] at h1
    have h2 := sl2Upper_injective ((hφ i₀) h1 |>.trans sl2Upper_zero.symm)
    exact one_ne_zero h2
  have hU2 : IsPGroup 2 U := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨c, rfl⟩ := hmemU x hx
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, sl2Upper_pow, Nat.cast_ofNat,
      htwo, zero_mul, sl2Upper_zero, map_one]
  have hgen : ∀ i, φ i (sl2Diag ζ) ∈ Subgroup.normalizer (U : Set S) := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      have hconj : ∀ a : Fˣ, ∀ x ∈ U, φ i₀ (sl2Diag a) * x * (φ i₀ (sl2Diag a))⁻¹ ∈ U := by
        intro a x hx
        obtain ⟨c, rfl⟩ := hmemU x hx
        rw [← map_inv, ← map_mul, ← map_mul, sl2Diag_conj_upper]
        exact hUmem _
      refine mem_normalizer_of_conj_mem (hconj ζ) fun x hx => ?_
      have hinv : (φ i₀ (sl2Diag ζ))⁻¹ = φ i₀ (sl2Diag ζ⁻¹) := by
        rw [← sl2DiagHom_apply, ← sl2DiagHom_apply, map_inv, map_inv]
      have := hconj ζ⁻¹ x hx
      rwa [← hinv, inv_inv] at this
    · have hfix : ∀ x ∈ U, φ i (sl2Diag ζ) * x * (φ i (sl2Diag ζ))⁻¹ = x := by
        intro x hx
        obtain ⟨c, rfl⟩ := hmemU x hx
        rw [hcomm i i₀ hi, mul_inv_cancel_right]
      refine mem_normalizer_of_conj_mem (fun x hx => by rw [hfix x hx]; exact hx)
        fun x hx => ?_
      have h1 := hfix x hx
      rw [mul_inv_eq_iff_eq_mul] at h1
      have h2 : (φ i (sl2Diag ζ))⁻¹ * x * φ i (sl2Diag ζ) = x := by
        rw [mul_assoc, ← h1, inv_mul_cancel_left]
      rw [h2]
      exact hx
  refine ⟨fun i => φ i (sl2Diag ζ), fun i => φ i (sl2Weyl F), U, ?_, ?_, ?_, ?_, hU1, hU2, hgen⟩
  · intro i j
    by_cases hij : i = j
    · rw [hij]
    · exact hcomm i j hij _ _
  · intro i
    rw [orderOf_injective _ (hφ i), orderOf_sl2Diag, hζ]
  · intro i
    dsimp only
    rw [← map_inv, ← map_mul, ← map_mul, sl2Weyl_conj_diag, map_inv]
  · intro i j hij _
    dsimp only
    rw [hcomm i j hij (sl2Weyl F) (sl2Diag ζ), mul_inv_cancel_right]

end Even

section Torus

open CFSG.RankThree.PartTwo.Census.Exceptional

variable {S : Type*} [Group S] {F : Type*} [Field F]

theorem exists_inverted_sl2Three_even (hF : ringChar F = 2) :
    ∃ g : SL(2, F), g * sl2Three F * g⁻¹ = (sl2Three F)⁻¹ := by
  have htwo : (2 : F) = 0 := by
    have := ringChar.Nat.cast_ringChar (R := F)
    rwa [hF, Nat.cast_ofNat] at this
  set g₀ : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩ with hg₀
  have hg : (g₀ : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl
  refine ⟨g₀, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  have hinv : (sl2Three F)⁻¹ = sl2Three F ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', sl2Three_pow_three]
  rw [hinv, pow_two]
  ext i j
  simp only [sl2Three, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Weyl, hg]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | linear_combination htwo | linear_combination (-1 : F) * htwo

theorem liftDatum_of_commuting_SL2_normalizing (hF : ringChar F = 2) {m : ℕ}
    (φ : Fin (m + 1) → SL(2, F) →* S) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, F), φ i A * φ j B = φ j B * φ i A)
    {U : Subgroup S} (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hN : ∀ i A, φ i A ∈ Subgroup.normalizer (U : Set S)) : LiftDatum S m := by
  obtain ⟨g₀, hg₀⟩ := exists_inverted_sl2Three_even hF
  have hne : sl2Three F ≠ 1 := fun h => sl2Three_not_commute F (by rw [h]; simp)
  have hw3 : orderOf (sl2Three F) = 3 := orderOf_eq_prime (sl2Three_pow_three F) hne
  refine ⟨fun i => φ i (sl2Three F), fun i => φ i g₀, U, ?_, ?_, ?_, ?_, hU1, hU2,
    fun i => hN i _⟩
  · intro i j
    by_cases hij : i = j
    · rw [hij]
    · exact hcomm i j hij _ _
  · intro i
    rw [orderOf_injective _ (hφ i), hw3]
  · intro i
    dsimp only
    rw [← map_inv, ← map_mul, ← map_mul, hg₀, map_inv]
  · intro i j hij _
    dsimp only
    rw [hcomm i j hij g₀ (sl2Three F), mul_inv_cancel_right]

theorem liftDatum_of_five_commuting_SL2_even (hF : ringChar F = 2) (φ : Fin 5 → SL(2, F) →* S)
    (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, F), φ i A * φ j B = φ j B * φ i A) :
    LiftDatum S 3 := by
  have hu : orderOf (φ 4 (sl2Upper 1)) = 2 := by
    rw [orderOf_injective (φ 4) (hφ 4)]
    exact orderOf_sl2Upper_one hF
  have hu1 : φ 4 (sl2Upper 1) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hu
    omega
  refine liftDatum_of_commuting_SL2_normalizing hF (m := 3) (fun i => φ i.castSucc)
    (fun i => hφ _) (fun i j hij A B => hcomm _ _ (fun h => hij (Fin.castSucc_injective 4 h)) A B)
    (U := Subgroup.zpowers (φ 4 (sl2Upper 1))) ?_ ?_ ?_
  · rwa [Ne, Subgroup.zpowers_eq_bot]
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  · intro i A
    exact centralizer_le_normalizer_zpowers _ (Subgroup.mem_centralizer_singleton_iff.2
      (hcomm _ _ (Fin.castSucc_ne_last i) A _))

theorem liftDatum_of_commuting_SL2_torus (hF : ringChar F = 2) {m : ℕ}
    (φ : Fin m → SL(2, F) →* S) (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, F), φ i A * φ j B = φ j B * φ i A)
    {u : S} (hu : orderOf u = 2) {τ g : S} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hφu : ∀ i A, φ i A * u = u * φ i A) (hτφ : ∀ i A, φ i A * τ = τ * φ i A)
    (hτu : τ * u = u * τ) (hgτ : g * τ * g⁻¹ = τ⁻¹) : LiftDatum S m := by
  obtain ⟨g₀, hg₀⟩ := exists_inverted_sl2Three_even hF
  have hne : sl2Three F ≠ 1 := fun h => sl2Three_not_commute F (by rw [h]; simp)
  have hw3 : orderOf (sl2Three F) = 3 := orderOf_eq_prime (sl2Three_pow_three F) hne
  have hz1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    omega
  refine ⟨Fin.snoc (fun i : Fin m => φ i (sl2Three F)) τ,
    Fin.snoc (fun i : Fin m => φ i g₀) g, Subgroup.zpowers u, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact Commute.refl _
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact (hτφ j _).symm
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact hτφ i _
      | cast j =>
        simp only [Fin.snoc_castSucc]
        by_cases hij : i = j
        · rw [hij]
        · exact hcomm i j hij _ _
  · intro i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using orderOf_eq_prime hτ3 hτ1
    | cast i =>
      simp only [Fin.snoc_castSucc]
      rw [orderOf_injective _ (hφ i), hw3]
  · intro i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hgτ
    | cast i =>
      simp only [Fin.snoc_castSucc]
      rw [← map_inv, ← map_mul, ← map_mul, hg₀, map_inv]
  · intro i j hij hi
    induction i using Fin.lastCases with
    | last => exact absurd rfl hi
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [hτφ i g₀, mul_inv_cancel_right]
      | cast j =>
        simp only [Fin.snoc_castSucc]
        have hij' : i ≠ j := fun h => hij (h ▸ rfl)
        rw [hcomm i j hij' g₀ _, mul_inv_cancel_right]
  · rwa [Ne, Subgroup.zpowers_eq_bot]
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  · intro i
    refine centralizer_le_normalizer_zpowers u (Subgroup.mem_centralizer_singleton_iff.2 ?_)
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact hτu
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact hφu i _

end Torus

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank

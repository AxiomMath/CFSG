module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootColumns

public noncomputable section

namespace CFSG.Wreathed.FourPointOrderEight

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.WreathCentralSquare
  CFSG.Wreathed.SquareRootSmallCharacterRigidity CFSG.Wreathed.ConditionalSquareRoot

open scoped BigOperators Classical

theorem isPrimitiveRoot_eight_of_sq_eq {η i : ℂ} (hi : i ^ 2 = -1) (hη : η ^ 2 = i) :
    IsPrimitiveRoot η (2 * 2 ^ 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : η ^ 2 ^ 2 = -1 := by
    rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, hη, hi]
  have h8 : η ^ 2 ^ (2 + 1) = 1 := by
    rw [pow_succ, pow_mul, h4]
    norm_num
  have hord : orderOf η = 2 ^ (2 + 1) := orderOf_eq_prime_pow (by rw [h4]; norm_num) h8
  rw [show 2 * 2 ^ 2 = 2 ^ (2 + 1) by norm_num, ← hord]
  exact IsPrimitiveRoot.orderOf η

theorem root_signed_columns {G : Type} [Group G] [Fintype G] (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ 2)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {i : ℂ} (hi : i ^ 2 = -1)
    (y : G) (hy : y = actualRoot S e) :
    let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    ∃ c₀ c₁ : basis.index → ℤ,
      (∀ χ ∈ B₀, ∀ r ∈ Subgroup.centralizer ({y} : Set G), Odd (orderOf r) →
        (basis.representation χ).character (y * r) = (basis.representation χ).character y) ∧
      (∀ χ ∈ B₀, (basis.representation χ).character y = c₀ χ + c₁ χ * i) ∧
      ∑ χ ∈ B₀, c₀ χ * c₀ χ = 4 ∧ ∑ χ ∈ B₀, c₁ χ * c₁ χ = 4 ∧ ∑ χ ∈ B₀, c₀ χ * c₁ χ = 0 ∧
      ∑ χ ∈ B₀, (c₀ χ : ℂ) * (basis.representation χ).character 1 = 0 ∧
      ∑ χ ∈ B₀, (c₁ χ : ℂ) * (basis.representation χ).character 1 = 0 ∧
      c₀ principal = 1 ∧ c₁ principal = 0 ∧
      (B₀.filter (fun χ => c₀ χ ≠ 0)).card = 4 ∧ (∀ χ ∈ B₀, c₀ χ = 0 ∨ c₀ χ = 1 ∨ c₀ χ = -1) ∧
      (B₀.filter (fun χ => c₁ χ ≠ 0)).card = 4 ∧
      ∀ χ ∈ B₀, c₁ χ = 0 ∨ c₁ χ = 1 ∨ c₁ χ = -1 := by
  intro B₀
  subst hy
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_pow_nat_eq i (by norm_num : 0 < 2)
  obtain ⟨hexp, hcgram, hcdeg, hc0, hcr, hfour⟩ :=
    actualRoot_signed_even_columns 2 le_rfl S e basis ideal principal hprincipal
      (isPrimitiveRoot_eight_of_sq_eq hi hη)
  let c : basis.index → ℕ → ℤ := fun χ r =>
    signedEvenEigenmultiplicity (basis.representation χ) (actualRoot S e) η (2 ^ 2) r
  have hexp' : ∀ χ ∈ B₀, ∀ h : ℤ, Odd h →
      ∀ z ∈ Subgroup.centralizer ({actualRoot S e} : Set G), Odd (orderOf z) →
        (basis.representation χ).character (actualRoot S e ^ h * z) =
          (basis.representation χ).character (actualRoot S e ^ h) ∧
        (basis.representation χ).character (actualRoot S e ^ h) =
          ∑ r ∈ Finset.range 2, (c χ r : ℂ) * (η ^ 2) ^ ((r : ℤ) * h) := hexp
  have hcgram' : ∀ r < 2, ∀ t < 2, ∑ χ ∈ B₀, c χ r * c χ t = if r = t then 4 else 0 := hcgram
  have hcdeg' : ∀ r < 2, ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character 1 = 0 :=
    hcdeg
  have hfour' : ∀ r < 2, (B₀.filter (fun χ => c χ r ≠ 0)).card = 4 ∧
      ∀ χ ∈ B₀, c χ r = 0 ∨ c χ r = 1 ∨ c χ r = -1 := hfour
  have hodd1 : Odd (orderOf (1 : G)) := by
    rw [orderOf_one]
    exact odd_one
  refine ⟨fun χ => c χ 0, fun χ => c χ 1, ?_, ?_, ?_, ?_, ?_, hcdeg' 0 (by norm_num),
    hcdeg' 1 (by norm_num), hc0, hcr 1 (by norm_num) (by norm_num), (hfour' 0 (by norm_num)).1,
    (hfour' 0 (by norm_num)).2, (hfour' 1 (by norm_num)).1, (hfour' 1 (by norm_num)).2⟩
  · intro χ hχ r hr hrodd
    have h := (hexp' χ hχ 1 odd_one r hr hrodd).1
    rwa [zpow_one] at h
  · intro χ hχ
    have h := (hexp' χ hχ 1 odd_one 1 (Subgroup.one_mem _) hodd1).2
    rw [zpow_one, Finset.sum_range_succ, Finset.sum_range_one] at h
    simp only [Nat.cast_zero, Nat.cast_one, zpow_zero, zpow_one, mul_one] at h
    rw [h, hη]
  · have h := hcgram' 0 (by norm_num) 0 (by norm_num)
    rwa [ite_eq_left rfl] at h
  · have h := hcgram' 1 (by norm_num) 1 (by norm_num)
    rwa [ite_eq_left rfl] at h
  · have h := hcgram' 0 (by norm_num) 1 (by norm_num)
    rwa [ite_eq_right (by norm_num)] at h

theorem root_orthogonal_central_columns {G : Type} [Group G] [Fintype G] (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ 2)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (z : G)
    (hz : z * wreathModelHom S e (Original.a (2 ^ 2)) = wreathModelHom S e (Original.a (2 ^ 2)) * z)
    (hzodd : Odd (orderOf z)) {h : ℤ} (hh : Odd h) (g₀ : G) (hg₀ : g₀ = actualRoot S e ^ h) :
    let a := wreathModelHom S e (Original.a (2 ^ 2))
    let x := wreathModelHom S e (Original.x (2 ^ 2))
    let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let X : basis.index → G → ℂ := fun χ => (basis.representation χ).character
    ∑ χ ∈ B₀, X χ g₀ * X χ a = 0 ∧ ∑ χ ∈ B₀, X χ g₀ * X χ (a * z) = 0 ∧
    ∑ χ ∈ B₀, X χ g₀ * X χ x = 0 ∧ ∑ χ ∈ B₀, X χ g₀ * X χ (x * z) = 0 ∧
    ∑ χ ∈ B₀, X χ g₀ * starRingEnd ℂ (X χ a) = 0 ∧
    ∑ χ ∈ B₀, X χ g₀ * starRingEnd ℂ (X χ (a * z)) = 0 := by
  intro a x B₀ X
  subst hg₀
  have horth : ∀ (k : ℕ) (r : G), r * a = a * r → Odd (orderOf r) →
      ∑ χ ∈ B₀, X χ (actualRoot S e ^ h) * starRingEnd ℂ (X χ (a ^ k * r)) = 0 := by
    intro k r hr hrodd
    refine actualRoot_odd_power_column_orthogonal_central 2 le_rfl S e basis ideal principal
      hprincipal hh k r ?_ hrodd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.pow_right (show Commute r a from hr) k).eq
  have h1 : (1 : G) * a = a * 1 := by rw [one_mul, mul_one]
  have hodd1 : Odd (orderOf (1 : G)) := by
    rw [orderOf_one]
    exact odd_one
  have hzinv : z⁻¹ * a = a * z⁻¹ := (Commute.inv_left (show Commute z a from hz)).eq
  have hzinvodd : Odd (orderOf z⁻¹) := by rwa [orderOf_inv]
  have ha4 : a ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← orderOf_wreathModelHom_a 2 S e, pow_orderOf_eq_one]
  have hxa : x = a ^ 2 := by
    change wreathModelHom S e (Original.x (2 ^ 2)) = wreathModelHom S e (Original.a (2 ^ 2)) ^ 2
    rw [wreathModelHom_x_eq]
    rfl
  have ha3 : (a ^ 3)⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_succ, ha4])
  have ha2 : (a ^ 2)⁻¹ = a ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_add, ha4])
  have hza2 : z * a ^ 2 = a ^ 2 * z := (Commute.pow_right (show Commute z a from hz) 2).eq
  have hcol : ∀ (k : ℕ) (r : G) (g : G), (a ^ k * r)⁻¹ = g → r * a = a * r → Odd (orderOf r) →
      ∑ χ ∈ B₀, X χ (actualRoot S e ^ h) * X χ g = 0 := by
    intro k r g hg hr hrodd
    rw [← horth k r hr hrodd]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [finite_character_conjugate_inverse, hg]
  refine ⟨hcol 3 1 a (by rw [mul_one, ha3]) h1 hodd1, hcol 3 z⁻¹ (a * z) ?_ hzinv hzinvodd,
    hcol 2 1 x (by rw [mul_one, ha2, hxa]) h1 hodd1, hcol 2 z⁻¹ (x * z) ?_ hzinv hzinvodd, ?_, ?_⟩
  · rw [mul_inv_rev, inv_inv, ha3, hz]
  · rw [mul_inv_rev, inv_inv, ha2, hza2, hxa]
  · have h := horth 1 1 h1 hodd1
    rwa [pow_one, mul_one] at h
  · have h := horth 1 z hz hzodd
    rwa [pow_one] at h

theorem sum_coeff_eq_zero {ι : Type*} (B : Finset ι) {i : ℂ} (hi : i ^ 2 = -1)
    (Xp Xm g : ι → ℂ) (c₀ c₁ : ι → ℤ) (hp : ∀ χ ∈ B, Xp χ = c₀ χ + c₁ χ * i)
    (hm : ∀ χ ∈ B, Xm χ = c₀ χ - c₁ χ * i) (hplus : ∑ χ ∈ B, Xp χ * g χ = 0)
    (hminus : ∑ χ ∈ B, Xm χ * g χ = 0) :
    ∑ χ ∈ B, (c₀ χ : ℂ) * g χ = 0 ∧ ∑ χ ∈ B, (c₁ χ : ℂ) * g χ = 0 := by
  have eplus : ∑ χ ∈ B, Xp χ * g χ =
      ∑ χ ∈ B, (c₀ χ : ℂ) * g χ + i * ∑ χ ∈ B, (c₁ χ : ℂ) * g χ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun χ hχ => by rw [hp χ hχ]; ring
  have eminus : ∑ χ ∈ B, Xm χ * g χ =
      ∑ χ ∈ B, (c₀ χ : ℂ) * g χ - i * ∑ χ ∈ B, (c₁ χ : ℂ) * g χ := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun χ hχ => by rw [hm χ hχ]; ring
  have hi0 : i ≠ 0 := by
    rintro rfl
    norm_num at hi
  rw [eplus] at hplus
  rw [eminus] at hminus
  refine ⟨by linear_combination (hplus + hminus) / 2, ?_⟩
  have h : i * ∑ χ ∈ B, (c₁ χ : ℂ) * g χ = 0 := by linear_combination (hplus - hminus) / 2
  exact (mul_eq_zero.mp h).resolve_left hi0

theorem sum_mul_lincomb_eq_zero {ι : Type*} (B : Finset ι) (p F G h : ι → ℂ) (α β : ℂ)
    (hh : ∀ χ, h χ = α * F χ + β * G χ) (hF : ∑ χ ∈ B, p χ * F χ = 0)
    (hG : ∑ χ ∈ B, p χ * G χ = 0) : ∑ χ ∈ B, p χ * h χ = 0 := by
  have hsum : ∑ χ ∈ B, p χ * h χ = α * ∑ χ ∈ B, p χ * F χ + β * ∑ χ ∈ B, p χ * G χ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun χ _ => by rw [hh]; ring
  rw [hsum, hF, hG, mul_zero, mul_zero, add_zero]

theorem sum_mul_fourier_eq_zero {ι : Type*} (B : Finset ι) (p T U A Bv : ι → ℂ) (i : ℂ)
    (v : ι → ℕ → Fin 2 → ℂ) (hv1 : ∀ χ, v χ 1 = ![(T χ + 2 * U χ) / 3, (T χ - U χ) / 3])
    (hv2 : ∀ χ, v χ 2 = ![(A χ + 2 * Bv χ) / 3, (A χ - Bv χ) / 3])
    (hv3 : ∀ χ, v χ 3 =
      ![starRingEnd ℂ ((T χ + 2 * U χ) / 3), starRingEnd ℂ ((T χ - U χ) / 3)])
    (hT : ∑ χ ∈ B, p χ * T χ = 0) (hU : ∑ χ ∈ B, p χ * U χ = 0)
    (hA : ∑ χ ∈ B, p χ * A χ = 0) (hB : ∑ χ ∈ B, p χ * Bv χ = 0)
    (hcT : ∑ χ ∈ B, p χ * starRingEnd ℂ (T χ) = 0)
    (hcU : ∑ χ ∈ B, p χ * starRingEnd ℂ (U χ) = 0) (j : ℕ) (ℓ : Fin 2) :
    ∑ χ ∈ B, p χ * ((1 / 4) * ∑ n' ∈ Finset.Icc 1 3, (i ^ (j * n') - 1) * v χ n' ℓ) = 0 := by
  have hrow : ∀ n' ∈ Finset.Icc 1 3, ∑ χ ∈ B, p χ * v χ n' ℓ = 0 := by
    intro n' hn'
    rw [Finset.mem_Icc] at hn'
    obtain ⟨h1, h3⟩ := hn'
    obtain rfl | rfl : ℓ = 0 ∨ ℓ = 1 := by fin_cases ℓ <;> simp
    · interval_cases n'
      · exact sum_mul_lincomb_eq_zero B p T U _ (1 / 3) (2 / 3)
          (fun χ => by rw [hv1]; simp only [Matrix.cons_val_zero]; ring) hT hU
      · exact sum_mul_lincomb_eq_zero B p A Bv _ (1 / 3) (2 / 3)
          (fun χ => by rw [hv2]; simp only [Matrix.cons_val_zero]; ring) hA hB
      · exact sum_mul_lincomb_eq_zero B p _ _ _ (1 / 3) (2 / 3)
          (fun χ => by
            rw [hv3]
            simp only [Matrix.cons_val_zero, map_div₀, map_add, map_mul, map_ofNat]
            ring) hcT hcU
    · interval_cases n'
      · exact sum_mul_lincomb_eq_zero B p T U _ (1 / 3) (-1 / 3)
          (fun χ => by
            rw [hv1]
            simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
            ring) hT hU
      · exact sum_mul_lincomb_eq_zero B p A Bv _ (1 / 3) (-1 / 3)
          (fun χ => by
            rw [hv2]
            simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
            ring) hA hB
      · exact sum_mul_lincomb_eq_zero B p _ _ _ (1 / 3) (-1 / 3)
          (fun χ => by
            rw [hv3]
            simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, map_div₀, map_sub, map_ofNat]
            ring) hcT hcU
  have hsum : ∑ χ ∈ B, p χ * ((1 / 4) * ∑ n' ∈ Finset.Icc 1 3, (i ^ (j * n') - 1) * v χ n' ℓ) =
      (1 / 4) * ∑ n' ∈ Finset.Icc 1 3, (i ^ (j * n') - 1) * ∑ χ ∈ B, p χ * v χ n' ℓ := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n' _ => Finset.sum_congr rfl fun χ _ => ?_
    ring
  rw [hsum, Finset.sum_eq_zero fun n' hn' => by rw [hrow n' hn', mul_zero], mul_zero]

theorem exists_two_pairs {ι : Type*} [DecidableEq ι] (T : Finset ι) (hT : T.card = 4)
    (σ : ι → ι) (hσσ : ∀ χ, σ (σ χ) = χ) (hσT : ∀ χ ∈ T, σ χ ∈ T)
    (hσne : ∀ χ ∈ T, σ χ ≠ χ) :
    ∃ χ₁ ∈ T, ∃ χ₂ ∈ T, χ₁ ≠ σ χ₁ ∧ χ₁ ≠ χ₂ ∧ χ₁ ≠ σ χ₂ ∧ σ χ₁ ≠ χ₂ ∧ σ χ₁ ≠ σ χ₂ ∧
      χ₂ ≠ σ χ₂ ∧ T = {χ₁, σ χ₁, χ₂, σ χ₂} := by
  obtain ⟨χ₁, hχ₁⟩ : T.Nonempty := Finset.card_pos.mp (by rw [hT]; norm_num)
  have h11 : σ χ₁ ≠ χ₁ := hσne χ₁ hχ₁
  have hcard : ((T.erase χ₁).erase (σ χ₁)).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h11, hσT χ₁ hχ₁⟩),
      Finset.card_erase_of_mem hχ₁, hT]
  obtain ⟨χ₂, hχ₂⟩ : ((T.erase χ₁).erase (σ χ₁)).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; norm_num)
  obtain ⟨h2σ1, hχ₂'⟩ := Finset.mem_erase.mp hχ₂
  obtain ⟨h21, hχ₂T⟩ := Finset.mem_erase.mp hχ₂'
  have h22 : σ χ₂ ≠ χ₂ := hσne χ₂ hχ₂T
  have h2' : σ χ₂ ≠ χ₁ := fun h => h2σ1 (by rw [← h, hσσ])
  have h2'' : σ χ₂ ≠ σ χ₁ := fun h => h21 (by rw [← hσσ χ₂, h, hσσ])
  refine ⟨χ₁, hχ₁, χ₂, hχ₂T, h11.symm, h21.symm, h2'.symm, h2σ1.symm, h2''.symm, h22.symm, ?_⟩
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact hχ₁
    · exact hσT _ hχ₁
    · exact hχ₂T
    · exact hσT _ hχ₂T
  · rw [hT, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h22.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h2σ1.symm, h2''.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h11.symm, h21.symm, h2'.symm⟩

end CFSG.Wreathed.FourPointOrderEight

module

public import CFSG.CharacterTheory.Semidihedral.Principal.EvenFourierFamily

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Open

variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}

theorem degree_zero_difference_star_coordinates_of_two_le
    {L I : Type*} [DecidableEq L] [Fintype I] [DecidableEq I] (zero : I)
    (hI : 2 ≤ Fintype.card I) (S : Finset L) (deg : L → ℤ) (hdeg : ∀ x ∈ S, 0 < deg x)
    (f : I → L → ℤ) (hzero : ∀ x ∈ S, f zero x = 0)
    (hdegree : ∀ i, ∑ x ∈ S, f i x * deg x = 0)
    (hgram : ∀ i k, i ≠ zero → k ≠ zero →
      ∑ x ∈ S, f i x * f k x = 1 + if i = k then 1 else 0) :
    ∃ (ε : ℤ) (ν : I → L), (ε = 1 ∨ ε = -1) ∧ Function.Injective ν ∧ (∀ i, ν i ∈ S) ∧
      (∀ i k, deg (ν i) = deg (ν k)) ∧
      ∀ i, ∀ x ∈ S, f i x = ε * ((if x = ν i then 1 else 0) - (if x = ν zero then 1 else 0)) := by
  rcases Nat.lt_or_ge (Fintype.card I) 3 with h2 | h3
  · obtain ⟨other, hother⟩ := Fintype.exists_ne_of_one_lt_card (by omega) zero
    have hall : ∀ i, i = zero ∨ i = other := by
      intro i
      by_contra hne
      push Not at hne
      have hsub : ({zero, other, i} : Finset I).card ≤ Fintype.card I := Finset.card_le_univ _
      rw [Finset.card_insert_of_notMem (by simp [hother.symm, hne.1.symm]),
        Finset.card_pair (Ne.symm hne.2)] at hsub
      omega
    obtain ⟨A, hAS, B', hBS, hAB, hdegAB, hform⟩ := degree_zero_norm_two_coordinates S deg hdeg
      (f other) (by simpa using hgram other other hother hother) (hdegree other)
    let ν : I → L := fun i => if i = zero then B' else A
    have hν0 : ν zero = B' := ite_eq_left rfl
    have hν1 : ν other = A := ite_eq_right hother
    refine ⟨1, ν, Or.inl rfl, ?_, fun i => ?_, fun i k => ?_, fun i x hx => ?_⟩
    · intro i k hik
      rcases hall i with rfl | rfl <;> rcases hall k with rfl | rfl
      · rfl
      · rw [hν0, hν1] at hik; exact absurd hik.symm hAB
      · rw [hν0, hν1] at hik; exact absurd hik hAB
      · rfl
    · rcases hall i with rfl | rfl
      · rw [hν0]; exact hBS
      · rw [hν1]; exact hAS
    · have hd : ∀ i, deg (ν i) = deg B' := fun i => by
        rcases hall i with rfl | rfl
        · rw [hν0]
        · rw [hν1, hdegAB]
      rw [hd i, hd k]
    · rcases hall i with rfl | rfl
      · rw [hzero x hx]
        ring
      · rw [hform x hx, hν1, hν0]
        ring
  · exact degree_zero_difference_star_coordinates zero h3 S deg hdeg f hzero hdegree hgram

omit [Fintype G] in
theorem twist_mul_not_mem_of_isOddResidueTransversal (hn : 4 ≤ n)
    {I : Finset (ZMod (modulus n))}
    (hI : IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I)
    {j : ZMod (modulus n)} (hj : j ∈ I) :
    (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) * j ∉ I := by
  intro haj
  obtain ⟨hM4, hKeven, hK2, -⟩ := modulus_eq_four_mul hn
  have hodd : Odd (j.val : ℤ) := by exact_mod_cast hI.odd j hj
  have hhalf : ((modulus n / 2 : ℕ) : ℤ) = 2 * ((2 ^ (n - 3) : ℕ) : ℤ) := by omega
  have hnc0 : ¬ (j.val : ℤ) ≡ 0 [ZMOD modulus n] := by
    intro h
    have hd := (Int.modEq_zero_iff_dvd.mp h)
    have h2 : (2 : ℤ) ∣ (j.val : ℤ) := (Dvd.intro (2 * ((2 ^ (n - 3) : ℕ) : ℤ))
      (by rw [hM4]; push_cast; ring)).trans hd
    exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hnc1 : ¬ (j.val : ℤ) ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] := by
    intro h
    have hd := Int.ModEq.dvd h.symm
    have h2 : (2 : ℤ) ∣ (j.val : ℤ) - ((modulus n / 2 : ℕ) : ℤ) :=
      (Dvd.intro (2 * ((2 ^ (n - 3) : ℕ) : ℤ)) (by rw [hM4]; push_cast; ring)).trans hd
    have h2' : (2 : ℤ) ∣ (j.val : ℤ) := by
      have := dvd_add h2 ⟨((2 ^ (n - 3) : ℕ) : ℤ), hhalf⟩
      rwa [sub_add_cancel] at this
    exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2')
  have hmove := (rotationFusion_twist_noncentral hn (j.val : ℤ) hnc0 hnc1).2.2
  have hne : j ≠ (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) * j := by
    intro h
    apply hmove
    rw [← ZMod.intCast_eq_intCast_iff]
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one, ZMod.natCast_zmod_val]
    exact h.symm
  have hc := hI.pair j (hI.odd j hj)
  rw [show ({j, (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) * j} ∩ I : Finset _) =
      {j, (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) * j} by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, hj⟩
      · exact ⟨Or.inr rfl, haj⟩, Finset.card_pair hne] at hc
  exact absurd hc (by norm_num)

theorem odd_family_coefficient_gram (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    {I : Finset (ZMod (modulus n))}
    (hI : IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let L := multiplicityColumn basis (e (r n) : G) (modulus n)
    let φ : ZMod (modulus n) → basis.index → ℤ := fun j c => L j.val c - L 1 c
    let θ : basis.index → ℤ := fun c => L 0 c - L ((modulus n / 2 : ℕ) : ℤ) c
    let η : ℕ → basis.index → ℤ := fun l c => L 0 c - L (2 * l) c
    (∀ j ∈ I, ∀ k ∈ I, j ≠ 1 → k ≠ 1 →
      ∑ c ∈ B, φ j c * φ k c = 1 + if j = k then 1 else 0) ∧
    (∀ j ∈ I, ∑ c ∈ B, φ j c * θ c = 0) ∧ (∀ j ∈ I, ∀ l : ℕ, ∑ c ∈ B, φ j c * η l c = 0) := by
  intro B L φ θ η
  obtain ⟨hM4, hKeven, hK2, -⟩ := modulus_eq_four_mul hn
  have hgram := multiplicityColumn_difference_gram hn e basis ideal principal hprincipal
  have hMeven : Even (modulus n) := ⟨2 * 2 ^ (n - 3), by omega⟩
  have haodd : Odd (((modulus n / 2 : ℕ) : ℤ) - 1) := ⟨((2 ^ (n - 3) : ℕ) : ℤ) - 1, by omega⟩
  have hhalfeven : Even ((modulus n / 2 : ℕ) : ℤ) := ⟨((2 ^ (n - 3) : ℕ) : ℤ), by omega⟩
  have hjodd : ∀ j ∈ I, Odd ((j.val : ℕ) : ℤ) := fun j hj => by exact_mod_cast hI.odd j hj
  have hone : (1 : ZMod (modulus n)) ∈ I := hI.one_mem
  have hnotI : ∀ j ∈ I, (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) * j ∉ I := fun j hj =>
    twist_mul_not_mem_of_isOddResidueTransversal hn hI hj
  have hz : ∀ x y : ℤ, Odd x → Even y → residueIndicator (modulus n) x y = 0 := fun x y hx hy =>
    residueIndicator_eq_zero_of_odd_sub hMeven (hx.sub_even hy)
  refine ⟨fun j hj k hk hj1 hk1 => ?_, fun j hj => ?_, fun j hj l => ?_⟩
  · have hev : Even (((j.val : ℕ) : ℤ) - 1) := (hjodd j hj).sub_odd odd_one
    rw [hgram _ 1 _ 1 hev]
    simp only [residueIndicator_eq_zmod, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
      Int.cast_one, ZMod.natCast_zmod_val, mul_one]
    have h3 : ¬ (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) * j = k := fun h =>
      hnotI j hj (by rw [h]; exact hk)
    have h4 : ¬ (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) * j = 1 := fun h =>
      hnotI j hj (by rw [h]; exact hone)
    have ha1 := hnotI 1 hone
    rw [mul_one] at ha1
    have h5 : ¬ ((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1 = k := fun h =>
      ha1 (by rw [h]; exact hk)
    have h6 : ¬ ((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1 = 1 := fun h =>
      ha1 (by rw [h]; exact hone)
    have h2 : ¬ (1 : ZMod (modulus n)) = k := fun h => hk1 h.symm
    simp only [hj1, h2, h3, h4, h5, h6, ite_false, ite_true]
    split_ifs <;> norm_num
  · have hev : Even (((j.val : ℕ) : ℤ) - 1) := (hjodd j hj).sub_odd odd_one
    rw [hgram _ 1 0 _ hev, hz _ _ (hjodd j hj) Even.zero, hz _ _ (hjodd j hj) hhalfeven,
      hz _ _ odd_one Even.zero, hz _ _ odd_one hhalfeven, hz _ _ (haodd.mul (hjodd j hj)) Even.zero,
      hz _ _ (haodd.mul (hjodd j hj)) hhalfeven, hz _ _ (haodd.mul odd_one) Even.zero,
      hz _ _ (haodd.mul odd_one) hhalfeven]
    norm_num
  · have hev : Even (((j.val : ℕ) : ℤ) - 1) := (hjodd j hj).sub_odd odd_one
    have h2l : Even (2 * (l : ℤ)) := even_two_mul _
    rw [hgram _ 1 0 _ hev, hz _ _ (hjodd j hj) Even.zero, hz _ _ (hjodd j hj) h2l,
      hz _ _ odd_one Even.zero, hz _ _ odd_one h2l, hz _ _ (haodd.mul (hjodd j hj)) Even.zero,
      hz _ _ (haodd.mul (hjodd j hj)) h2l, hz _ _ (haodd.mul odd_one) Even.zero,
      hz _ _ (haodd.mul odd_one) h2l]
    norm_num

theorem basis_combination_two (basis : FiniteIrreducibleCharacterBasis G) {B : Finset basis.index}
    {y s : basis.index} (hy : y ∈ B) (hs : s ∈ B) (b c : ℤ) (g : G) :
    ∑ d ∈ B, (((b * (if d = y then 1 else 0) + c * (if d = s then 1 else 0) : ℤ)) : ℂ) *
        (basis.representation d).character g =
      b * (basis.representation y).character g + c * (basis.representation s).character g := by
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', hy, hs, ite_true]

theorem odd_cyclic_principal_Fourier_family (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (I : Finset (ZMod (modulus n)))
    (hI : IsOddResidueTransversal (((modulus n / 2 : ℕ) : ZMod (modulus n)) - 1) I) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : G := (e (r n) : G)
    let M : ℕ := modulus n
    let χ : basis.index → G → ℂ := fun c => (basis.representation c).character
    let L := multiplicityColumn basis ρ M
    let φ : ZMod M → basis.index → ℤ := fun j c => L j.val c - L 1 c
    let θ : basis.index → ℤ := fun c => L 0 c - L ((M / 2 : ℕ) : ℤ) c
    let η : ℕ → basis.index → ℤ := fun l c => L 0 c - L (2 * l) c
    let f : ZMod M → G → ℂ := fun j => principalCyclicProjection basis B ρ
      (fun x => cyclicLinearCharacter ρ M j.val x - cyclicLinearCharacter ρ M 1 x)
    let Θ := principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x)
    let E := fun l : ℕ => principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
    I.card = M / 4 ∧
    (∀ (j : ZMod M) c, characterPairing (fun x : Subgroup.zpowers ρ => χ c x)
        (fun x => cyclicLinearCharacter ρ M j.val x - cyclicLinearCharacter ρ M 1 x) = φ j c) ∧
    (∀ (j : ZMod M) g, f j g = ∑ c ∈ B, (φ j c : ℂ) * χ c g) ∧
    f 1 = 0 ∧ (∀ j ∈ I, f j 1 = 0) ∧ (∀ j ∈ I, φ j principal = 0) ∧
    (∀ j ∈ I, characterPairing (f j) 1 = 0) ∧
    (∀ j ∈ I, ∀ k ∈ I, j ≠ 1 → k ≠ 1 → ∑ c ∈ B, φ j c * φ k c = 1 + if j = k then 1 else 0) ∧
    (∀ j ∈ I, ∀ k ∈ I, j ≠ 1 → k ≠ 1 →
      characterPairing (f j) (f k) = 1 + if j = k then 1 else 0) ∧
    (∀ j ∈ I, ∑ c ∈ B, φ j c * θ c = 0 ∧ characterPairing (f j) Θ = 0) ∧
    (∀ j ∈ I, ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 →
      ∑ c ∈ B, φ j c * η l c = 0 ∧ characterPairing (f j) (E l) = 0) ∧
    ∃ (εo : ℤ) (ν : ZMod M → basis.index) (d : ℕ), (εo = 1 ∨ εo = -1) ∧ 0 < d ∧
      (∀ j ∈ I, ∀ k ∈ I, ν j = ν k → j = k) ∧
      (∀ j ∈ I, ν j ∈ B ∧ ν j ≠ principal ∧ χ (ν j) 1 = d) ∧
      (∀ j ∈ I, f j = (εo : ℂ) • (χ (ν j) - χ (ν 1))) ∧
      (∀ j ∈ I, ∀ c ∈ B,
        φ j c = εo * ((if c = ν j then 1 else 0) - (if c = ν 1 then 1 else 0))) ∧
      ∀ (c₁ c₂ c₃ : basis.index) (δ₁ δ₂ δ₃ εe : ℤ) (ψ : ℕ → basis.index),
        c₁ ∈ B → c₂ ∈ B → c₃ ∈ B → c₁ ≠ c₂ → c₁ ≠ c₃ → c₂ ≠ c₃ →
        c₁ ≠ principal → c₂ ≠ principal → c₃ ≠ principal →
        (δ₁ = 1 ∨ δ₁ = -1) → (δ₂ = 1 ∨ δ₂ = -1) → (δ₃ = 1 ∨ δ₃ = -1) → (εe = 1 ∨ εe = -1) →
        (∀ j l : ℕ, 1 ≤ j → j ≤ M / 4 - 1 → 1 ≤ l → l ≤ M / 4 - 1 → ψ j = ψ l → j = l) →
        (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 →
          ψ l ∈ B ∧ ψ l ≠ principal ∧ ψ l ≠ c₁ ∧ ψ l ≠ c₂ ∧ ψ l ≠ c₃) →
        Θ = 1 + (δ₁ : ℂ) • χ c₁ + (δ₂ : ℂ) • χ c₂ + (δ₃ : ℂ) • χ c₃ →
        (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → E l = 1 + (δ₁ : ℂ) • χ c₁ + (εe : ℂ) • χ (ψ l)) →
        (∀ j ∈ I, ν j ≠ c₁ ∧ ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ν j ≠ ψ l) ∧
        (5 ≤ n → (∀ j ∈ I, ν j ≠ c₂ ∧ ν j ≠ c₃) ∧ M / 2 + 3 ≤ B.card) ∧
        (n = 4 → (∀ j ∈ I, ν j ≠ c₂ ∧ ν j ≠ c₃) ∨
          (I.image ν = {c₂, c₃} ∧ δ₂ = δ₃ ∧ χ (ψ 1) 1 = 2 * d)) := by
  intro B ρ M χ L φ θ η f Θ E
  obtain ⟨hM4, hKeven, hK2, -⟩ := modulus_eq_four_mul hn
  have hM4' : M = 4 * 2 ^ (n - 3) := hM4
  have hpB : principal ∈ B := coefficientBlock_self_mem _ _ _
  have : Fact (1 < modulus n) := ⟨by omega⟩
  have hIcard : I.card = M / 4 := by
    have h := (sum_range_odd_transversal_columns hM4 hKeven hK2 (fun _ => (0 : ℤ))
      (fun _ _ _ => rfl) (fun _ => rfl) _ (supplied_twist_val hn) I hI.odd hI.pair).2
    omega
  have hcoef : ∀ (j : ZMod M) c, characterPairing (fun x : Subgroup.zpowers ρ => χ c x)
      (fun x => cyclicLinearCharacter ρ M j.val x - cyclicLinearCharacter ρ M 1 x) = φ j c :=
    fun j c => characterPairing_linear_difference hn e basis _ _ c
  have hfapply : ∀ (j : ZMod M) g, f j g = ∑ c ∈ B, (φ j c : ℂ) * χ c g := fun j =>
    principalCyclicProjection_apply basis B ρ _ (φ j) (hcoef j)
  have hffun : ∀ j, f j = fun g => ∑ c ∈ B, (φ j c : ℂ) * χ c g := fun j => funext (hfapply j)
  have hφ1 : ∀ c, φ 1 c = 0 := fun c => by
    show multiplicityColumn basis (e (r n) : G) (modulus n) (((1 : ZMod (modulus n)).val : ℕ) : ℤ)
      c - multiplicityColumn basis (e (r n) : G) (modulus n) 1 c = 0
    rw [ZMod.val_one, Nat.cast_one, sub_self]
  have hf1 : f 1 = 0 := by
    funext g
    rw [hfapply 1 g]
    simp [hφ1]
  have hvals := (cyclic_principal_Fourier_projection_values hn e basis ideal principal
    hprincipal).2.1 1 (by rw [orderOf_one]; exact odd_one)
  have hjodd : ∀ j ∈ I, Odd ((j.val : ℕ) : ℤ) := fun j hj => by exact_mod_cast hI.odd j hj
  have hfdeg1 : ∀ j ∈ I, f j 1 = 0 := fun j hj => hvals.2.2 _ (hjodd j hj)
  have hLp := multiplicityColumn_principal hn e basis hprincipal
  have hφp : ∀ j ∈ I, φ j principal = 0 := by
    intro j hj
    show multiplicityColumn basis (e (r n) : G) (modulus n) ((j.val : ℕ) : ℤ) principal -
      multiplicityColumn basis (e (r n) : G) (modulus n) 1 principal = 0
    have hjpos : 0 < j.val := (hI.odd j hj).pos
    have hjlt : j.val < modulus n := ZMod.val_lt j
    rw [hLp, hLp, ite_eq_right, ite_eq_right]
    · norm_num
    · intro hd
      have := Int.le_of_dvd one_pos hd
      omega
    · intro hd
      have := Int.le_of_dvd (by exact_mod_cast hjpos) hd
      omega
  have hpair1 : ∀ j ∈ I, characterPairing (f j) 1 = 0 := by
    intro j hj
    rw [hffun j, characterPairing_basis_combination_one basis hprincipal hpB]
    exact_mod_cast hφp j hj
  obtain ⟨hφφ, hφθ, hφη⟩ := odd_family_coefficient_gram hn e basis ideal principal hprincipal hI
  obtain ⟨hcoefΘ, hcoefE, hΘapply, hEapply, hΘ1, hE1, -⟩ :=
    even_cyclic_principal_Fourier_family hn e basis ideal principal hprincipal
  have hΘfun : Θ = fun g => ∑ c ∈ B, (θ c : ℂ) * χ c g := funext hΘapply
  have hEfun : ∀ l : ℕ, E l = fun g => ∑ c ∈ B, (η l c : ℂ) * χ c g := fun l => funext (hEapply l)
  have hpairff : ∀ j ∈ I, ∀ k ∈ I, j ≠ 1 → k ≠ 1 →
      characterPairing (f j) (f k) = 1 + if j = k then 1 else 0 := by
    intro j hj k hk hj1 hk1
    rw [hffun j, hffun k, characterPairing_basis_combination basis B (fun c => (φ j c : ℂ))]
    have h := hφφ j hj k hk hj1 hk1
    split_ifs at h ⊢ <;> exact_mod_cast h
  have hpairfΘ : ∀ j ∈ I, characterPairing (f j) Θ = 0 := by
    intro j hj
    rw [hffun j, hΘfun, characterPairing_basis_combination basis B (fun c => (φ j c : ℂ))]
    exact_mod_cast hφθ j hj
  have hpairfE : ∀ j ∈ I, ∀ l : ℕ, characterPairing (f j) (E l) = 0 := by
    intro j hj l
    rw [hffun j, hEfun l, characterPairing_basis_combination basis B (fun c => (φ j c : ℂ))]
    exact_mod_cast hφη j hj l
  let deg : basis.index → ℤ := fun c => (Module.finrank ℂ (basis.representation c).vector : ℤ)
  have hdegpos : ∀ c ∈ B, 0 < deg c := fun c _ => by
    show (0 : ℤ) < (Module.finrank ℂ (basis.representation c).vector : ℤ)
    exact_mod_cast (basis_character_one basis c).2
  have hdegval : ∀ c, χ c 1 = (deg c : ℂ) := fun c => by
    show (basis.representation c).character 1 =
      (((Module.finrank ℂ (basis.representation c).vector : ℤ)) : ℂ)
    rw [(basis_character_one basis c).1]
    push_cast
    rfl
  have hφdeg : ∀ j ∈ I, ∑ c ∈ B, φ j c * deg c = 0 := by
    intro j hj
    have h := hfapply j 1
    rw [hfdeg1 j hj, basis_combination_one basis B (φ j)] at h
    exact_mod_cast h.symm
  have hcardI : 2 ≤ Fintype.card {j // j ∈ I} := by
    rw [Fintype.card_coe, hIcard]
    omega
  obtain ⟨εo, ν', hεo, hν'inj, hν'B, hν'deg, hν'form⟩ :=
    degree_zero_difference_star_coordinates_of_two_le (⟨1, hI.one_mem⟩ : {j // j ∈ I}) hcardI B
      deg hdegpos (fun j c => φ j.val c) (fun c _ => hφ1 c) (fun j => hφdeg j.val j.2)
      (fun j k hj hk => by
        have hj1 : j.val ≠ 1 := fun h => hj (Subtype.ext h)
        have hk1 : k.val ≠ 1 := fun h => hk (Subtype.ext h)
        have h := hφφ j.val j.2 k.val k.2 hj1 hk1
        by_cases hjk : j = k
        · rw [ite_eq_left hjk]
          rw [ite_eq_left (congrArg Subtype.val hjk)] at h
          exact h
        · rw [ite_eq_right hjk]
          rw [ite_eq_right (fun h' => hjk (Subtype.ext h'))] at h
          exact h)
  let ν : ZMod M → basis.index := fun j => if h : j ∈ I then ν' ⟨j, h⟩ else principal
  have hν : ∀ j (h : j ∈ I), ν j = ν' ⟨j, h⟩ := fun j h => dite_eq_left h
  have hν1 : ν 1 = ν' ⟨1, hI.one_mem⟩ := hν 1 hI.one_mem
  have hνB : ∀ j ∈ I, ν j ∈ B := fun j hj => by rw [hν j hj]; exact hν'B _
  have hνinj : ∀ j ∈ I, ∀ k ∈ I, ν j = ν k → j = k := fun j hj k hk h => by
    rw [hν j hj, hν k hk] at h
    exact congrArg Subtype.val (hν'inj h)
  have hφform : ∀ j ∈ I, ∀ c ∈ B,
      φ j c = εo * ((if c = ν j then 1 else 0) - (if c = ν 1 then 1 else 0)) := by
    intro j hj c hc
    rw [hν j hj, hν1]
    exact hν'form ⟨j, hj⟩ c hc
  obtain ⟨j₀, hj₀, hj₀1⟩ : ∃ j₀ ∈ I, j₀ ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : I ⊆ {1} := fun j hj => Finset.mem_singleton.mpr (h j hj)
    have hc := Finset.card_le_card hsub
    rw [hIcard, Finset.card_singleton] at hc
    omega
  have hνp : ∀ j ∈ I, ν j ≠ principal := by
    have h1 : ν 1 ≠ principal := by
      intro h
      have h0 := hφform j₀ hj₀ principal hpB
      rw [hφp j₀ hj₀, ite_eq_left h.symm] at h0
      by_cases hpj : principal = ν j₀
      · exact hj₀1 (hνinj j₀ hj₀ 1 hI.one_mem (hpj.symm.trans h.symm))
      · rw [ite_eq_right hpj] at h0
        rcases hεo with rfl | rfl <;> norm_num at h0
    intro j hj hjp
    have h0 := hφform j hj principal hpB
    rw [hφp j hj, ite_eq_left hjp.symm, ite_eq_right (Ne.symm h1)] at h0
    rcases hεo with rfl | rfl <;> norm_num at h0
  let d : ℕ := Module.finrank ℂ (basis.representation (ν 1)).vector
  have hd : 0 < d := (basis_character_one basis (ν 1)).2
  have hνdeg : ∀ j ∈ I, deg (ν j) = (d : ℤ) := by
    intro j hj
    rw [hν j hj, hν'deg ⟨j, hj⟩ ⟨1, hI.one_mem⟩, ← hν1]
  have hνdeg' : ∀ j ∈ I, χ (ν j) 1 = d := fun j hj => by
    rw [hdegval, hνdeg j hj]
    push_cast
    rfl
  have hfdiff : ∀ j ∈ I, f j = (εo : ℂ) • (χ (ν j) - χ (ν 1)) := by
    intro j hj
    funext g
    have hsum : ∑ c ∈ B, (φ j c : ℂ) * χ c g = ∑ c ∈ B, (((εo * (if c = ν j then 1 else 0) +
        (-εo) * (if c = ν 1 then 1 else 0) : ℤ)) : ℂ) * (basis.representation c).character g :=
      Finset.sum_congr rfl fun c hc => by
        rw [hφform j hj c hc]
        congr 1
        push_cast
        ring
    rw [hfapply j g, hsum, basis_combination_two basis (hνB j hj) (hνB 1 hI.one_mem)]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    push_cast
    ring
  refine ⟨hIcard, hcoef, hfapply, hf1, hfdeg1, hφp, hpair1, hφφ, hpairff,
    fun j hj => ⟨hφθ j hj, hpairfΘ j hj⟩, fun j hj l _ _ => ⟨hφη j hj l, hpairfE j hj l⟩,
    εo, ν, d, hεo, hd, hνinj, fun j hj => ⟨hνB j hj, hνp j hj, hνdeg' j hj⟩, hfdiff, hφform, ?_⟩
  intro c₁ c₂ c₃ δ₁ δ₂ δ₃ εe ψ hc₁B hc₂B hc₃B h12 h13 h23 hc₁p hc₂p hc₃p hδ₁ hδ₂ hδ₃ hεe hψinj
    hψavoid hΘdec hEdec
  have hJ1 : 1 ≤ M / 4 - 1 := by omega
  have hθform : ∀ c ∈ B, θ c = (if c = principal then 1 else 0) +
      δ₁ * (if c = c₁ then 1 else 0) + δ₂ * (if c = c₂ then 1 else 0) +
      δ₃ * (if c = c₃ then 1 else 0) := by
    intro c hc
    have hfun : (fun g => ∑ d ∈ B, (θ d : ℂ) * (basis.representation d).character g) =
        fun g => ∑ d ∈ B, ((((if d = principal then 1 else 0) + δ₁ * (if d = c₁ then 1 else 0) +
          δ₂ * (if d = c₂ then 1 else 0) + δ₃ * (if d = c₃ then 1 else 0) : ℤ)) : ℂ) *
            (basis.representation d).character g := by
      funext g
      rw [basis_combination_four basis hpB hc₁B hc₂B hc₃B, hprincipal]
      have h := (hΘapply g).symm.trans (congrFun hΘdec g)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h
      exact h
    have h1 := basis_combination_coefficient basis hc (fun d => (θ d : ℂ))
    have h2 := basis_combination_coefficient basis hc (fun d =>
      ((((if d = principal then 1 else 0) + δ₁ * (if d = c₁ then 1 else 0) +
        δ₂ * (if d = c₂ then 1 else 0) + δ₃ * (if d = c₃ then 1 else 0) : ℤ)) : ℂ))
    rw [hfun] at h1
    exact_mod_cast h1.symm.trans h2
  have hηform : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ∀ c ∈ B, η l c =
      (if c = principal then 1 else 0) + δ₁ * (if c = c₁ then 1 else 0) +
        εe * (if c = ψ l then 1 else 0) := by
    intro l hl1 hl2 c hc
    obtain ⟨hψB, -⟩ := hψavoid l hl1 hl2
    have hfun : (fun g => ∑ d ∈ B, (η l d : ℂ) * (basis.representation d).character g) =
        fun g => ∑ d ∈ B, ((((if d = principal then 1 else 0) + δ₁ * (if d = c₁ then 1 else 0) +
          εe * (if d = ψ l then 1 else 0) : ℤ)) : ℂ) * (basis.representation d).character g := by
      funext g
      rw [basis_combination_three basis hpB hc₁B hψB, hprincipal]
      have h := (hEapply l g).symm.trans (congrFun (hEdec l hl1 hl2) g)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h
      exact h
    have h1 := basis_combination_coefficient basis hc (fun d => (η l d : ℂ))
    have h2 := basis_combination_coefficient basis hc (fun d =>
      ((((if d = principal then 1 else 0) + δ₁ * (if d = c₁ then 1 else 0) +
        εe * (if d = ψ l then 1 else 0) : ℤ)) : ℂ))
    rw [hfun] at h1
    exact_mod_cast h1.symm.trans h2
  have hθval : ∀ x ∈ B, x ≠ principal → θ x = δ₁ * (if x = c₁ then 1 else 0) +
      δ₂ * (if x = c₂ then 1 else 0) + δ₃ * (if x = c₃ then 1 else 0) := by
    intro x hx hxp
    rw [hθform x hx, ite_eq_right hxp]
    ring
  have hηval : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ∀ x ∈ B, x ≠ principal →
      η l x = δ₁ * (if x = c₁ then 1 else 0) + εe * (if x = ψ l then 1 else 0) := by
    intro l hl1 hl2 x hx hxp
    rw [hηform l hl1 hl2 x hx, ite_eq_right hxp]
    ring
  have hE1deg : 1 + δ₁ * deg c₁ + εe * deg (ψ 1) = 0 := by
    have h := (hE1 1 le_rfl hJ1).symm.trans (congrFun (hEdec 1 le_rfl hJ1) 1)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h
    rw [hdegval, hdegval] at h
    exact_mod_cast h.symm
  have hεeδ : εe = -δ₁ := by
    have hd1 := hdegpos c₁ hc₁B
    have hdψ := hdegpos (ψ 1) (hψavoid 1 le_rfl hJ1).1
    rcases hδ₁ with rfl | rfl <;> rcases hεe with rfl | rfl <;> omega
  have hθν : ∀ j ∈ I, θ (ν j) = θ (ν 1) := by
    intro j hj
    have h := hφθ j hj
    have hsum : ∑ c ∈ B, φ j c * θ c = ∑ c ∈ B, θ c * (εo * (if c = ν j then 1 else 0) +
        (-εo) * (if c = ν 1 then 1 else 0)) :=
      Finset.sum_congr rfl fun c hc => by rw [hφform j hj c hc]; ring
    rw [hsum, sum_mul_two_labels B θ (hνB j hj) (hνB 1 hI.one_mem)] at h
    rcases hεo with rfl | rfl <;> linarith
  have hην : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ∀ j ∈ I, η l (ν j) = η l (ν 1) := by
    intro l _ _ j hj
    have h := hφη j hj l
    have hsum : ∑ c ∈ B, φ j c * η l c = ∑ c ∈ B, η l c * (εo * (if c = ν j then 1 else 0) +
        (-εo) * (if c = ν 1 then 1 else 0)) :=
      Finset.sum_congr rfl fun c hc => by rw [hφform j hj c hc]; ring
    rw [hsum, sum_mul_two_labels B (η l) (hνB j hj) (hνB 1 hI.one_mem)] at h
    rcases hεo with rfl | rfl <;> linarith
  have hother : ∀ j ∈ I, ∃ j' ∈ I, j' ≠ j := by
    intro j hj
    by_cases hj1 : j = 1
    · exact ⟨j₀, hj₀, by rw [hj1]; exact hj₀1⟩
    · exact ⟨1, hI.one_mem, Ne.symm hj1⟩
  have havoid : ∀ j ∈ I, ν j ≠ c₁ ∧ ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ν j ≠ ψ l := by
    intro j hj
    obtain ⟨j', hj', hj'j⟩ := hother j hj
    have hνne : ν j' ≠ ν j := fun h => hj'j (hνinj j' hj' j hj h)
    refine ⟨fun hjc => ?_, fun l hl1 hl2 hjψ => ?_⟩
    · have hj'c : ν j' ≠ c₁ := fun h => hνne (h.trans hjc.symm)
      obtain ⟨-, -, hψ1, -, -⟩ := hψavoid 1 le_rfl hJ1
      have h := (hην 1 le_rfl hJ1 j' hj').trans (hην 1 le_rfl hJ1 j hj).symm
      rw [hηval 1 le_rfl hJ1 _ (hνB j' hj') (hνp j' hj'),
        hηval 1 le_rfl hJ1 _ (hνB j hj) (hνp j hj), hjc, ite_eq_right hj'c, ite_eq_left rfl,
        ite_eq_right (Ne.symm hψ1), hεeδ] at h
      split_ifs at h <;> omega
    · have hj'ψ : ν j' ≠ ψ l := fun h => hνne (h.trans hjψ.symm)
      obtain ⟨-, -, hψ1, -, -⟩ := hψavoid l hl1 hl2
      have h := (hην l hl1 hl2 j' hj').trans (hην l hl1 hl2 j hj).symm
      rw [hηval l hl1 hl2 _ (hνB j' hj') (hνp j' hj'),
        hηval l hl1 hl2 _ (hνB j hj) (hνp j hj), hjψ, ite_eq_right hj'ψ, ite_eq_left rfl,
        ite_eq_right hψ1, hεeδ] at h
      split_ifs at h <;> omega
  have hcases : ∀ x ∈ B, x ≠ principal → x ≠ c₁ → θ x ≠ 0 → x = c₂ ∨ x = c₃ := by
    intro x hx hxp hx1 hθx
    rw [hθval x hx hxp, ite_eq_right hx1] at hθx
    by_contra h
    push Not at h
    rw [ite_eq_right h.1, ite_eq_right h.2] at hθx
    simp at hθx
  have havoid23 : θ (ν 1) = 0 → ∀ j ∈ I, ν j ≠ c₂ ∧ ν j ≠ c₃ := by
    intro hv j hj
    have h := hθν j hj
    rw [hv] at h
    constructor
    · intro hjc
      rw [hjc, hθval c₂ hc₂B hc₂p, ite_eq_right (Ne.symm h12), ite_eq_left rfl,
        ite_eq_right h23] at h
      rcases hδ₂ with rfl | rfl <;> omega
    · intro hjc
      rw [hjc, hθval c₃ hc₃B hc₃p, ite_eq_right (Ne.symm h13), ite_eq_right (Ne.symm h23),
        ite_eq_left rfl] at h
      rcases hδ₃ with rfl | rfl <;> omega
  have hcover : θ (ν 1) ≠ 0 → I.image ν ⊆ {c₂, c₃} := by
    intro hv x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    rcases hcases (ν j) (hνB j hj) (hνp j hj) (havoid j hj).1 (by rw [hθν j hj]; exact hv) with
      h | h <;> simp [h]
  have himage : (I.image ν).card = I.card :=
    Finset.card_image_of_injOn fun j hj k hk h =>
      hνinj j (Finset.mem_coe.mp hj) k (Finset.mem_coe.mp hk) h
  refine ⟨havoid, fun h5 => ?_, fun h4 => ?_⟩
  ·
    have hKbig : 4 ≤ 2 ^ (n - 3) := by
      have : 2 ^ 2 ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this
    have hv : θ (ν 1) = 0 := by
      by_contra hv
      have hc := Finset.card_le_card (hcover hv)
      rw [himage, hIcard, Finset.card_pair h23] at hc
      omega
    refine ⟨havoid23 hv, ?_⟩
    let T : Finset basis.index := {principal, c₁, c₂, c₃}
    let U : Finset basis.index := (Finset.Icc 1 (M / 4 - 1)).image ψ
    have hT : T.card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h23]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h12, h13⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hc₁p.symm, hc₂p.symm, hc₃p.symm⟩
    have hU : U.card = M / 4 - 1 := by
      rw [Finset.card_image_of_injOn, Nat.card_Icc]
      · omega
      · intro j hj l hl h
        have hj' := Finset.mem_Icc.mp (Finset.mem_coe.mp hj)
        have hl' := Finset.mem_Icc.mp (Finset.mem_coe.mp hl)
        exact hψinj j l hj'.1 hj'.2 hl'.1 hl'.2 h
    have hTU : Disjoint T U := by
      rw [Finset.disjoint_left]
      intro x hxT hxU
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hxU
      obtain ⟨-, hψp, hψ1, hψ2, hψ3⟩ :=
        hψavoid l (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with h | h | h | h
      · exact hψp h
      · exact hψ1 h
      · exact hψ2 h
      · exact hψ3 h
    have hTV : Disjoint T (I.image ν) := by
      rw [Finset.disjoint_left]
      intro x hxT hxV
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hxV
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with h | h | h | h
      · exact hνp j hj h
      · exact (havoid j hj).1 h
      · exact (havoid23 hv j hj).1 h
      · exact (havoid23 hv j hj).2 h
    have hUV : Disjoint U (I.image ν) := by
      rw [Finset.disjoint_left]
      intro x hxU hxV
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hxU
      obtain ⟨j, hj, hjl⟩ := Finset.mem_image.mp hxV
      exact (havoid j hj).2 l (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2 hjl
    have hsub : T ∪ U ∪ I.image ν ⊆ B := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hpB
          · exact hc₁B
          · exact hc₂B
          · exact hc₃B
        · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
          exact (hψavoid l (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2).1
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        exact hνB j hj
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hTV, hUV⟩),
      Finset.card_union_of_disjoint hTU, hT, hU, himage, hIcard] at hc
    omega
  ·
    have hK : 2 ^ (n - 3) = 2 := by rw [h4]; norm_num
    by_cases hv : θ (ν 1) = 0
    · exact Or.inl (havoid23 hv)
    · right
      have himeq : I.image ν = {c₂, c₃} := Finset.eq_of_subset_of_card_le (hcover hv) (by
        rw [Finset.card_pair h23, himage, hIcard]
        omega)
      have hc₂mem : c₂ ∈ I.image ν := by rw [himeq]; simp
      have hc₃mem : c₃ ∈ I.image ν := by rw [himeq]; simp
      obtain ⟨j₂, hj₂, hj₂eq⟩ := Finset.mem_image.mp hc₂mem
      obtain ⟨j₃, hj₃, hj₃eq⟩ := Finset.mem_image.mp hc₃mem
      have hθc₂ : θ c₂ = δ₂ := by
        rw [hθval c₂ hc₂B hc₂p, ite_eq_right (Ne.symm h12), ite_eq_left rfl, ite_eq_right h23]
        ring
      have hθc₃ : θ c₃ = δ₃ := by
        rw [hθval c₃ hc₃B hc₃p, ite_eq_right (Ne.symm h13), ite_eq_right (Ne.symm h23),
          ite_eq_left rfl]
        ring
      have hδ : δ₂ = δ₃ := by
        rw [← hθc₂, ← hθc₃, ← hj₂eq, ← hj₃eq, hθν j₂ hj₂, hθν j₃ hj₃]
      have hdc₂ : deg c₂ = d := by rw [← hj₂eq]; exact hνdeg j₂ hj₂
      have hdc₃ : deg c₃ = d := by rw [← hj₃eq]; exact hνdeg j₃ hj₃
      have hΘdeg : 1 + δ₁ * deg c₁ + δ₂ * deg c₂ + δ₃ * deg c₃ = 0 := by
        have h := hΘ1.symm.trans (congrFun hΘdec 1)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h
        rw [hdegval, hdegval, hdegval] at h
        exact_mod_cast h.symm
      have hdψ := hdegpos (ψ 1) (hψavoid 1 le_rfl hJ1).1
      have hdpos : (0 : ℤ) < d := by exact_mod_cast hd
      have hdψ2 : deg (ψ 1) = 2 * d := by
        rw [hdc₂, hdc₃, ← hδ] at hΘdeg
        rcases hδ₂ with rfl | rfl <;> rcases hεe with rfl | rfl <;> omega
      refine ⟨himeq, hδ, ?_⟩
      rw [hdegval, hdψ2]
      push_cast
      ring

end CFSG.Semidihedral.Principal

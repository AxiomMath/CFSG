module

public import CFSG.CharacterTheory.Semidihedral.Principal.EvenFourierFamily
public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Open

variable {H : Type*} [Group H] [Fintype H] {n : ℕ} {S : Sylow 2 H}

omit [Fintype H] in
theorem degree_one_character_pow (data : FiniteComplexRepresentation H)
    (hdegree : data.character 1 = 1) (x : H) (v : ℕ) :
    data.character (x ^ v) = data.character x ^ v := by
  induction v with
  | zero => rw [pow_zero, pow_zero, hdegree]
  | succ v ih => rw [pow_succ, character_mul_of_degree_eq_one data hdegree, ih, pow_succ]

theorem characterPairing_rotation_scalar (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup H)) (F F' h : Subgroup.zpowers (e (r n) : H) → ℂ)
    (c : ℂ) (hF : ∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] → ¬ v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      F ⟨(e (r n) : H) ^ v, Subgroup.zpow_mem_zpowers _ _⟩ =
        c * F' ⟨(e (r n) : H) ^ v, Subgroup.zpow_mem_zpowers _ _⟩)
    (h1 : h 1 = 0) (ht : h ⟨(e (r n) : H) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0) :
    characterPairing F h = c * characterPairing F' h := by
  have hord := suppliedRotation_orderOf (by omega) e
  rw [characterPairing_zpowers_eq_sum_range hord, characterPairing_zpowers_eq_sum_range hord,
    mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv0 : (v : ℤ) ≡ 0 [ZMOD modulus n]
  · have hx : (⟨(e (r n) : H) ^ (-(v : ℤ)), Subgroup.zpow_mem_zpowers _ _⟩ :
        Subgroup.zpowers (e (r n) : H)) = 1 := Subtype.ext (by
      show (e (r n) : H) ^ (-(v : ℤ)) = 1
      rw [← zpow_zero (e (r n) : H), suppliedRotation_zpow_eq_iff (by omega) e]
      simpa using hv0.neg)
    rw [hx, h1]
    ring
  by_cases hv1 : (v : ℤ) ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]
  · have hx : (⟨(e (r n) : H) ^ (-(v : ℤ)), Subgroup.zpow_mem_zpowers _ _⟩ :
        Subgroup.zpowers (e (r n) : H)) =
        ⟨(e (r n) : H) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ := Subtype.ext (by
      show (e (r n) : H) ^ (-(v : ℤ)) = (e (r n) : H) ^ (modulus n / 2)
      rw [← zpow_natCast (e (r n) : H) (modulus n / 2), suppliedRotation_zpow_eq_iff (by omega) e]
      refine hv1.neg.trans ?_
      rw [Int.modEq_iff_dvd]
      obtain ⟨hM4, -, hK2, -⟩ := modulus_eq_four_mul hn
      exact ⟨1, by omega⟩)
    rw [hx, ht]
    ring
  · rw [hF v hv0 hv1]
    ring

theorem characterPairing_sign_character_even_difference (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup H)) (data : FiniteComplexRepresentation H)
    (hdegree : data.character 1 = 1) (hr : data.character (e (r n) : H) = -1) {l : ℕ}
    (hl1 : 1 ≤ l) (hl2 : l ≤ modulus n / 4 - 1) :
    characterPairing (fun x : Subgroup.zpowers (e (r n) : H) => data.character x)
      (fun x => 1 - cyclicLinearCharacter (e (r n) : H) (modulus n) (2 * l) x) = 0 := by
  have hord := suppliedRotation_orderOf (by omega) e
  have hM : 0 < modulus n := by unfold modulus; positivity
  obtain ⟨hM4, -, hK2, -⟩ := modulus_eq_four_mul hn
  rw [characterPairing_zpowers_eq_sum_range hord]
  have hterm : ∀ v : ℕ, data.character ((e (r n) : H) ^ ((v : ℕ) : ℤ)) *
      (1 - cyclicLinearCharacter (e (r n) : H) (modulus n) (2 * l)
        ⟨(e (r n) : H) ^ (-(v : ℤ)), Subgroup.zpow_mem_zpowers _ _⟩) =
      cyclicRoot (modulus n) ^ ((((modulus n / 2 : ℕ) : ℤ) - 0) * v) -
        cyclicRoot (modulus n) ^ ((((modulus n / 2 : ℕ) : ℤ) - 2 * l) * v) := by
    intro v
    rw [zpow_natCast, degree_one_character_pow data hdegree, hr,
      cyclicLinearCharacter_zpow hord]
    have hneg : (-1 : ℂ) ^ v = cyclicRoot (modulus n) ^ ((((modulus n / 2 : ℕ) : ℤ)) * v) := by
      rw [zpow_mul, cyclicRoot_zpow_half hn, zpow_natCast]
    rw [hneg, mul_sub, mul_one, cyclicRoot_zpow_mul_neg, sub_zero]
  rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_sub_distrib, mul_sub,
    cyclicRoot_average _ hM, cyclicRoot_average _ hM, ite_eq_right, ite_eq_right, sub_zero]
  · intro hd
    have := Int.le_of_dvd (by omega) hd
    omega
  · intro hd
    have := Int.le_of_dvd (by omega) hd
    omega

omit [Fintype H] in
theorem suppliedReflection_orderOf (hn : 3 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup H)) :
    orderOf (e (s n) : H) = 2 := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_s n hn]

theorem local_even_Fourier_principal_character_column (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup H)) (basis : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (δ φ δφ : basis.index) (q : ℕ) (ε : ℤ)
    (hδdeg : (basis.representation δ).character 1 = 1)
    (_hδsq : ∀ h, (basis.representation δ).character h * (basis.representation δ).character h = 1)
    (hδr : (basis.representation δ).character (e (r n) : H) = -1)
    (hφB : φ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hφdeg : (basis.representation φ).character 1 = q) (_hq : Odd q) (hq1 : 1 < q)
    (hε : ε = 1 ∨ ε = -1)
    (hδφ : ∀ h, (basis.representation δφ).character h =
      (basis.representation δ).character h * (basis.representation φ).character h)
    (_hδB : δ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (_hδφB : δφ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (_h1δ : principal ≠ δ) (h1φ : principal ≠ φ) (_h1δφ : principal ≠ δφ) (_hδφne : δ ≠ φ)
    (_hδδφ : δ ≠ δφ) (_hφδφ : φ ≠ δφ)
    (hφt : (basis.representation φ).character ((e (r n) : H) ^ (modulus n / 2)) = q)
    (hφs : (basis.representation φ).character (e (s n) : H) = -ε)
    (hφrot : ∀ j : ℤ, ¬ j ≡ 0 [ZMOD modulus n] → ¬ j ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      (basis.representation φ).character ((e (r n) : H) ^ j) = ε) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : H := (e (r n) : H)
    let σ : H := (e (s n) : H)
    let M : ℕ := modulus n
    let t : H := ρ ^ (M / 2)
    let χ : basis.index → H → ℂ := fun c => (basis.representation c).character
    let E := fun l : ℕ => principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
    ∃ η : ℕ → basis.index,
      (∀ j l : ℕ, 1 ≤ j → j ≤ M / 4 - 1 → 1 ≤ l → l ≤ M / 4 - 1 → η j = η l → j = l) ∧
      ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 →
        η l ∈ B ∧ η l ≠ principal ∧ η l ≠ δ ∧ η l ≠ φ ∧ η l ≠ δφ ∧
        E l = 1 + (ε : ℂ) • χ φ - (ε : ℂ) • χ (η l) ∧
        χ (η l) 1 = q + ε ∧ χ (η l) t = q + ε ∧ χ (η l) σ = 0 := by
  intro B ρ σ M t χ E
  obtain ⟨hM4, -, hK2, -⟩ := modulus_eq_four_mul hn
  have hM4' : M = 4 * 2 ^ (n - 3) := hM4
  have hpB : principal ∈ B := coefficientBlock_self_mem _ _ _
  have hord : orderOf ρ = M := suppliedRotation_orderOf (by omega) e
  have hhalfLam : ∀ j : ℤ,
      cyclicLinearCharacter ρ M j ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = (-1 : ℂ) ^ j :=
    fun j => cyclicLinearCharacter_half hn e j
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨-, hcoefE, -, hEapply, -, hE1, -, hηp, -, -, -, -, hηη, -⟩ :=
    even_cyclic_principal_Fourier_family hn e basis ideal principal hprincipal
  let ηc : ℕ → basis.index → ℤ := fun l c =>
    multiplicityColumn basis ρ M 0 c - multiplicityColumn basis ρ M (2 * l) c
  have hh1 : ∀ l : ℕ, (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
      (1 : Subgroup.zpowers ρ) = 0 := fun l => by
    simp only [cyclicLinearCharacter_one hord, sub_self]
  have hht : ∀ l : ℕ, (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
      ⟨ρ ^ (M / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 := fun l => by
    simp only [hhalfLam, zpow_mul]
    norm_num
  have hone : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → characterPairing
      (fun _ : Subgroup.zpowers ρ => (1 : ℂ))
      (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x) = 1 := by
    intro l hl1 hl2
    have h := hcoefE l principal
    have hfun : (fun x : Subgroup.zpowers ρ => (basis.representation principal).character x) =
        fun _ => (1 : ℂ) := funext fun x => by rw [hprincipal]; rfl
    rw [hηp l hl1 hl2, Int.cast_one] at h
    rw [← hfun]
    exact h
  have hηφ : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ηc l φ = ε := by
    intro l hl1 hl2
    have h := hcoefE l φ
    rw [characterPairing_rotation_scalar hn e _ (fun _ => 1) _ (ε : ℂ)
      (fun v hv0 hv1 => by
        show (basis.representation φ).character ((e (r n) : H) ^ v) = (ε : ℂ) * 1
        rw [hφrot v hv0 hv1, mul_one]) (hh1 l) (hht l), hone l hl1 hl2, mul_one] at h
    exact_mod_cast h.symm
  have hηδ : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ηc l δ = 0 := by
    intro l hl1 hl2
    have h := hcoefE l δ
    rw [characterPairing_sign_character_even_difference hn e _ hδdeg hδr hl1 hl2] at h
    exact_mod_cast h.symm
  have hηδφ : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ηc l δφ = 0 := by
    intro l hl1 hl2
    have h := hcoefE l δφ
    rw [characterPairing_rotation_scalar hn e _
      (fun x : Subgroup.zpowers ρ => (basis.representation δ).character x) _ (ε : ℂ)
      (fun v hv0 hv1 => by
        show (basis.representation δφ).character ((e (r n) : H) ^ v) =
          (ε : ℂ) * (basis.representation δ).character ((e (r n) : H) ^ v)
        rw [hδφ, hφrot v hv0 hv1, mul_comm]) (hh1 l) (hht l),
      characterPairing_sign_character_even_difference hn e _ hδdeg hδr hl1 hl2, mul_zero] at h
    exact_mod_cast h.symm
  have hex : ∀ l : ℕ, ∃ x : basis.index, 1 ≤ l → l ≤ M / 4 - 1 →
      x ∈ B ∧ x ≠ principal ∧ x ≠ φ ∧ (ηc l x = 1 ∨ ηc l x = -1) ∧
        ∀ y ∈ B, y ≠ principal → y ≠ φ → y ≠ x → ηc l y = 0 := by
    intro l
    by_cases hl : 1 ≤ l ∧ l ≤ M / 4 - 1
    · obtain ⟨hl1, hl2⟩ := hl
      have hnorm : ∑ c ∈ B, ηc l c * ηc l c = 3 := by
        have h := hηη l l hl1 hl2 hl1 hl2
        rw [ite_eq_left rfl] at h
        exact h.trans (by norm_num)
      have hφB' : φ ∈ B.erase principal := Finset.mem_erase.mpr ⟨Ne.symm h1φ, hφB⟩
      have h1 := Finset.sum_erase_add B (fun c => ηc l c * ηc l c) hpB
      have h2 := Finset.sum_erase_add (B.erase principal) (fun c => ηc l c * ηc l c) hφB'
      have hp1 : ηc l principal = 1 := hηp l hl1 hl2
      rw [hp1, hnorm] at h1
      rw [hηφ l hl1 hl2, hε2] at h2
      have hT : ∑ c ∈ (B.erase principal).erase φ, ηc l c * ηc l c = ((1 : ℕ) : ℤ) := by
        push_cast
        linarith
      obtain ⟨N, hNT, hNcard, hNsign, hNout⟩ :=
        small_norm_support _ (ηc l) (n := 1) (by norm_num) hT
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hNcard
      have hxT := hNT (Finset.mem_singleton_self x)
      have hxφ := Finset.ne_of_mem_erase hxT
      have hxB' := Finset.mem_of_mem_erase hxT
      refine ⟨x, fun _ _ => ⟨Finset.mem_of_mem_erase hxB', Finset.ne_of_mem_erase hxB', hxφ,
        hNsign x (Finset.mem_singleton_self x), fun y hy hyp hyφ hyx => ?_⟩⟩
      exact hNout y (Finset.mem_erase.mpr ⟨hyφ, Finset.mem_erase.mpr ⟨hyp, hy⟩⟩)
        (by simp [hyx])
    · exact ⟨principal, fun h1 h2 => absurd ⟨h1, h2⟩ hl⟩
  choose η hη using hex
  have hform : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ∀ y ∈ B,
      ηc l y = (if y = principal then 1 else 0) + ε * (if y = φ then 1 else 0) +
        ηc l (η l) * (if y = η l then 1 else 0) := by
    intro l hl1 hl2 y hy
    obtain ⟨-, hxp, hxφ, -, hxout⟩ := hη l hl1 hl2
    by_cases hyp : y = principal
    · rw [hyp, ite_eq_left rfl, ite_eq_right h1φ, ite_eq_right (Ne.symm hxp),
        show ηc l principal = 1 from hηp l hl1 hl2]
      ring
    by_cases hyφ : y = φ
    · rw [hyφ, ite_eq_right (Ne.symm h1φ), ite_eq_left rfl, ite_eq_right (Ne.symm hxφ),
        hηφ l hl1 hl2]
      ring
    by_cases hyx : y = η l
    · rw [hyx, ite_eq_right hxp, ite_eq_right hxφ, ite_eq_left rfl]
      ring
    · rw [ite_eq_right hyp, ite_eq_right hyφ, ite_eq_right hyx, hxout y hy hyp hyφ hyx]
      ring
  let deg : basis.index → ℤ := fun c => (Module.finrank ℂ (basis.representation c).vector : ℤ)
  have hdegpos : ∀ c, 0 < deg c := fun c => by
    show (0 : ℤ) < (Module.finrank ℂ (basis.representation c).vector : ℤ)
    exact_mod_cast (basis_character_one basis c).2
  have hdegval : ∀ c, χ c 1 = (deg c : ℂ) := fun c => by
    show (basis.representation c).character 1 =
      (((Module.finrank ℂ (basis.representation c).vector : ℤ)) : ℂ)
    rw [(basis_character_one basis c).1]
    push_cast
    rfl
  have hdegp : deg principal = 1 := by
    have h := hdegval principal
    rw [show χ principal = 1 from hprincipal, Pi.one_apply] at h
    exact_mod_cast h.symm
  have hdegφ : deg φ = q := by
    have h := hdegval φ
    rw [show χ φ 1 = q from hφdeg] at h
    exact_mod_cast h.symm
  have hτ : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ηc l (η l) = -ε ∧ deg (η l) = q + ε := by
    intro l hl1 hl2
    obtain ⟨hxB, hxp, hxφ, hxsign, -⟩ := hη l hl1 hl2
    have h := (hE1 l hl1 hl2).symm.trans (hEapply l 1)
    have h' := h.trans (basis_combination_one basis B (ηc l))
    have hsum : ∑ c ∈ B, ηc l c * deg c = 0 := by exact_mod_cast h'.symm
    have hsum' : ∑ c ∈ B, ηc l c * deg c = ∑ c ∈ B, deg c * (1 * (if c = principal then 1 else 0) +
        ε * (if c = φ then 1 else 0) + ηc l (η l) * (if c = η l then 1 else 0)) :=
      Finset.sum_congr rfl fun c hc => by rw [hform l hl1 hl2 c hc]; ring
    rw [hsum', sum_mul_three_labels B deg hpB hφB hxB, hdegp, hdegφ] at hsum
    have hd := hdegpos (η l)
    rcases hε with rfl | rfl <;> rcases hxsign with h | h <;> rw [h] at hsum ⊢ <;>
      constructor <;> omega
  have hEdec : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 →
      E l = 1 + (ε : ℂ) • χ φ - (ε : ℂ) • χ (η l) := by
    intro l hl1 hl2
    obtain ⟨hxB, -, -, -, -⟩ := hη l hl1 hl2
    funext g
    have hsum : ∑ c ∈ B, (ηc l c : ℂ) * χ c g = ∑ c ∈ B,
        ((((if c = principal then 1 else 0) + ε * (if c = φ then 1 else 0) +
          (-ε) * (if c = η l then 1 else 0) : ℤ)) : ℂ) * (basis.representation c).character g :=
      Finset.sum_congr rfl fun c hc => by rw [hform l hl1 hl2 c hc, (hτ l hl1 hl2).1]
    have h := (hEapply l g).trans hsum
    rw [basis_combination_three basis hpB hφB hxB, hprincipal] at h
    refine h.trans ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply,
      Int.cast_neg]
    ring
  have hinj : ∀ j l : ℕ, 1 ≤ j → j ≤ M / 4 - 1 → 1 ≤ l → l ≤ M / 4 - 1 → η j = η l → j = l := by
    intro j l hj1 hj2 hl1 hl2 hjl
    by_contra hne
    have h := hηη j l hj1 hj2 hl1 hl2
    rw [ite_eq_right hne] at h
    have h3 := hηη l l hl1 hl2 hl1 hl2
    rw [ite_eq_left rfl] at h3
    have hsame : ∑ c ∈ B, ηc j c * ηc l c = ∑ c ∈ B, ηc l c * ηc l c :=
      Finset.sum_congr rfl fun c hc => by
        rw [hform j hj1 hj2 c hc, hform l hl1 hl2 c hc, (hτ j hj1 hj2).1, (hτ l hl1 hl2).1, hjl]
    have h' : ∑ c ∈ B, ηc j c * ηc l c = 2 := h.trans (by norm_num)
    have h3' : ∑ c ∈ B, ηc l c * ηc l c = 3 := h3.trans (by norm_num)
    omega
  have hvals := (cyclic_principal_Fourier_projection_values hn e basis ideal principal
    hprincipal).2.2
  have hEt : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → E l t = 0 := fun l hl1 hl2 =>
    (hvals t t 1 (mul_one t) (Commute.one_right t) (suppliedRotation_half_orderOf hn e)
      (by rw [orderOf_one]; exact odd_one)).2.1 l hl1 hl2
  have hEσ : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → E l σ = 0 := fun l hl1 hl2 =>
    (hvals σ σ 1 (mul_one σ) (Commute.one_right σ) (suppliedReflection_orderOf (by omega) e)
      (by rw [orderOf_one]; exact odd_one)).2.1 l hl1 hl2
  refine ⟨η, hinj, fun l hl1 hl2 => ?_⟩
  obtain ⟨hxB, hxp, hxφ, -, -⟩ := hη l hl1 hl2
  obtain ⟨hτl, hdl⟩ := hτ l hl1 hl2
  have hneδ : η l ≠ δ := fun h => by
    have h1 := hηδ l hl1 hl2
    rw [← h, hτl] at h1
    rcases hε with rfl | rfl <;> norm_num at h1
  have hneδφ : η l ≠ δφ := fun h => by
    have h1 := hηδφ l hl1 hl2
    rw [← h, hτl] at h1
    rcases hε with rfl | rfl <;> norm_num at h1
  have hdec := hEdec l hl1 hl2
  have ht0 := hEt l hl1 hl2
  have hs0 := hEσ l hl1 hl2
  rw [hdec] at ht0 hs0
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at ht0 hs0
  rw [show χ φ t = q from hφt] at ht0
  rw [show χ φ σ = -ε from hφs] at hs0
  refine ⟨hxB, hxp, hneδ, hxφ, hneδφ, hdec, ?_, ?_, ?_⟩
  · rw [hdegval, hdl]
    push_cast
    ring
  · rcases hε with rfl | rfl
    · push_cast at ht0 ⊢
      linear_combination -ht0
    · push_cast at ht0 ⊢
      linear_combination ht0
  · rcases hε with rfl | rfl
    · push_cast at hs0 ⊢
      linear_combination -hs0
    · push_cast at hs0 ⊢
      linear_combination hs0

end CFSG.Semidihedral.Principal

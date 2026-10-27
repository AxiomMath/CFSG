module

public import CFSG.CharacterTheory.Semidihedral.FixedFieldData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

open CFSG.Semidihedral.FixedFieldData

theorem exists_pow_eq_of_pow_div_eq_one {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    {m : ℕ} (hm : m ∣ Nat.card G) {x : G} (hx : x ^ (Nat.card G / m) = 1) :
    ∃ y : G, y ^ m = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, g ^ i = x := by
    have h1 : x ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.2 (hg x)
    exact (Submonoid.mem_powers_iff x g).1 h1
  obtain ⟨c, hc⟩ := hm
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · have : 0 < Nat.card G := Nat.card_pos
      omega
    · exact h
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · have : 0 < Nat.card G := Nat.card_pos
      omega
    · exact h
  have hdiv : Nat.card G / m = c := by rw [hc]; exact Nat.mul_div_cancel_left c hmpos
  rw [hdiv, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hord, hc] at hx
  obtain ⟨j, rfl⟩ : m ∣ i := Nat.dvd_of_mul_dvd_mul_right hcpos hx
  exact ⟨g ^ j, by rw [← pow_mul, mul_comm]⟩

theorem exists_pow_eq_of_pow_three_eq_one {Γ : Type*} [Group Γ] [Finite Γ] [IsCyclic Γ]
    {σ δ : Γ} (hσ : orderOf σ = 3) (hδ : δ ^ 3 = 1) : ∃ j : ℕ, j < 3 ∧ δ = σ ^ j := by
  classical
  have := Fintype.ofFinite Γ
  set S := Finset.univ.filter (fun x : Γ => x ^ 3 = 1) with hS
  have hle : S.card ≤ 3 := IsCyclic.card_pow_eq_one_le (by norm_num)
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  set T : Finset Γ := {1, σ, σ ^ 2} with hT
  have hσ1 : σ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hσ; norm_num at hσ
  have hσ2 : σ ^ 2 ≠ 1 := fun h1 => by
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hσ] at this
    norm_num at this
  have hσσ : σ ≠ σ ^ 2 := fun h1 => by
    apply hσ1
    have h2 : σ * σ = σ * 1 := by rw [← sq, ← h1, mul_one]
    exact mul_left_cancel h2
  have hTc : T.card = 3 := by
    rw [hT, Finset.card_insert_of_notMem, Finset.card_pair hσσ]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hσ1, Ne.symm hσ2⟩
  have hTS : T ⊆ S := by
    intro x hx
    simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 3
    · exact hσ3
    · rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hσ3, one_pow]
  have hST : S = T := (Finset.eq_of_subset_of_card_le hTS (by rw [hTc]; exact hle)).symm
  have hδS : δ ∈ S := by simp [hS, hδ]
  rw [hST] at hδS
  simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hδS
  rcases hδS with rfl | rfl | rfl
  · exact ⟨0, by norm_num, by rw [pow_zero]⟩
  · exact ⟨1, by norm_num, by rw [pow_one]⟩
  · exact ⟨2, by norm_num, rfl⟩

theorem ringAut_pow_apply {K : Type*} [Field K] {p : ℕ} {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ p)
    (n : ℕ) (c : K) : (φ ^ n) c = c ^ (p ^ n) := by
  induction n with
  | zero => rw [pow_zero, RingAut.one_apply, pow_zero, pow_one]
  | succ n ih => rw [pow_succ', RingAut.mul_apply, ih, hφ, ← pow_mul, ← pow_succ]

theorem exists_frobenius_rep {k : Type} [Field k] [Finite k] {τ : k ≃+* k}
    (hτ : orderOf τ = 3) :
    ∃ r i : ℕ, r ^ 3 = Nat.card k ∧ (i = 1 ∨ i = 2) ∧ ∀ x : k, (τ ^ i) x = x ^ r := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists k
  have hpp : p.Prime := CharP.char_is_prime k p
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k p
  have hcard : Nat.card k = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨fr, hfr, hord, -, hautcard, hcyc, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality p n hpp n.pos k hcard
  have h3 : 3 ∣ (n : ℕ) := by
    have h := orderOf_dvd_natCard τ
    rwa [hτ, hautcard] at h
  obtain ⟨m, hm⟩ := h3
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := n.pos
    omega
  have : Finite (k ≃+* k) := Nat.finite_of_card_ne_zero (by rw [hautcard]; exact n.pos.ne')
  have hgord : orderOf (fr ^ m) = 3 := by
    rw [orderOf_pow' _ hm0, hord, hm, Nat.gcd_eq_right (dvd_mul_left m 3)]
    exact Nat.mul_div_cancel 3 (Nat.pos_of_ne_zero hm0)
  have hτ3 : τ ^ 3 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  obtain ⟨j, hj, hτj⟩ := exists_pow_eq_of_pow_three_eq_one hgord hτ3
  have hg3 : (fr ^ m) ^ 3 = 1 := by rw [← hgord]; exact pow_orderOf_eq_one _
  have hgx : ∀ x : k, (fr ^ m) x = x ^ (p ^ m) := ringAut_pow_apply hfr m
  have hrr : (p ^ m) ^ 3 = Nat.card k := by rw [← pow_mul, hcard, hm, mul_comm]
  interval_cases j
  · exfalso
    rw [pow_zero] at hτj
    rw [hτj, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  · exact ⟨p ^ m, 1, hrr, Or.inl rfl, fun x => by simp only [hτj, pow_one]; exact hgx x⟩
  · refine ⟨p ^ m, 2, hrr, Or.inr rfl, fun x => ?_⟩
    have h : τ ^ 2 = fr ^ m := by
      rw [hτj, ← pow_mul]
      calc (fr ^ m) ^ (2 * 2) = (fr ^ m) ^ 3 * (fr ^ m) := by rw [← pow_succ]
        _ = fr ^ m := by rw [hg3, one_mul]
    rw [h, hgx]

theorem isCyclic_ringEquiv (k : Type) [Field k] [Finite k] :
    IsCyclic (k ≃+* k) ∧ Finite (k ≃+* k) := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists k
  have hpp : p.Prime := CharP.char_is_prime k p
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k p
  have hcard : Nat.card k = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨-, -, -, -, hautcard, hcyc, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality p n hpp n.pos k hcard
  exact ⟨hcyc, Nat.finite_of_card_ne_zero (by rw [hautcard]; exact n.pos.ne')⟩

structure FrobData (k : Type) [Field k] [Finite k] where
  r : ℕ
  τ : k ≃+* k
  apply_eq : ∀ x, τ x = x ^ r
  card_eq : r ^ 3 = Nat.card k
  two_le : 2 ≤ r

namespace FrobData

variable {k : Type} [Field k] [Finite k] (F : FrobData k)

theorem exists_of_orderOf_eq_three {τ : k ≃+* k} (hτ : orderOf τ = 3) :
    ∃ (F : FrobData k) (i : ℕ), (i = 1 ∨ i = 2) ∧ F.τ = τ ^ i := by
  obtain ⟨r, i, hr, hi, hx⟩ := exists_frobenius_rep hτ
  have hk : 2 ≤ Nat.card k := Finite.one_lt_card
  have hr2 : 2 ≤ r := by
    by_contra h
    have : r ≤ 1 := by omega
    have : r ^ 3 ≤ 1 := by
      calc r ^ 3 ≤ 1 ^ 3 := Nat.pow_le_pow_left this 3
        _ = 1 := one_pow 3
    omega
  exact ⟨⟨r, τ ^ i, hx, hr, hr2⟩, i, hi, rfl⟩

theorem mod_three (h3 : 3 ∣ Nat.card k - 1) : F.r % 3 = 1 := by
  have hk : 0 < Nat.card k := Nat.card_pos
  have h1 : F.r ^ 3 % 3 = 1 := by
    rw [F.card_eq]
    omega
  have h2 : F.r ^ 3 % 3 = F.r % 3 := by
    have := Nat.pow_mod F.r 3 3
    rcases (by omega : F.r % 3 = 0 ∨ F.r % 3 = 1 ∨ F.r % 3 = 2) with h | h | h <;>
      simp [this, h]
  omega

theorem card_units_eq : Nat.card kˣ = (F.r - 1) * (1 + F.r + F.r ^ 2) := by
  have key : ∀ r : ℕ, 1 ≤ r → r ^ 3 - 1 = (r - 1) * (1 + r + r ^ 2) := by
    intro r hr
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    apply Nat.sub_eq_of_eq_add
    simp only [Nat.add_sub_cancel]
    ring
  rw [Nat.card_units, ← F.card_eq]
  exact key F.r (by have := F.two_le; omega)

theorem three_dvd_norm (h3 : 3 ∣ Nat.card k - 1) : 3 ∣ 1 + F.r + F.r ^ 2 := by
  have h := F.mod_three h3
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, Nat.add_mod 1, Nat.pow_mod, h]

theorem exists_unit_apply_eq (l : kˣ) (hl : (l : k) * F.τ l * F.τ (F.τ l) = 1) :
    ∃ m : kˣ, F.τ (m : k) = (m : k) * ((l : k))⁻¹ := by
  have h2 := F.two_le
  have hl' : l ^ (1 + F.r + F.r ^ 2) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hl, F.apply_eq, F.apply_eq, ← pow_mul]
    ring
  have hdvd : F.r - 1 ∣ Nat.card kˣ := ⟨1 + F.r + F.r ^ 2, F.card_units_eq⟩
  have hdiv : Nat.card kˣ / (F.r - 1) = 1 + F.r + F.r ^ 2 := by
    rw [F.card_units_eq]
    exact Nat.mul_div_cancel_left _ (by omega)
  obtain ⟨m, hm⟩ := exists_pow_eq_of_pow_div_eq_one (G := kˣ) hdvd (x := l⁻¹)
    (by rw [hdiv, inv_pow, hl', inv_one])
  refine ⟨m, ?_⟩
  have hm' : (m : k) ^ (F.r - 1) = ((l : k))⁻¹ := by
    have := congrArg Units.val hm
    rwa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] at this
  have hpow : (m : k) ^ F.r = (m : k) ^ (F.r - 1) * (m : k) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [F.apply_eq, hpow, hm', mul_comm]

theorem exists_unit_cube_of_apply_eq (h3 : 3 ∣ Nat.card k - 1) {x : kˣ} (hx : F.τ (x : k) = x) :
    ∃ c : kˣ, c ^ 3 = x := by
  have h2 := F.two_le
  have hxr : x ^ (F.r - 1) = 1 := by
    apply Units.ext
    have h1 : (x : k) ^ F.r = x := by rw [← F.apply_eq]; exact hx
    have hx0 : (x : k) ≠ 0 := x.ne_zero
    have hpow : (x : k) ^ F.r = (x : k) ^ (F.r - 1) * (x : k) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow] at h1
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact mul_right_cancel₀ hx0 (by rw [h1, one_mul])
  obtain ⟨t, ht⟩ := F.three_dvd_norm h3
  have hdvd : 3 ∣ Nat.card kˣ := by
    rw [F.card_units_eq, ht]
    exact ⟨(F.r - 1) * t, by ring⟩
  have hdiv : Nat.card kˣ / 3 = (F.r - 1) * t := by
    rw [F.card_units_eq, ht, show (F.r - 1) * (3 * t) = 3 * ((F.r - 1) * t) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  exact exists_pow_eq_of_pow_div_eq_one hdvd (by rw [hdiv, pow_mul, hxr, one_pow])

theorem exists_omega (h3 : 3 ∣ Nat.card k - 1) :
    ∃ ω : kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ F.τ (ω : k) = ω := by
  have hmod := F.mod_three h3
  obtain ⟨ω, hω⟩ : ∃ ω : kˣ, orderOf ω = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply exists_prime_orderOf_dvd_card' 3
    rw [Nat.card_units]
    exact h3
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  refine ⟨ω, hω3, ?_, ?_⟩
  · intro h
    rw [h, orderOf_one] at hω
    omega
  · rw [F.apply_eq]
    have hr : F.r = 3 * (F.r / 3) + 1 := by omega
    rw [hr, pow_succ, pow_mul]
    have : (ω : k) ^ 3 = 1 := by
      have := congrArg Units.val hω3
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [this, one_pow, one_mul]

end FrobData

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

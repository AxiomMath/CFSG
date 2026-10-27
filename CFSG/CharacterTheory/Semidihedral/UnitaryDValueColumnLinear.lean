module

public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteCharacters

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.UnitaryDValue.Columns

open CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def omega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem omega_sq_add_omega_add_one : omega ^ 2 + omega + 1 = 0 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext
  · simp only [omega, pow_two, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re]
    linarith
  · simp only [omega, pow_two, Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_im]
    ring

theorem omega_pow_three : omega ^ 3 = 1 := by
  have h := omega_sq_add_omega_add_one
  linear_combination (omega - 1) * h

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp only [omega, Complex.one_re] at this
  norm_num at this

theorem omega_ne_zero : omega ≠ 0 := by
  intro h
  have := omega_pow_three
  rw [h] at this
  norm_num at this

theorem omega_sq_ne_one : omega ^ 2 ≠ 1 := by
  intro h
  apply omega_ne_one
  have h3 := omega_pow_three
  rw [pow_succ, h, one_mul] at h3
  exact h3

theorem omega_sq_ne_omega : omega ^ 2 ≠ omega := by
  intro h
  apply omega_ne_one
  have h0 := omega_ne_zero
  rw [pow_two] at h
  exact mul_left_cancel₀ h0 (h.trans (mul_one omega).symm)

theorem omega_inv : omega⁻¹ = omega ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', omega_pow_three])

theorem eq_of_pow_three_eq_one {z : ℂ} (hz : z ^ 3 = 1) : z = 1 ∨ z = omega ∨ z = omega ^ 2 := by
  have h := omega_sq_add_omega_add_one
  have h3 := omega_pow_three
  have hprod : (z - 1) * (z - omega) * (z - omega ^ 2) = 0 := by
    linear_combination hz - z ^ 2 * h + z * omega * h - h3
  rcases mul_eq_zero.mp hprod with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl (sub_eq_zero.mp h2)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h1))

theorem exists_linear_character {G : Type*} [Group G] [Finite G] {Q P : Subgroup G}
    (hPQ : P ≤ Q) {k : ℕ} (hQ : Nat.card Q = 3 ^ (k + 1)) (hP : Nat.card P = 3 ^ k) {t₀ : G}
    (ht₀Q : t₀ ∈ Q) (ht₀P : t₀ ∉ P) :
    ∃ μ : Q →* ℂˣ,
      (∀ u : Q, ((μ u : ℂˣ) : ℂ) = 1 ↔ (u : G) ∈ P) ∧
      (∀ u : Q, ((μ u : ℂˣ) : ℂ) = omega ↔ (u : G) * t₀⁻¹ ∈ P) ∧
      (∀ u : Q, ((μ u : ℂˣ) : ℂ) = omega ^ 2 ↔ (u : G) * t₀ ∈ P) ∧
      ∀ u : Q, ((μ u : ℂˣ) : ℂ) = 1 ∨ ((μ u : ℂˣ) : ℂ) = omega ∨
        ((μ u : ℂˣ) : ℂ) = omega ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P' : Subgroup Q := P.subgroupOf Q with hP'
  have hcardP' : Nat.card P' = 3 ^ k := by
    rw [← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPQ).toEquiv
  have hindex : P'.index = 3 := by
    have h := P'.card_mul_index
    rw [hcardP', hQ, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) k) h
  have hnormal : P'.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hindex, hQ, Nat.Prime.pow_minFac Nat.prime_three (Nat.succ_ne_zero k)])
  have hcardquot : Nat.card (Q ⧸ P') = 3 := by rw [← Subgroup.index_eq_card, hindex]
  set t : Q := ⟨t₀, ht₀Q⟩ with ht
  set g : Q ⧸ P' := (t : Q ⧸ P') with hg
  have hg1 : g ≠ 1 := by
    rw [hg, Ne, QuotientGroup.eq_one_iff, hP', Subgroup.mem_subgroupOf]
    exact ht₀P
  have hgen : ∀ x : Q ⧸ P', x ∈ Subgroup.zpowers g := fun x =>
    mem_zpowers_of_prime_card hcardquot hg1
  have hgord : orderOf g = 3 := by rw [orderOf_eq_card_of_forall_mem_zpowers hgen, hcardquot]
  set ωu : ℂˣ := Units.mk0 omega omega_ne_zero with hωu
  have hωord : orderOf ωu = 3 := by
    rw [orderOf_eq_prime_iff]
    refine ⟨?_, ?_⟩
    · ext
      simp [ωu, omega_pow_three]
    · intro h
      apply omega_ne_one
      have := congrArg Units.val h
      simpa [ωu] using this
  let μ₀ : Q ⧸ P' →* ℂˣ := monoidHomOfForallMemZpowers hgen (g' := ωu) (by rw [hωord, hgord])
  have hμ₀g : μ₀ g = ωu := monoidHomOfForallMemZpowers_apply_gen hgen _
  have hμ₀inj : ∀ x, μ₀ x = 1 → x = 1 := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen x)
    rw [map_zpow, hμ₀g] at hx
    have h3 : ((orderOf ωu : ℕ) : ℤ) ∣ n := orderOf_dvd_iff_zpow_eq_one.mpr hx
    rw [hωord, ← hgord] at h3
    exact orderOf_dvd_iff_zpow_eq_one.mp h3
  let μ : Q →* ℂˣ := μ₀.comp (QuotientGroup.mk' P')
  have hμt : μ t = ωu := hμ₀g
  have hμ1 : ∀ u : Q, ((μ u : ℂˣ) : ℂ) = 1 ↔ (u : G) ∈ P := by
    intro u
    rw [Units.val_eq_one]
    constructor
    · intro h
      have h' := hμ₀inj _ h
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hP', Subgroup.mem_subgroupOf] at h'
      exact h'
    · intro h
      have h' : (u : Q ⧸ P') = 1 := by
        rw [QuotientGroup.eq_one_iff, hP', Subgroup.mem_subgroupOf]
        exact h
      change μ₀ (u : Q ⧸ P') = 1
      rw [h', map_one]
  have hμtval : ((μ t : ℂˣ) : ℂ) = omega := by rw [hμt, hωu, Units.val_mk0]
  refine ⟨μ, hμ1, ?_, ?_, ?_⟩
  · intro u
    have key := hμ1 (u * t⁻¹)
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hμtval] at key
    rw [← mul_inv_eq_one₀ omega_ne_zero, key]
    rfl
  · intro u
    have key := hμ1 (u * t)
    rw [map_mul, Units.val_mul, hμtval] at key
    rw [← omega_inv, ← mul_eq_one_iff_eq_inv₀ omega_ne_zero, key]
    rfl
  · intro u
    apply eq_of_pow_three_eq_one
    have hu3 : (u : Q ⧸ P') ^ 3 = 1 := by
      rw [← hcardquot]
      exact pow_card_eq_one'
    have : μ u ^ 3 = 1 := by
      change μ₀ (u : Q ⧸ P') ^ 3 = 1
      rw [← map_pow, hu3, map_one]
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

@[expose] noncomputable def column {G : Type*} [Group G] [Fintype G] (Q : Subgroup G)
    (μ : Q →* ℂˣ) (χ : G → ℂ) : ℂ :=
  (Nat.card Q : ℂ)⁻¹ * ∑ u : Q, χ u * (1 - ((μ u : ℂˣ) : ℂ))

@[expose] noncomputable def twist {Q V : Type*} [Group Q] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (μ : Q →* ℂˣ) : Representation ℂ Q V where
  toFun u := ((μ u : ℂˣ) : ℂ) • ρ u
  map_one' := by simp
  map_mul' u w := by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

theorem twist_character {Q V : Type*} [Group Q] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (μ : Q →* ℂˣ) (u : Q) :
    (twist ρ μ).character u = ((μ u : ℂˣ) : ℂ) * ρ.character u := by
  change LinearMap.trace ℂ V (((μ u : ℂˣ) : ℂ) • ρ u) = _
  rw [map_smul, smul_eq_mul]
  rfl

theorem exists_int_column {G : Type*} [Group G] [Fintype G] (Q : Subgroup G) (μ : Q →* ℂˣ)
    (ρ : FiniteComplexRepresentation G) : ∃ n : ℤ, column Q μ ρ.character = n := by
  let ρQ : Representation ℂ Q ρ.vector := ρ.representation.comp Q.subtype
  have : Invertible (Nat.card Q : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h1 := Representation.card_inv_mul_sum_char_eq_finrank ρQ
  have h2 := Representation.card_inv_mul_sum_char_eq_finrank (twist ρQ μ)
  refine ⟨(Module.finrank ℂ ρQ.invariants : ℤ) - Module.finrank ℂ (twist ρQ μ).invariants, ?_⟩
  push_cast
  rw [← h1, ← h2, column, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [twist_character]
  change ρ.character u * _ = ρ.character u - _ * ρ.character u
  ring

theorem card_filter_eq_ncard {G : Type*} [Group G] [Fintype G] (Q : Subgroup G) (S : G → Prop)
    (hS : ∀ x, S x → x ∈ Q) [DecidablePred fun u : Q => S u] :
    (Finset.univ.filter fun u : Q => S u).card = {x : G | S x}.ncard := by
  rw [← Set.ncard_coe_finset]
  have heq : {x : G | S x} =
      Subtype.val '' (↑(Finset.univ.filter fun u : Q => S u) : Set Q) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
      Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun hx => ⟨hS x hx, hx⟩, fun ⟨_, hx⟩ => hx⟩
  rw [heq, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem class_weight_sum {G : Type*} [Group G] [Fintype G] {Q P : Subgroup G} (hPQ : P ≤ Q)
    {t₀ : G} (ht₀Q : t₀ ∈ Q) (μ : Q →* ℂˣ)
    (hμω : ∀ u : Q, ((μ u : ℂˣ) : ℂ) = omega ↔ (u : G) * t₀⁻¹ ∈ P)
    (hμω2 : ∀ u : Q, ((μ u : ℂˣ) : ℂ) = omega ^ 2 ↔ (u : G) * t₀ ∈ P)
    (hμcases : ∀ u : Q, ((μ u : ℂˣ) : ℂ) = 1 ∨ ((μ u : ℂˣ) : ℂ) = omega ∨
      ((μ u : ℂˣ) : ℂ) = omega ^ 2)
    (v : G) (hcount : {u : G | IsConj v u ∧ u * t₀⁻¹ ∈ P}.ncard = 9 ∧
      {u : G | IsConj v u ∧ u * t₀ ∈ P}.ncard = 9) :
    ∑ u : Q, (if IsConj v (u : G) then 1 - ((μ u⁻¹ : ℂˣ) : ℂ) else 0) = 27 := by
  have hterm : ∀ u : Q, (if IsConj v (u : G) then 1 - ((μ u⁻¹ : ℂˣ) : ℂ) else 0) =
      (if IsConj v (u : G) ∧ (u : G) * t₀⁻¹ ∈ P then 1 - omega ^ 2 else 0) +
        (if IsConj v (u : G) ∧ (u : G) * t₀ ∈ P then 1 - omega else 0) := by
    intro u
    rw [map_inv, Units.val_inv_eq_inv_val]
    rcases hμcases u with h | h | h
    · have h1 : ¬ (u : G) * t₀⁻¹ ∈ P := fun hm =>
        omega_ne_one (((hμω u).mpr hm).symm.trans h)
      have h2 : ¬ (u : G) * t₀ ∈ P := fun hm =>
        omega_sq_ne_one (((hμω2 u).mpr hm).symm.trans h)
      simp [h, h1, h2]
    · have h1 : (u : G) * t₀⁻¹ ∈ P := (hμω u).mp h
      have h2 : ¬ (u : G) * t₀ ∈ P := fun hm =>
        omega_sq_ne_omega (((hμω2 u).mpr hm).symm.trans h)
      simp only [h, h1, h2, and_true, and_false, ite_false, add_zero, omega_inv]
    · have h1 : ¬ (u : G) * t₀⁻¹ ∈ P := fun hm =>
        omega_sq_ne_omega (h.symm.trans ((hμω u).mpr hm))
      have h2 : (u : G) * t₀ ∈ P := (hμω2 u).mp h
      have hinv : (omega ^ 2)⁻¹ = omega := by
        rw [inv_eq_iff_eq_inv, omega_inv]
      simp only [h, h1, h2, and_true, and_false, ite_false, zero_add, hinv]
  rw [Finset.sum_congr rfl fun u _ => hterm u, Finset.sum_add_distrib, Finset.sum_ite,
    Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const_zero, add_zero, add_zero,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  rw [@card_filter_eq_ncard _ _ _ Q (fun x => IsConj v x ∧ x * t₀⁻¹ ∈ P) (fun x hx => by
    have : x = x * t₀⁻¹ * t₀ := by group
    rw [this]
    exact Q.mul_mem (hPQ hx.2) ht₀Q) _]
  rw [@card_filter_eq_ncard _ _ _ Q (fun x => IsConj v x ∧ x * t₀ ∈ P) (fun x hx => by
    have : x = x * t₀ * t₀⁻¹ := by group
    rw [this]
    exact Q.mul_mem (hPQ hx.2) (Q.inv_mem ht₀Q)) _]
  rw [hcount.1, hcount.2]
  have h := omega_sq_add_omega_add_one
  push_cast
  linear_combination (-9 : ℂ) * h

end CFSG.Semidihedral.UnitaryDValue.Columns

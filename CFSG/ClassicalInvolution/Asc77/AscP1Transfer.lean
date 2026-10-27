module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.ClassicalInvolution.Asc77

open MulAction Subgroup

variable {G : Type*} [Group G] [Finite G] {H : Subgroup G} {A : Type*} [CommGroup A]
  (ϕ : ↥H →* A)

theorem transfer_apply_eq_one (a : G)
    (h : ∀ (g : G) (n : ℕ) (hg : g⁻¹ * a ^ n * g ∈ H), ϕ ⟨g⁻¹ * a ^ n * g, hg⟩ = 1) :
    MonoidHom.transfer ϕ a = 1 := by
  have := Fintype.ofFinite (Quotient (orbitRel (zpowers a) (G ⧸ H)))
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  exact Finset.prod_eq_one fun q _ => h _ _ _

theorem transfer_apply_eq_pow_index (a : G) (ha : a ∈ H)
    (h : ∀ (g : G) (n : ℕ) (hg : g⁻¹ * a ^ n * g ∈ H),
      ϕ ⟨g⁻¹ * a ^ n * g, hg⟩ = ϕ ⟨a, ha⟩ ^ n) :
    MonoidHom.transfer ϕ a = ϕ ⟨a, ha⟩ ^ H.index := by
  have := Fintype.ofFinite (Quotient (orbitRel (zpowers a) (G ⧸ H)))
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  calc ∏ q : Quotient (orbitRel (zpowers a) (G ⧸ H)),
        ϕ ⟨(Quotient.out q.out)⁻¹ * a ^ Function.minimalPeriod (fun x => a • x) q.out *
          Quotient.out q.out, QuotientGroup.out_conj_pow_minimalPeriod_mem H a q.out⟩
      = ∏ q : Quotient (orbitRel (zpowers a) (G ⧸ H)),
          ϕ ⟨a, ha⟩ ^ Function.minimalPeriod (fun x => a • x) q.out :=
        Finset.prod_congr rfl fun q _ => h _ _ _
    _ = ϕ ⟨a, ha⟩ ^ ∑ q : Quotient (orbitRel (zpowers a) (G ⧸ H)),
          Function.minimalPeriod (fun x => a • x) q.out := Finset.prod_pow_eq_pow_sum _ _ _
    _ = ϕ ⟨a, ha⟩ ^ H.index := by rw [Subgroup.index_eq_sum_minimalPeriod H a]

theorem transfer_apply_ne_one (a : G) (ha : a ∈ H) (ha2 : IsPGroup 2 (zpowers a))
    (hϕ : ϕ ⟨a, ha⟩ ≠ 1) (hodd : Odd H.index)
    (h : ∀ (g : G) (n : ℕ) (hg : g⁻¹ * a ^ n * g ∈ H),
      ϕ ⟨g⁻¹ * a ^ n * g, hg⟩ = ϕ ⟨a, ha⟩ ^ n) :
    MonoidHom.transfer ϕ a ≠ 1 := by
  rw [transfer_apply_eq_pow_index ϕ a ha h]
  intro hpow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := ha2.exists_card_eq
  rw [Nat.card_zpowers] at hm
  have h1 : ϕ ⟨a, ha⟩ ^ 2 ^ m = 1 := by
    have : (⟨a, ha⟩ : ↥H) ^ 2 ^ m = 1 := by
      apply Subtype.ext
      rw [← hm]
      exact pow_orderOf_eq_one a
    rw [← map_pow, this, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hϕ (orderOf_eq_one_iff.mp (by simpa using hj))
  have hdvd : 2 ∣ H.index := by
    have h2 : orderOf (ϕ ⟨a, ha⟩) ∣ H.index := orderOf_dvd_of_pow_eq_one hpow
    rw [hj] at h2
    exact (dvd_pow_self 2 hj0).trans h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem transfer_apply_eq_one_of_pow_four (a : G) (ha4 : a ^ 4 = 1)
    (h1 : ∀ (g : G) (hg : g⁻¹ * a * g ∈ H), ϕ ⟨g⁻¹ * a * g, hg⟩ = 1)
    (h2 : ∀ (g : G) (hg : g⁻¹ * a ^ 2 * g ∈ H), ϕ ⟨g⁻¹ * a ^ 2 * g, hg⟩ = 1) :
    MonoidHom.transfer ϕ a = 1 ∧ MonoidHom.transfer ϕ (a ^ 2) = 1 := by
  have hV : MonoidHom.transfer ϕ a = 1 := by
    refine transfer_apply_eq_one ϕ a fun g n hg => ?_
    have hn : a ^ n = a ^ (n % 4) := by
      conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, ha4, one_pow, one_mul]
    have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hcases with h0 | h0 | h0 | h0
    · have : ⟨g⁻¹ * a ^ n * g, hg⟩ = (1 : ↥H) := by
        apply Subtype.ext
        simp [hn, h0]
      rw [this, map_one]
    · have e : g⁻¹ * a ^ n * g = g⁻¹ * a * g := by rw [hn, h0, pow_one]
      have hg' : g⁻¹ * a * g ∈ H := e ▸ hg
      have : (⟨g⁻¹ * a ^ n * g, hg⟩ : ↥H) = ⟨g⁻¹ * a * g, hg'⟩ := Subtype.ext e
      rw [this]
      exact h1 g hg'
    · have e : g⁻¹ * a ^ n * g = g⁻¹ * a ^ 2 * g := by rw [hn, h0]
      have hg' : g⁻¹ * a ^ 2 * g ∈ H := e ▸ hg
      have : (⟨g⁻¹ * a ^ n * g, hg⟩ : ↥H) = ⟨g⁻¹ * a ^ 2 * g, hg'⟩ := Subtype.ext e
      rw [this]
      exact h2 g hg'
    · have e : g⁻¹ * a ^ n * g = (g⁻¹ * a * g)⁻¹ := by
        have h3 : a ^ 3 = a⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← pow_succ]
          exact ha4
        rw [hn, h0, h3]
        group
      have hg' : g⁻¹ * a * g ∈ H := by
        have := H.inv_mem (e ▸ hg)
        simpa using this
      have : (⟨g⁻¹ * a ^ n * g, hg⟩ : ↥H) = (⟨g⁻¹ * a * g, hg'⟩ : ↥H)⁻¹ := Subtype.ext e
      rw [this, map_inv, h1 g hg', inv_one]
  exact ⟨hV, by rw [map_pow, hV, one_pow]⟩

omit [Finite G] in
theorem out_conj_mem_of_smul_eq {a : G} {q : G ⧸ H} (hq : a • q = q) :
    (Quotient.out q)⁻¹ * a * Quotient.out q ∈ H := by
  have h : (↑(a * Quotient.out q) : G ⧸ H) = ↑(Quotient.out q) := by
    change a • (↑(Quotient.out q) : G ⧸ H) = ↑(Quotient.out q)
    rw [QuotientGroup.out_eq']
    exact hq
  have := QuotientGroup.eq.mp h.symm
  simpa [mul_assoc] using this

omit [Finite G] in
theorem eq_of_orbitRel_of_fixed {a : G} {x y : G ⧸ H} (hx : a • x = x)
    (h : orbitRel (zpowers a) (G ⧸ H) y x) : y = x := by
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp h
  have hgx : (g : G) • x = x := by
    have : zpowers a ≤ stabilizer G x :=
      (Subgroup.zpowers_le).mpr (MulAction.mem_stabilizer_iff.mpr hx)
    exact MulAction.mem_stabilizer_iff.mp (this g.2)
  rw [← hg]
  exact hgx

omit [Finite G] in
theorem not_fixed_of_orbitRel {a : G} {x y : G ⧸ H} (hx : a • x ≠ x)
    (h : orbitRel (zpowers a) (G ⧸ H) y x) : a • y ≠ y := by
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp h
  intro hy
  apply hx
  have hcomm : a * (g : G) = (g : G) * a := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [← hk]
    exact ((Commute.refl a).zpow_right k).eq
  have h1 : a • ((g : G) • x) = (g : G) • x := by
    have : (g • x : G ⧸ H) = y := hg
    rw [show ((g : G) • x) = y from this]
    exact hy
  have h2 : (g : G) • (a • x) = (g : G) • x := by
    rw [← mul_smul, ← hcomm, mul_smul]
    exact h1
  exact smul_left_cancel (g : G) h2

open scoped Classical in
theorem transfer_apply_involution [Fintype (G ⧸ H)] (a : G) (ha : a * a = 1) :
    MonoidHom.transfer ϕ a =
      ∏ q : G ⧸ H, if hq : a • q = q then
        ϕ ⟨(Quotient.out q)⁻¹ * a * Quotient.out q, out_conj_mem_of_smul_eq hq⟩ else 1 := by
  have := Fintype.ofFinite (Quotient (orbitRel (zpowers a) (G ⧸ H)))
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  rw [← Finset.prod_fiberwise Finset.univ
    (fun x : G ⧸ H => (Quotient.mk'' x : Quotient (orbitRel (zpowers a) (G ⧸ H))))]
  refine Finset.prod_congr rfl fun O _ => ?_
  set x₀ : G ⧸ H := Quotient.out O with hx₀
  have hOx : (Quotient.mk'' x₀ : Quotient (orbitRel (zpowers a) (G ⧸ H))) = O :=
    Quotient.out_eq O
  by_cases hfix : a • x₀ = x₀
  · have hper : Function.minimalPeriod (fun x => a • x) x₀ = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hfix
    have hfiber : Finset.univ.filter (fun x : G ⧸ H =>
        (Quotient.mk'' x : Quotient (orbitRel (zpowers a) (G ⧸ H))) = O) = {x₀} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hi
        have : orbitRel (zpowers a) (G ⧸ H) i x₀ := by
          rw [← hOx] at hi
          exact Quotient.exact' hi
        exact eq_of_orbitRel_of_fixed hfix this
      · rintro rfl
        exact hOx
    rw [hfiber, Finset.prod_singleton, dite_eq_left hfix]
    congr 1
    apply Subtype.ext
    simp only [hper, pow_one]
  · have hper : Function.minimalPeriod (fun x => a • x) x₀ = 2 := by
      have hdvd : Function.minimalPeriod (fun x => a • x) x₀ ∣ 2 := by
        refine Function.IsPeriodicPt.minimalPeriod_dvd ?_
        show (fun x => a • x)^[2] x₀ = x₀
        simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
          smul_smul, ha, one_smul]
      have h1 : Function.minimalPeriod (fun x => a • x) x₀ ≠ 1 := fun h =>
        hfix (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h h1
      · exact h
    have hall : ∀ i ∈ Finset.univ.filter (fun x : G ⧸ H =>
        (Quotient.mk'' x : Quotient (orbitRel (zpowers a) (G ⧸ H))) = O),
        (if hq : a • i = i then
          ϕ ⟨(Quotient.out i)⁻¹ * a * Quotient.out i, out_conj_mem_of_smul_eq hq⟩ else 1) = 1 := by
      intro i hi
      have hi' : orbitRel (zpowers a) (G ⧸ H) i x₀ := by
        have := (Finset.mem_filter.mp hi).2
        rw [← hOx] at this
        exact Quotient.exact' this
      exact dite_eq_right (not_fixed_of_orbitRel hfix hi')
    rw [Finset.prod_eq_one hall]
    have : (⟨(Quotient.out x₀)⁻¹ * a ^ Function.minimalPeriod (fun x => a • x) x₀ *
        Quotient.out x₀, QuotientGroup.out_conj_pow_minimalPeriod_mem H a x₀⟩ : ↥H) = 1 := by
      apply Subtype.ext
      simp only [hper, pow_two, ha, mul_one, inv_mul_cancel, OneMemClass.coe_one]
    rw [this, map_one]

end CFSG.ClassicalInvolution.Asc77

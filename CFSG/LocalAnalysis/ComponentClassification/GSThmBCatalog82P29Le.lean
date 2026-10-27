module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Lb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabL

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open Polynomial CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
  CFSG.ComponentClassification.CatFactsL4U4

namespace L4M

variable {F : Type} [Field F]

local notation "𝔼" => extension (-1 : F)

local notation "𝕣" => AdjoinRoot.root (quadraticPolynomial (-1 : F))

theorem exists_coord (e : 𝔼) : ∃ a b : F, e = algebraMap F 𝔼 a + algebraMap F 𝔼 b * 𝕣 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective e
  have hf := quadraticPolynomial_monic (-1 : F)
  have hf1 : quadraticPolynomial (-1 : F) ≠ 1 := by
    intro h
    have := quadraticPolynomial_natDegree (-1 : F)
    rw [h, natDegree_one] at this
    norm_num at this
  have h1 : AdjoinRoot.mk (quadraticPolynomial (-1 : F)) p =
      AdjoinRoot.mk _ (p %ₘ quadraticPolynomial (-1 : F)) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ quadraticPolynomial (-1 : F), by
      linear_combination (Polynomial.modByMonic_add_div p (quadraticPolynomial (-1 : F))).symm⟩
  have hdeg : (p %ₘ quadraticPolynomial (-1 : F)).natDegree ≤ 1 := by
    have h := Polynomial.natDegree_modByMonic_lt p hf hf1
    rw [quadraticPolynomial_natDegree] at h
    omega
  obtain ⟨g, hg1, hg2⟩ : ∃ g : F[X], g = p %ₘ quadraticPolynomial (-1 : F) ∧ g.natDegree ≤ 1 :=
    ⟨_, rfl, hdeg⟩
  rw [h1, ← hg1]
  have hg := Polynomial.eq_X_add_C_of_natDegree_le_one hg2
  refine ⟨g.coeff 0, g.coeff 1, ?_⟩
  conv_lhs => rw [hg]
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq]
  ring

theorem coord_eq (hns : ¬ IsSquare (-1 : F)) {a b c d : F}
    (h : algebraMap F 𝔼 a + algebraMap F 𝔼 b * 𝕣 = algebraMap F 𝔼 c + algebraMap F 𝔼 d * 𝕣) :
    a = c ∧ b = d := by
  have := StabL.eq_zero_of_add_mul_root hns (x := a - c) (y := b - d) (by
    rw [map_sub, map_sub]
    linear_combination h)
  exact ⟨sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩

theorem zM_pow_coord (hr : 𝕣 * 𝕣 = -1) {e : 𝔼} {x y : F}
    (he : e = algebraMap F 𝔼 x + algebraMap F 𝔼 y * 𝕣) (j : ℕ) :
    ∃ c d : F, e ^ j = algebraMap F 𝔼 c + algebraMap F 𝔼 d * 𝕣 ∧ zM x y ^ j = zM c d := by
  induction j with
  | zero => exact ⟨1, 0, by simp, by rw [pow_zero, zM_one_zero]⟩
  | succ j ih =>
    obtain ⟨c, d, h1, h2⟩ := ih
    refine ⟨c * x - d * y, c * y + d * x, ?_, ?_⟩
    · rw [pow_succ, h1, he]
      simp only [map_sub, map_add, map_mul]
      linear_combination (algebraMap F 𝔼 d * algebraMap F 𝔼 y) * hr
    · rw [pow_succ, h2, zM_mul_zM]

variable [Fintype F]

theorem exists_zM (hq : Fintype.card F % 4 = 3) {m : ℕ} (hm : 1 ≤ m)
    (hm1 : 2 ^ m ∣ Fintype.card F + 1) (hm2 : ¬ 2 ^ (m + 1) ∣ Fintype.card F + 1) :
    ∃ x y : F, x ^ 2 + y ^ 2 = -1 ∧
      (zM x y ^ 2 ^ (m - 1) = kap ∨ zM x y ^ 2 ^ (m - 1) = -kap) := by
  classical
  have hns : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  have : Fact (¬ IsSquare (-1 : F)) := ⟨hns⟩
  have : Finite 𝔼 := Module.finite_of_finite F
  have hr : 𝕣 * 𝕣 = -1 := by
    rw [← sq, extension_root_square, map_neg, map_one]
  have hE : Nat.card 𝔼 = Fintype.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), extension_finrank, Nat.card_eq_fintype_card]
  have hEu : Nat.card 𝔼ˣ = Fintype.card F ^ 2 - 1 := by
    rw [Nat.card_units, hE]
  have hq3 : 3 ≤ Fintype.card F := by omega
  have hdvd : 2 ^ (m + 1) ∣ Fintype.card F ^ 2 - 1 := by
    have e : Fintype.card F ^ 2 - 1 = (Fintype.card F - 1) * (Fintype.card F + 1) := by
      zify [(by omega : 1 ≤ Fintype.card F), Nat.one_le_pow 2 _ (by omega : 0 < Fintype.card F)]
      ring
    rw [e, pow_succ, mul_comm (2 ^ m)]
    exact Nat.mul_dvd_mul (by omega) hm1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := 𝔼ˣ)
  have hog : orderOf g = Fintype.card F ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hEu]
  have hog0 : orderOf g ≠ 0 := by
    rw [hog]
    have : 9 ≤ Fintype.card F ^ 2 := by nlinarith
    omega
  obtain ⟨z, hoz⟩ : ∃ z : 𝔼ˣ, orderOf z = 2 ^ (m + 1) :=
    ⟨_, orderOf_pow_orderOf_div hog0 (by rw [hog]; exact hdvd)⟩
  have hz2 : (z : 𝔼) ^ 2 ^ m = -1 := by
    have h1 : (z : 𝔼) ^ 2 ^ m * (z : 𝔼) ^ 2 ^ m = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', ← Units.val_pow_eq_pow_val, ← hoz,
        pow_orderOf_eq_one, Units.val_one]
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · exfalso
      have h' : z ^ 2 ^ m = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
      have h3 := Nat.le_of_dvd (pow_pos two_pos _) (hoz ▸ orderOf_dvd_of_pow_eq_one h')
      have h4 := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self m)
      omega
    · exact h
  have hu : (z : 𝔼) ^ 2 ^ (m - 1) = 𝕣 ∨ (z : 𝔼) ^ 2 ^ (m - 1) = -𝕣 := by
    have h1 : (z : 𝔼) ^ 2 ^ (m - 1) * (z : 𝔼) ^ 2 ^ (m - 1) = 𝕣 * 𝕣 := by
      rw [hr, ← pow_add, ← two_mul, ← pow_succ', show m - 1 + 1 = m by omega, hz2]
    have h2 : ((z : 𝔼) ^ 2 ^ (m - 1) - 𝕣) * ((z : 𝔼) ^ 2 ^ (m - 1) + 𝕣) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  obtain ⟨x, y, hxy⟩ := exists_coord (z : 𝔼)
  obtain ⟨c, d, hcd1, hcd2⟩ := zM_pow_coord hr hxy (2 ^ (m - 1))
  refine ⟨x, y, ?_, ?_⟩
  ·
    obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
    have : Fact (ringChar F).Prime := ⟨hp⟩
    have : CharP 𝔼 (ringChar F) :=
      charP_of_injective_algebraMap (algebraMap F 𝔼).injective (ringChar F)
    have hrq : 𝕣 ^ Fintype.card F = -𝕣 := by
      obtain ⟨s, hs⟩ : ∃ s, Fintype.card F = 4 * s + 3 := ⟨Fintype.card F / 4, by omega⟩
      rw [hs, show 4 * s + 3 = 2 * (2 * s + 1) + 1 by ring, pow_succ, pow_mul, sq, hr,
        Odd.neg_one_pow ⟨s, rfl⟩, neg_one_mul]
    have hzq : (z : 𝔼) ^ Fintype.card F = algebraMap F 𝔼 x - algebraMap F 𝔼 y * 𝕣 := by
      rw [hxy, hcard, add_pow_char_pow, mul_pow, ← map_pow, ← map_pow, ← hcard,
        FiniteField.pow_card, FiniteField.pow_card, hrq]
      ring
    have hzq1 : (z : 𝔼) ^ (Fintype.card F + 1) = algebraMap F 𝔼 (x ^ 2 + y ^ 2) := by
      rw [pow_succ, hzq, hxy]
      simp only [map_add, map_pow]
      linear_combination (-(algebraMap F 𝔼 y ^ 2)) * hr
    have hzq2 : (z : 𝔼) ^ (Fintype.card F + 1) = -1 := by
      obtain ⟨u, hu⟩ := hm1
      have hu_odd : Odd u := by
        rcases Nat.even_or_odd u with ⟨v, hv⟩ | h
        · exfalso
          exact hm2 ⟨v, by rw [hu, hv, pow_succ]; ring⟩
        · exact h
      rw [hu, pow_mul, hz2, hu_odd.neg_one_pow]
    have : algebraMap F 𝔼 (x ^ 2 + y ^ 2) = algebraMap F 𝔼 (-1) := by
      rw [← hzq1, hzq2, map_neg, map_one]
    exact (algebraMap F 𝔼).injective this
  · rw [hcd2]
    rcases hu with h | h
    · left
      rw [hcd1] at h
      have h' : algebraMap F 𝔼 c + algebraMap F 𝔼 d * 𝕣 =
          algebraMap F 𝔼 0 + algebraMap F 𝔼 1 * 𝕣 := by
        rw [h, map_zero, map_one, zero_add, one_mul]
      obtain ⟨hc, hd⟩ := coord_eq hns h'
      rw [hc, hd, zM_zero_one]
    · right
      rw [hcd1] at h
      have h' : algebraMap F 𝔼 c + algebraMap F 𝔼 d * 𝕣 =
          algebraMap F 𝔼 0 + algebraMap F 𝔼 (-1) * 𝕣 := by
        rw [h, map_zero, map_neg, map_one, zero_add, neg_one_mul]
      obtain ⟨hc, hd⟩ := coord_eq hns h'
      rw [hc, hd, zM_zero_neg_one]

end L4M

end CFSG.ComponentClassification.GSThmB.P29

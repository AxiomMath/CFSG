module

public import CFSG.ClassicalInvolution.Phan.PhanQ32LeafR
public import CFSG.ClassicalInvolution.Phan.PhanQ28Leaf0
public import CFSG.ClassicalInvolution.Phan.PhanQ30LeafPi

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section Frame2

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem inW0_of_wc_zero {v : V8 K} (h : ∀ k, wc v k = 0) : InW0 v :=
  inW0_of_coord (by have := h 0; rwa [wc_zero] at this) (by have := h 2; rwa [wc_two] at this)
    (by have := h 1; rwa [wc_one] at this) (by have := h 3; rwa [wc_three] at this)

theorem coord_ne_of_not_zero {d : V8 K} (h : ¬ ∀ k, wc d k = 0) :
    d (Sum.inl 2) ≠ 0 ∨ d (Sum.inl 3) ≠ 0 ∨ d (Sum.inr 2) ≠ 0 ∨ d (Sum.inr 3) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  apply h
  intro k
  fin_cases k <;> simp [wc, h1, h2, h3, h4]

theorem four_ne_of_exists {r : Fin 4 → K} (h : ∃ k, r k ≠ 0) :
    r 0 ≠ 0 ∨ r 1 ≠ 0 ∨ r 2 ≠ 0 ∨ r 3 ≠ 0 := by
  obtain ⟨k, hk⟩ := h
  fin_cases k
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)
  · exact Or.inr (Or.inr (Or.inl hk))
  · exact Or.inr (Or.inr (Or.inr hk))

theorem exists_kappa {c d : V8 K} (hw : ∀ i j, wedge c d i j = 0) (hc : ¬ ∀ k, wc c k = 0)
    (hd : ¬ ∀ k, wc d k = 0) : ∃ κ : K, κ ≠ 0 ∧ ∀ k, wc c k = κ * wc d k := by
  obtain ⟨l, m, hlm, hrel⟩ := exists_parallel_of_wedge_zero (X := wc c) (Y := wc d)
    (fun i j => hw i j)
  have hl : l ≠ 0 := by
    intro hl0
    have hm : m ≠ 0 := by
      rcases hlm with h | h
      · exact absurd hl0 h
      · exact h
    apply hd
    intro k
    have := hrel k
    rw [hl0, zero_mul, zero_add] at this
    exact (mul_eq_zero.1 this).resolve_left hm
  have hm : m ≠ 0 := by
    intro hm0
    apply hc
    intro k
    have := hrel k
    rw [hm0, zero_mul, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hl
  refine ⟨-m / l, div_ne_zero (neg_ne_zero.2 hm) hl, fun k => ?_⟩
  have h := hrel k
  have : wc c k = -(m * wc d k) / l := by
    rw [eq_div_iff hl]
    linear_combination h
  rw [this]
  ring

theorem exists_rational_direction {d : V8 K} (hd : ∃ k, wc d k ≠ 0)
    (hrat : ∀ i j, wedge d (conj D d) i j = 0) :
    ∃ (r : Fin 4 → K) (ρ : K), ρ ≠ 0 ∧ (∀ k, D.τ (r k) = r k) ∧ (∃ k, r k ≠ 0) ∧
      ∀ k, wc d k = ρ * r k := by
  obtain ⟨j, hj⟩ := hd
  refine ⟨fun k => wc d k / wc d j, wc d j, hj, fun k => ?_, ⟨j, ?_⟩, fun k => ?_⟩
  · have h := hrat k j
    simp only [wedge, wc_conj] at h
    have hτj : D.τ (wc d j) ≠ 0 := (map_ne_zero D.τ).2 hj
    show D.τ (wc d k / wc d j) = wc d k / wc d j
    rw [map_div₀, div_eq_div_iff hτj hj]
    linear_combination (-1 : K) * h
  · show wc d j / wc d j ≠ 0
    rw [div_self hj]
    exact one_ne_zero
  · show wc d k = wc d j * (wc d k / wc d j)
    field_simp

variable [Fintype K] [DecidableEq K]

theorem quad_frame (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {a b c d : V8 K} (Fr : QFrame D a b c d) :
    Resolved D a b c d := by
  by_cases hL0 : ∃ i j, wedge c d i j ≠ 0
  · obtain ⟨e, hef, he1, he2, he3, he4⟩ := exists_common_nbr_of_wedge (D := D) h2 hq2 hq5 Fr.ha
      Fr.hb Fr.haf Fr.hbf Fr.hcf Fr.hdf Fr.hab Fr.hbc Fr.hda hL0
    exact Or.inl ⟨e, hef, he1, he2, he3, he4⟩
  push Not at hL0
  by_cases hcz : ∀ k, wc c k = 0
  · by_cases hdz : ∀ k, wc d k = 0
    · refine leaf_A D h2 hε Fr (r1 := 1) (r2 := 0) (r3 := 1) (r4 := 0) (ρc := 0) (ρd := 0)
        (map_one D.τ) (map_zero D.τ) (map_one D.τ) (map_zero D.τ) (by simp) ?_ ?_
      · intro k
        rw [hcz k, zero_mul]
      · intro k
        rw [hdz k, zero_mul]
    · exact leaf_NR0 D h2 hq2 hq5 Fr (inW0_of_wc_zero hcz) (coord_ne_of_not_zero hdz)
  · by_cases hdz : ∀ k, wc d k = 0
    · exact Resolved.of_mirror (leaf_NR0 D h2 hq2 hq5 Fr.mirror (inW0_of_wc_zero hdz)
        (coord_ne_of_not_zero hcz))
    · obtain ⟨κ, hκ, hcd2⟩ := exists_kappa hL0 hcz hdz
      by_cases hnr : ∃ i j, wedge d (conj D d) i j ≠ 0
      · exact leaf_pi D h2 hq2 hq5 Fr hκ hcd2 hnr
      push Not at hnr
      obtain ⟨r, ρ, hρ, hrfix, hrne, hdr⟩ := exists_rational_direction D (not_forall.1 hdz) hnr
      have hrk : ∀ k : Fin 4, ![r 0, r 1, r 2, r 3] k = r k := by
        intro k
        fin_cases k <;> rfl
      have hc2 : ∀ k, wc c k = (κ * ρ) * ![r 0, r 1, r 2, r 3] k := by
        intro k
        rw [hcd2 k, hdr k, hrk k]
        ring
      have hd2 : ∀ k, wc d k = ρ * ![r 0, r 1, r 2, r 3] k := by
        intro k
        rw [hdr k, hrk k]
      by_cases hrQ : r 0 * r 2 + r 1 * r 3 = 0
      · by_cases hbd : B8 b d = 0
        · exact leaf_P D h2 hq2 hq5 Fr κ hcd2 hnr hbd (coord_ne_of_not_zero hdz)
        · by_cases hac : B8 a c = 0
          · have hκ' : ∀ k, wc d k = κ⁻¹ * wc c k := by
              intro k
              rw [hcd2 k, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul]
            have hratc : ∀ i j, wedge c (conj D c) i j = 0 := by
              intro i j
              have h := hnr i j
              simp only [wedge, wc_conj] at h ⊢
              rw [hcd2 i, hcd2 j, map_mul, map_mul]
              linear_combination (κ * D.τ κ) * h
            exact Resolved.of_mirror (leaf_P D h2 hq2 hq5 Fr.mirror κ⁻¹ hκ' hratc hac
              (coord_ne_of_not_zero hcz))
          · obtain ⟨r', s, s', H⟩ := exists_hypBasis (D := D) (hrfix 0) (hrfix 1) (hrfix 2)
              (hrfix 3) hrQ (four_ne_of_exists hrne)
            have hc3 : ∀ k, wc c k = (κ * ρ) * wc (wvec (r 0) (r 1) (r 2) (r 3)) k := by
              intro k
              rw [wc_wvec]
              exact hc2 k
            have hd3 : ∀ k, wc d k = ρ * wc (wvec (r 0) (r 1) (r 2) (r 3)) k := by
              intro k
              rw [wc_wvec]
              exact hd2 k
            exact leaf_R D h2 hε hq2 hq5 Fr H hc3 hd3 hρ hac hbd
      · exact leaf_A D h2 hε Fr (hrfix 0) (hrfix 1) (hrfix 2) (hrfix 3) hrQ hc2 hd2

end Frame2

end CFSG.ClassicalInvolution.PhanQ

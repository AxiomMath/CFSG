module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open
open scoped commutatorElement

section Idx

variable {G : Type*} [Group G]

theorem comm_eq_one_of_odd_order_pow {b x : G} (hb : Odd (orderOf b))
    (hbc : b * ⁅b, x⁆ = ⁅b, x⁆ * b) {n : ℕ} (hc : ⁅b, x⁆ ^ (2 ^ n) = 1) : b * x = x * b := by
  set c := ⁅b, x⁆ with hc'
  have hbx : b * x * b⁻¹ = c * x := by rw [hc', commutatorElement_def]; group
  have hbck : ∀ k : ℕ, b * c ^ k * b⁻¹ = c ^ k := fun k => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Commute.pow_right (show Commute b c from hbc) k).eq
  have key : ∀ k : ℕ, b ^ k * x * (b ^ k)⁻¹ = c ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc b ^ (k + 1) * x * (b ^ (k + 1))⁻¹ = b * (b ^ k * x * (b ^ k)⁻¹) * b⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = (b * c ^ k * b⁻¹) * (b * x * b⁻¹) := by rw [ih]; group
        _ = c ^ (k + 1) * x := by rw [hbck k, hbx, pow_succ, mul_assoc]
  have h1 : c ^ orderOf b = 1 := by
    have := key (orderOf b)
    rw [pow_orderOf_eq_one] at this
    simpa using this.symm
  have hcop : Nat.Coprime (orderOf b) (2 ^ n) := (Odd.coprime_two_right hb).pow_right n
  have hc1 : c = 1 := by
    have := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
      (orderOf_dvd_of_pow_eq_one hc)
    exact orderOf_eq_one_iff.1 this
  have : ⁅b, x⁆ = 1 := hc1
  rwa [commutatorElement_eq_one_iff_mul_comm] at this

variable [Finite G]

theorem centralize_of_index_two {y : G} {X Y : Subgroup G} (hy : Odd (orderOf y))
    (hYy : y ∈ Subgroup.normalizer (Y : Set G)) (hY2 : IsPGroup 2 Y) (hXY : X ≤ Y)
    (hcard : Nat.card Y = 2 * Nat.card X) (hXc : ∀ x ∈ X, y * x = x * y) :
    ∀ t ∈ Y, y * t = t * y := by
  have hidx : (X.subgroupOf Y).index = 2 := by
    have h := Subgroup.relIndex_mul_card (H := X) (K := Y)
    rw [inf_of_le_left hXY, hcard] at h
    have hpos : 0 < Nat.card X := Nat.card_pos
    have := Nat.eq_of_mul_eq_mul_right hpos h
    simpa [Subgroup.relIndex] using this
  intro t ht
  by_cases htX : t ∈ X
  · exact hXc t htX
  · have hsY : y * t * y⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 hYy t).1 ht
    have hsX : y * t * y⁻¹ ∉ X := by
      intro hs
      have h1 := hXc _ hs
      have h2 : y * (y * t * y⁻¹) = y * t := by rw [h1]; group
      exact htX (by rwa [mul_left_cancel h2] at hs)
    have hcX : ⁅y, t⁆ ∈ X := by
      have key := (Subgroup.mul_mem_iff_of_index_two hidx
        (a := (⟨y * t * y⁻¹, hsY⟩ : Y)) (b := (⟨t⁻¹, Y.inv_mem ht⟩ : Y))).2 (by
          constructor
          · intro h
            exact absurd (Subgroup.mem_subgroupOf.1 h) hsX
          · intro h
            exact absurd (X.inv_mem_iff.1 (Subgroup.mem_subgroupOf.1 h)) htX)
      have := Subgroup.mem_subgroupOf.1 key
      rwa [commutatorElement_def]
    obtain ⟨n, hn⟩ := hY2 (⟨⁅y, t⁆, by
      rw [commutatorElement_def]
      exact Y.mul_mem hsY (Y.inv_mem ht)⟩ : Y)
    exact comm_eq_one_of_odd_order_pow hy (hXc _ hcX) (n := n)
      (by simpa using congrArg Subtype.val hn)

theorem eq_or_eq_of_index_four_of_odd {R R₀ T : Subgroup G} {y : G} (hR2 : IsPGroup 2 R)
    (hR₀T : R₀ ≤ T) (hTR : T ≤ R) (hidx : Nat.card R = 4 * Nat.card R₀)
    (hy : Odd (orderOf y)) (hyR : y ∈ Subgroup.normalizer (R : Set G))
    (hyT : y ∈ Subgroup.normalizer (T : Set G)) (hyR₀ : ∀ r ∈ R₀, y * r = r * y)
    (hnc : ¬ ∀ r ∈ R, y * r = r * y) : T = R₀ ∨ T = R := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne₀, hneR⟩ := hcon
  have hlt₀ : R₀ < T := lt_of_le_of_ne hR₀T (Ne.symm hne₀)
  have hltR : T < R := lt_of_le_of_ne hTR hneR
  have hm : 0 < Nat.card R₀ := Nat.card_pos
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hR₀T
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hTR
  have hc₀ := Subgroup.card_lt_of_lt hlt₀
  have hcR := Subgroup.card_lt_of_lt hltR
  have hkj : k * j = 4 := by
    have h : Nat.card R₀ * (k * j) = Nat.card R₀ * 4 := by
      calc Nat.card R₀ * (k * j) = (Nat.card R₀ * k) * j := by ring
        _ = Nat.card T * j := by rw [← hk]
        _ = Nat.card R := hj.symm
        _ = Nat.card R₀ * 4 := by rw [hidx]; ring
    exact Nat.eq_of_mul_eq_mul_left hm h
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k
    · simp at hk; omega
    · simp at hk; omega
  have hj2 : 2 ≤ j := by
    by_contra h
    push Not at h
    interval_cases j
    · simp at hj; omega
    · simp at hj; omega
  have hk' : k = 2 := by
    have : k ≤ 2 := by
      by_contra h
      push Not at h
      nlinarith
    omega
  have hj' : j = 2 := by subst hk'; omega
  have hT2 : IsPGroup 2 T := hR2.to_le hTR
  have hyT' : ∀ t ∈ T, y * t = t * y :=
    centralize_of_index_two hy hyT hT2 hR₀T (by rw [hk, hk']; ring) hyR₀
  have hyR' : ∀ t ∈ R, y * t = t * y :=
    centralize_of_index_two hy hyR hR2 hTR (by rw [hj, hj']; ring) hyT'
  exact hnc hyR'

end Idx

section Chain

variable {G : Type*} [Group G] [Finite G] {R Z R₀ R₁ A : Subgroup G} {y : G}

theorem eq_of_index_four_chain (hR : timmesfeldIsExtraspecial ↥R)
    (hZ : Z = (Subgroup.center ↥R).map R.subtype) (hZR₀ : Z ≤ R₀) (hR₀R : R₀ ≤ R)
    (hR₀ : timmesfeldIsExtraspecial ↥R₀ ∨ Nat.card R₀ = 2)
    (hidx : Nat.card R = 4 * Nat.card R₀) (hAR₀ : A ≤ Subgroup.normalizer (R₀ : Set G))
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hyA : y ∈ A) (hy : Odd (orderOf y))
    (hyR₀ : ∀ r ∈ R₀, y * r = r * y) (hnc : ¬ ∀ r ∈ R, y * r = r * y)
    (hU : ∀ T : Subgroup G, IsPGroup 2 T → A ≤ Subgroup.normalizer (T : Set G) →
      T ≤ Subgroup.centralizer (Z : Set G) → T ≤ R)
    (hR₁ : IsPGroup 2 R₁) (hAR₁ : A ≤ Subgroup.normalizer (R₁ : Set G)) (h01 : R₀ < R₁) :
    R₁ = R := by
  have hbetween : ∀ T : Subgroup G, R₀ ≤ T → T ≤ R → A ≤ Subgroup.normalizer (T : Set G) →
      T = R₀ ∨ T = R := fun T hR₀T hTR hAT =>
    eq_or_eq_of_index_four_of_odd hR.1 hR₀T hTR hidx hy (hAR hyA) (hAT hyA) hyR₀ hnc
  have hM : ∀ T : Subgroup G, R₀ ≤ T → T ≤ R → A ≤ Subgroup.normalizer (T : Set G) →
      ∀ s ∈ T, (∀ t ∈ T, s * t = t * s) → s ∈ Z := by
    intro T hR₀T hTR hAT s hs hcomm
    rcases hbetween T hR₀T hTR hAT with rfl | rfl
    · exact (isExtraspecial_or_card_two_iff_radical hR hZ hZR₀ hR₀R).1 hR₀ s hs hcomm
    · rw [hZ]
      exact mem_center_map_iff.2 ⟨hs, fun r hr => (hcomm r hr).symm⟩
  obtain ⟨hR₁R, -⟩ := isExtraspecial_of_nondeg_chain hR hZ hZR₀ hR₀R hAR₀ hU hM hR₁ hAR₁ h01
  rcases hbetween R₁ h01.le hR₁R hAR₁ with h | h
  · exact absurd h (ne_of_gt h01)
  · exact h

end Chain

end CFSG.LocalAnalysis.GLTheoremA.H301B

end

module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb7

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem SCert.SE.ut_mul_split : ∀ u : UT3 F4c,
    (⟨u.a, 0, u.c + u.a * u.b⟩ : UT3 F4c) * ⟨0, u.b, 0⟩ = u := by
  decide +kernel

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

abbrev xX : D.Xt := D.piX ⟨D.x, D.S1_le_Y1 (D.toG_mem_S1 (by decide))⟩

abbrev tX : D.Xt := D.piX ⟨D.t, D.S1_le_Y1 (D.toG_mem_S1 (by decide))⟩

theorem not_conj_xX_tX :
    ¬ ∃ g : D.Xt, g⁻¹ * D.xX * g = D.tX := by
  rintro ⟨c, hc⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (zpowers D.lY) c
  have hc' : D.piX (g⁻¹ * ⟨D.x, D.S1_le_Y1 (D.toG_mem_S1 (by decide))⟩ * g) = D.tX := by
    rw [map_mul, map_mul, map_inv]
    exact hc
  obtain ⟨h, hh⟩ := D.exists_conj_Y1_of_conj_Xt (D.toG_mem_S1 (by decide)) (Subtype.ext (by
      rw [Subgroup.coe_mul, ← map_mul, show SE.gen 6 * SE.gen 6 = 1 by decide, map_one]; rfl))
    (Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, SE.invRep1_mul_self, map_one]; rfl))
    (fun h1 => SE.invRep1_ne_one (D.toG_injective ((congrArg Subtype.val h1).trans
      (map_one _).symm)))
    (fun h1 => SE.gen0_ne_invRep1 (D.toG_injective h1).symm) hc'
  exact D.not_conj_x_t ⟨h, by simpa using congrArg Subtype.val hh⟩

omit [Finite Y] in
theorem xX_mem_Ft : D.xX ∈ D.Ft := ⟨_, mem_subgroupOf.mpr ((D.toG_mem_F_iff).mpr (by decide)), rfl⟩

omit [Finite Y] in
theorem tX_mem_Ft : D.tX ∈ D.Ft := ⟨_, mem_subgroupOf.mpr ((D.toG_mem_F_iff).mpr (by decide)), rfl⟩

theorem xX_ne_one : D.xX ≠ 1 := by
  intro h
  dsimp only [xX, piX] at h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, D.mem_zpowers_l_iff] at h
  rcases h with h | h | h | h
  · exact absurd (D.toG_injective (h.trans (map_one _).symm)) (by decide)
  · exact absurd (D.toG_injective h) (by decide)
  · exact absurd (D.toG_injective h) (by decide)
  · exact absurd (D.toG_injective (h.trans (map_mul _ _ _).symm)) (by decide)

theorem tX_ne_one : D.tX ≠ 1 := by
  intro h
  dsimp only [tX, piX] at h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, D.mem_zpowers_l_iff] at h
  rcases h with h | h | h | h
  · exact absurd (D.toG_injective (h.trans (map_one _).symm)) (by decide)
  · exact absurd (D.toG_injective h) (by decide)
  · exact absurd (D.toG_injective h) (by decide)
  · exact absurd (D.toG_injective (h.trans (map_mul _ _ _).symm)) (by decide)

theorem mem_T_iff_mul (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) {w : D.Xt}
    (hw : w ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    ∃ e ∈ D.Et, ∃ f ∈ D.Ft, w = e * f := by
  set u := D.tUT hO hz ⟨w, hw⟩
  set e := (D.tUT hO hz).symm ⟨u.a, 0, u.c + u.a * u.b⟩
  set f := (D.tUT hO hz).symm ⟨0, u.b, 0⟩
  refine ⟨e, ?_, f, ?_, ?_⟩
  · rw [D.mem_Et_iff_tUT hO hz e.2]
    simp [e]
  · rw [D.mem_Ft_iff_tUT hO hz f.2]
    simp [f]
  · have h : e * f = ⟨w, hw⟩ := by
      apply (D.tUT hO hz).injective
      rw [map_mul]
      simp only [e, f, MulEquiv.apply_symm_apply]
      exact SE.ut_mul_split u
    rw [← Subgroup.coe_mul, h]


theorem eq_one_of_centralizes_ZT (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (hE : D.Et.Normal) (hF : D.Ft.Normal)
    (hC : centralizer (((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) : Set D.Xt) ≤
      ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt))
    {w : D.Xt} (hodd : Odd (orderOf w)) (hZ : ∀ c ∈ D.Et ⊓ D.Ft, w * c = c * w) : w = 1 := by
  have hwE := D.centralizes_Et hodd hZ fun e he => hE.conj_mem e he w
  have hwF := D.centralizes_Ft hodd hZ fun f hf => hF.conj_mem f hf w
  have hwT : w ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) := by
    refine hC (mem_centralizer_iff.mpr fun τ hτ => ?_)
    obtain ⟨e, he, f, hf, rfl⟩ := D.mem_T_iff_mul hO hz hτ
    rw [mul_assoc, ← hwF f hf, ← mul_assoc, ← hwE e he, mul_assoc]
  have h2 := (D.sylowXt hO hz).isPGroup' ⟨w, hwT⟩
  obtain ⟨k, hk⟩ := h2
  have hk' : w ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  rcases b with _ | b
  · rwa [pow_zero, orderOf_eq_one_iff] at hb
  · rw [hb] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, b.succ_ne_zero⟩))

theorem index_ne_nine (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (hE : D.Et.Normal) (hF : D.Ft.Normal)
    (hC : centralizer (((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) : Set D.Xt) ≤
      ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt).index ≠ 9 := by
  intro h9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card D.Xt = 9 * 64 := by
    rw [← h9, ← Subgroup.index_mul_card, show Nat.card ((D.sylowXt hO hz : Sylow 2 D.Xt) :
      Subgroup D.Xt) = 64 by
        rw [Nat.card_congr (D.tUT hO hz).toEquiv]; exact card_UT3c]
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 D.Xt))
  have hP9 : Nat.card (P : Subgroup D.Xt) = 9 := by
    rw [Sylow.card_eq_multiplicity, hcard, show (9 * 64 : ℕ) = 3 ^ 2 * 64 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 64)]
    norm_num
  obtain ⟨w, hwP, hw1, hwZ⟩ := D.exists_centralizes_ZT hO hz (by rw [hP9])
    (fun w _ e he => hE.conj_mem e he w) (fun w _ f hf => hF.conj_mem f hf w)
  have hodd : Odd (orderOf w) := by
    have hdvd : orderOf w ∣ 9 := by
      rw [← hP9, ← Subgroup.orderOf_mk w hwP]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat (by decide) hdvd
  exact hw1 (D.eq_one_of_centralizes_ZT hO hz hE hF hC hodd hwZ)

end GHSylow

end CFSG.ComponentClassification.GHarris

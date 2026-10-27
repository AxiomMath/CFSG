module

public import CFSG.LargeExtraspecial.AS35QTSCountW

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTS

open Subgroup

variable {G : Type} [Group G]

theorem card_codes : codes.toFinset.card = 82944 := by
  classical
  have h1 : Nat.card CC = codes.toFinset.card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨psiCode x, ?_⟩) ⟨?_, ?_⟩)
    · exact List.mem_toFinset.mpr (psiCode_mem x)
    · intro x y h
      exact psiCode_injective (congrArg Subtype.val h)
    · rintro ⟨c, hc⟩
      obtain ⟨x, hx⟩ := exists_psiCode_eq (List.mem_toFinset.mp hc)
      exact ⟨x, Subtype.ext hx⟩
  rw [← h1, natCard_CC, List.toFinset_card_of_nodup qts_lists.2.1, qts_lists.1]

namespace Chart

variable {S : Setting G} [Finite G] (T : Chart S)

omit [Finite G] in
include T in
theorem natCard_M : Nat.card S.M = 82944 := by
  classical
  rw [← card_codes, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨T.th x, ?_⟩) ⟨?_, ?_⟩)
  · exact List.mem_toFinset.mpr (T.th_mem x x.2)
  · intro x y h
    exact Subtype.ext (T.th_injOn x x.2 y y.2 (congrArg Subtype.val h))
  · rintro ⟨c, hc⟩
    obtain ⟨x, hx, hxc⟩ := T.th_surj c (List.mem_toFinset.mp hc)
    exact ⟨⟨x, hx⟩, Subtype.ext hxc⟩

include T in
theorem natCard_G (hS : S.SixHyp) : Nat.card G = 13685760 := by
  obtain ⟨t₀, ht₀, htc⟩ := T.exists_t0 hS
  have ht₀M := t0_mem_M ht₀ hS
  have h := card_eq_thompson S.z_mul_z S.z_ne_one (w_mul_self ht₀ hS) (w_ne_one ht₀)
    (fun y hy hy1 => T.isConj_or_isConj hS ht₀M (t0_isConj ht₀) (t0_ne ht₀) hy hy1)
    (T.not_isConj_mul hS ht₀M (t0_isConj ht₀) (t0_ne ht₀))
  rw [h, T.count_z hS ht₀, T.count_w hS ht₀ htc, T.natCard_centralizer_w hS ht₀ htc]
  change 1188 * 4608 + 99 * Nat.card S.M = 13685760
  rw [T.natCard_M]

include T in
theorem ncard_D (hS : S.SixHyp) : {x | IsConj S.z x}.ncard = 165 := by
  have h := ncard_conj_mul_card_centralizer S.z
  change _ * Nat.card S.M = _ at h
  rw [T.natCard_M, T.natCard_G hS] at h
  omega

include T in
theorem exists_common_neighbour (hS : S.SixHyp) {e : G} (he : IsConj S.z e)
    (hez : ¬ e * S.z = S.z * e) :
    ∃ p, IsConj S.z p ∧ p * S.z = S.z * p ∧ p * e = e * p ∧ p ≠ S.z := by
  classical
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨t₀, ht₀, -⟩ := T.exists_t0 hS
  have ht₀M := t0_mem_M ht₀ hS
  have hzt : t₀ * S.z = S.z * t₀ := S.mem_M_iff.mp ht₀M
  have ht₀z := t0_isConj ht₀
  have hne := t0_ne ht₀
  set Df := Finset.univ.filter fun x : G => IsConj S.z x
  set ℓf := Finset.univ.filter fun x : G => x ∈ lineSet S S.z t₀
  set X := Df \ ℓf
  set I := (X ×ˢ ℓf).filter fun q : G × G => q.1 * q.2 = q.2 * q.1
  have hDf : Df.card = 165 := by
    rw [← T.ncard_D hS, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [Df]
  have hℓf : ℓf.card = 5 := by
    rw [← T.ncard_lineSet_at hS (IsConj.refl _) ht₀z hzt hne, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [ℓf]
  have hℓD : ℓf ⊆ Df := by
    intro x hx
    simp only [ℓf, Df, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1
  have hX : X.card = 160 := by
    rw [Finset.card_sdiff_of_subset hℓD, hDf, hℓf]
  have hfib : ∀ p ∈ ℓf, (X.filter fun x => x * p = p * x).card = 32 := by
    intro p hp
    simp only [ℓf, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have h37 : (Df.filter fun x => x * p = p * x).card = 37 := by
      rw [← T.ncard_DC hS hp.1, ← Set.ncard_coe_finset]
      congr 1
      ext x
      simp [Df]
    have hsub : ℓf ⊆ Df.filter fun x => x * p = p * x := by
      intro y hy
      simp only [ℓf, Df, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact ⟨hy.1, T.commute_of_mem_lineSet_at hS (IsConj.refl _) ht₀z hzt hne hy hp⟩
    have e : (X.filter fun x => x * p = p * x) = (Df.filter fun x => x * p = p * x) \ ℓf := by
      ext x
      simp only [X, Finset.mem_filter, Finset.mem_sdiff]
      tauto
    rw [e, Finset.card_sdiff_of_subset hsub, h37, hℓf]
  have hI : I.card = 160 := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun q : G × G => q.2) (s := I) (t := ℓf)
      (fun q hq => (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2)
    rw [this, Finset.sum_congr rfl (g := fun _ => 32), Finset.sum_const, hℓf, smul_eq_mul]
    intro p hp
    rw [← hfib p hp]
    refine Finset.card_bij (fun q _ => q.1) ?_ ?_ ?_
    · intro q hq
      simp only [I, Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨⟨hq1, -⟩, hq3⟩, rfl⟩ := hq
      exact Finset.mem_filter.mpr ⟨hq1, hq3⟩
    · intro q hq q' hq' e
      simp only [I, Finset.mem_filter, Finset.mem_product] at hq hq'
      exact Prod.ext e (hq.2.trans hq'.2.symm)
    · intro x hx
      obtain ⟨hxX, hxp⟩ := Finset.mem_filter.mp hx
      exact ⟨(x, p), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hxX, hp⟩, hxp⟩, rfl⟩, rfl⟩
  have hinj : Set.InjOn (fun q : G × G => q.1) I := by
    intro q hq q' hq' e
    have hq1 := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    have hq2 := Finset.mem_filter.mp (Finset.mem_coe.mp hq')
    simp only at e
    by_contra hqq
    have hpp : q.2 ≠ q'.2 := fun h => hqq (Prod.ext e h)
    obtain ⟨hqX, hp⟩ := Finset.mem_product.mp hq1.1
    obtain ⟨-, hp'⟩ := Finset.mem_product.mp hq2.1
    simp only [ℓf, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    obtain ⟨hxD, hxl⟩ := Finset.mem_sdiff.mp hqX
    simp only [Df, ℓf, Finset.mem_filter, Finset.mem_univ, true_and] at hxD hxl
    have hl := T.lineSet_eq_of_mem hS (IsConj.refl _) ht₀z hzt hne hp hp' hpp
    apply hxl
    rw [← hl]
    exact ⟨hxD, hq1.2, e ▸ hq2.2⟩
  have himage : I.image (fun q => q.1) = X := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    · rw [Finset.card_image_of_injOn hinj, hX, hI]
  have heX : e ∈ X := by
    simp only [X, Df, ℓf, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨he, fun h => hez h.2.1⟩
  rw [← himage] at heX
  obtain ⟨⟨x, p⟩, hq, rfl⟩ := Finset.mem_image.mp heX
  simp only [I, Finset.mem_filter, Finset.mem_product, ℓf, Finset.mem_univ, true_and] at hq
  obtain ⟨⟨-, hp⟩, hxp⟩ := hq
  refine ⟨p, hp.1, hp.2.1, hxp.symm, ?_⟩
  rintro rfl
  exact hez hxp

include T in
theorem orderOf_mem (hS : S.SixHyp) (g₁ g₂ : G) :
    orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ) := by
  set g := g₁⁻¹ * g₂
  set e := g * S.z * g⁻¹ with he
  have hconj : g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹) = g₁ * (S.z * e) * g₁⁻¹ := by
    rw [he]
    simp only [g]
    group
  rw [hconj, Setting.orderOf_conj_eq]
  have hez : IsConj S.z e := isConj_iff.mpr ⟨g, rfl⟩
  have hee := S.mul_self_of_isConj hez
  have h23 : (S.z * e) ^ 2 = 1 ∨ (S.z * e) ^ 3 = 1 := by
    by_cases hc : e * S.z = S.z * e
    · left
      rw [pow_two]
      calc S.z * e * (S.z * e) = S.z * (e * S.z) * e := by group
        _ = S.z * (S.z * e) * e := by rw [hc]
        _ = 1 := by rw [← mul_assoc S.z S.z e, S.z_mul_z, one_mul, hee]
    · obtain ⟨p, hp, hpz, hpe, -⟩ := T.exists_common_neighbour hS hez hc
      exact T.orderOf_mul_dvd_at hS hp (IsConj.refl _) hez hpz.symm hpe.symm
  rcases h23 with h | h
  · have := orderOf_dvd_of_pow_eq_one h
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h1 <;> simp [h1]
  · have := orderOf_dvd_of_pow_eq_one h
    rcases (Nat.dvd_prime Nat.prime_three).mp this with h1 | h1 <;> simp [h1]

end Chart

theorem orderOf_mem_of_iso [Finite G] (S : Setting G)
    (hS : S.SixHyp) (hiso : Nonempty (centralizer ({S.z} : Set G) ≃* CC)) (g₁ g₂ : G) :
    orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨φ⟩ := hiso
  exact (chartOf S φ).orderOf_mem hS g₁ g₂

end CFSG.LargeExtraspecial.AS35QTS

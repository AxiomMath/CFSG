module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup

section Order156

variable {A : Type*} [Group A]

theorem eq_of_mem_zpowers_of_orderOf_eq_three {z w : A} (hz : orderOf z = 3)
    (hw : w ∈ zpowers z) : w = 1 ∨ w = z ∨ w = z * z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  rw [← zpow_mod_orderOf, hz]
  have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  generalize k % ((3 : ℕ) : ℤ) = r at h0 h3 ⊢
  interval_cases r
  · exact Or.inl (zpow_zero z)
  · exact Or.inr (Or.inl (zpow_one z))
  · exact Or.inr (Or.inr (zpow_two z))

theorem pow_three_eq_one_of_orderOf_eq_three {z : A} (hz : orderOf z = 3) : z ^ 3 = 1 := by
  rw [← hz]
  exact pow_orderOf_eq_one z

theorem eq_one_of_pow_four_of_commute
    (hNE : ∀ g z : A, orderOf z = 3 → g * z * g⁻¹ ∈ zpowers z → g ^ 39 = 1)
    {g z : A} (hg : g ^ 4 = 1) (hz : orderOf z = 3) (hgz : g * z = z * g) : g = 1 := by
  have h1 : g * z * g⁻¹ ∈ zpowers z := by
    rw [hgz, mul_inv_cancel_right]
    exact mem_zpowers z
  have h39 := hNE g z hz h1
  have h3 : g ^ 3 = 1 := by
    rw [← h39, show (39 : ℕ) = 4 * 9 + 3 by norm_num, pow_add, pow_mul, hg, one_pow, one_mul]
  calc g = g ^ 4 * (g ^ 3)⁻¹ := by group
    _ = 1 := by rw [hg, h3]; simp

theorem commute_of_mem_normalizer_zpowers
    (hNE : ∀ g z : A, orderOf z = 3 → g * z * g⁻¹ ∈ zpowers z → g ^ 39 = 1)
    {z : A} (hz : orderOf z = 3) {g : A} (hg : g ∈ Subgroup.normalizer (zpowers z : Set A)) :
    g * z = z * g := by
  have hz3 : z ^ 3 = 1 := pow_three_eq_one_of_orderOf_eq_three hz
  have hgz : g * z * g⁻¹ ∈ zpowers z := (mem_normalizer_iff.1 hg z).1 (mem_zpowers z)
  have h39 := hNE g z hz hgz
  rcases eq_of_mem_zpowers_of_orderOf_eq_three hz hgz with h | h | h
  · exfalso
    have hz1 : z = 1 := by
      have := congrArg (fun a => g⁻¹ * a * g) h
      simpa [mul_assoc] using this
    rw [hz1, orderOf_one] at hz
    omega
  · calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [h]
  · exfalso
    have h2 : g ^ 2 * z * (g ^ 2)⁻¹ = z := by
      calc g ^ 2 * z * (g ^ 2)⁻¹ = g * (g * z * g⁻¹) * g⁻¹ := by rw [pow_two]; group
        _ = g * (z * z) * g⁻¹ := by rw [h]
        _ = (g * z * g⁻¹) * (g * z * g⁻¹) := by group
        _ = (z * z) * (z * z) := by rw [h]
        _ = z ^ 3 * z := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = z := by rw [hz3, one_mul]
    have hsq : g ^ 2 * z = z * g ^ 2 := by
      calc g ^ 2 * z = g ^ 2 * z * (g ^ 2)⁻¹ * g ^ 2 := (inv_mul_cancel_right _ _).symm
        _ = z * g ^ 2 := by rw [h2]
    have hg20 : (g ^ 2) ^ 20 = g := by
      rw [← pow_mul, show 2 * 20 = 1 + 39 by norm_num, pow_add, h39, mul_one, pow_one]
    have hc : g * z = z * g := by
      rw [← hg20]
      exact (Commute.pow_left (show Commute (g ^ 2) z from hsq) 20).eq
    have hzz : z * z = z := by
      rw [← h]
      calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hc]
        _ = z := by group
    have hz1 : z = 1 := mul_left_cancel (a := z) (by simpa using hzz)
    rw [hz1, orderOf_one] at hz
    omega

end Order156

section Finite

variable {A : Type*} [Group A] [Finite A]

theorem exists_normal_card_four_of_card_156 (hcard : Nat.card A = 156) {c : A}
    (hc : orderOf c = 13) (hcc : ∀ g : A, g * c = c * g)
    (hNE : ∀ g z : A, orderOf z = 3 → g * z * g⁻¹ ∈ zpowers z → g ^ 39 = 1) :
    ∃ V : Subgroup A, V.Normal ∧ Nat.card V = 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card A by rw [hcard]; norm_num)
  have hYcard : Nat.card (zpowers z) = 3 := by rw [Nat.card_zpowers, hz]
  have hYp : IsPGroup 3 (zpowers z) := IsPGroup.of_card (n := 1) (by rw [hYcard, pow_one])
  have hYidx : ¬ 3 ∣ (zpowers z).index := by
    have h := (zpowers z).card_mul_index
    rw [hYcard, hcard] at h
    have : (zpowers z).index = 52 := by omega
    rw [this]
    norm_num
  let P : Sylow 3 A := hYp.toSylow hYidx
  have hP : Subgroup.normalizer (P : Set A) ≤ Subgroup.centralizer (P : Set A) := by
    intro g hg
    have hcomm : g * z = z * g := commute_of_mem_normalizer_zpowers hNE hz hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute z g from hcomm.symm) k).eq
  set K : Subgroup A := (MonoidHom.transferSylow P hP).ker with hK
  haveI hKn : K.Normal := MonoidHom.normal_ker _
  have hcompl : K.IsComplement' (P : Subgroup A) := MonoidHom.ker_transferSylow_isComplement' P hP
  have hK52 : Nat.card K = 52 := by
    have h := hcompl.card_mul_card
    have hP3 : Nat.card (P : Subgroup A) = 3 := hYcard
    rw [hP3, hcard] at h
    omega
  have hcK : c ∈ K := by
    rw [hK, MonoidHom.mem_ker]
    have h1 : orderOf (MonoidHom.transferSylow P hP c) ∣ 13 :=
      hc ▸ orderOf_map_dvd _ c
    have h2 : orderOf (MonoidHom.transferSylow P hP c) ∣ 3 := by
      have := orderOf_dvd_natCard (MonoidHom.transferSylow P hP c)
      rwa [show Nat.card (P : Subgroup A) = 3 from hYcard] at this
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2)
  obtain ⟨V₀, hV₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := K) 2 (n := 2)
    (by rw [hK52]; norm_num)
  set V : Subgroup A := V₀.map K.subtype with hV
  have hV4 : Nat.card V = 4 := by
    rw [hV, Subgroup.card_map_of_injective K.subtype_injective, hV₀]
    norm_num
  have hVK : V ≤ K := Subgroup.map_subtype_le V₀
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  have hVidx : ¬ 2 ∣ V.index := by
    have h := V.card_mul_index
    rw [hV4, hcard] at h
    have : V.index = 39 := by omega
    rw [this]
    norm_num
  let Q : Sylow 2 A := hVp.toSylow hVidx
  have hQV : (Q : Subgroup A) = V := rfl
  have hKN : K ≤ Subgroup.normalizer (V : Set A) := by
    have hVN : V ≤ Subgroup.normalizer (V : Set A) ⊓ K :=
      fun x hx => ⟨Subgroup.le_normalizer hx, hVK hx⟩
    have hcnorm : c ∈ Subgroup.normalizer (V : Set A) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [← hcc h, mul_inv_cancel_right]
    have hcN : c ∈ Subgroup.normalizer (V : Set A) ⊓ K := Subgroup.mem_inf.2 ⟨hcnorm, hcK⟩
    have h4 : 4 ∣ Nat.card (Subgroup.normalizer (V : Set A) ⊓ K : Subgroup A) :=
      hV4 ▸ Subgroup.card_dvd_of_le hVN
    have h13 : 13 ∣ Nat.card (Subgroup.normalizer (V : Set A) ⊓ K : Subgroup A) :=
      hc ▸ Subgroup.orderOf_dvd_natCard _ hcN
    have h52 : 52 ∣ Nat.card (Subgroup.normalizer (V : Set A) ⊓ K : Subgroup A) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h13
    have hle : Subgroup.normalizer (V : Set A) ⊓ K ≤ K := inf_le_right
    have hpos : 0 < Nat.card (Subgroup.normalizer (V : Set A) ⊓ K : Subgroup A) := Nat.card_pos
    have hge : Nat.card K ≤ Nat.card (Subgroup.normalizer (V : Set A) ⊓ K : Subgroup A) := by
      rw [hK52]
      exact Nat.le_of_dvd hpos h52
    have heq : Subgroup.normalizer (V : Set A) ⊓ K = K := Subgroup.eq_of_le_of_card_ge hle hge
    rw [← heq]
    exact inf_le_left
  have hfr : Subgroup.normalizer (V : Set A) ⊔ K = ⊤ := Sylow.normalizer_sup_eq_top' Q hVK
  have hnorm : Subgroup.normalizer (V : Set A) = ⊤ := by
    rw [eq_top_iff, ← hfr]
    exact sup_le le_rfl hKN
  exact ⟨V, Subgroup.normalizer_eq_top_iff.1 hnorm, hV4⟩

theorem mem_of_pow_four_eq_one (hcard : Nat.card A = 156) {V : Subgroup A} [V.Normal]
    (hV4 : Nat.card V = 4) {g : A} (hg : g ^ 4 = 1) : g ∈ V := by
  have hidx : V.index = 39 := by
    have h := V.card_mul_index
    rw [hV4, hcard] at h
    omega
  have hq : Nat.card (A ⧸ V) = 39 := by rw [← Subgroup.index_eq_card, hidx]
  have h4 : (QuotientGroup.mk g : A ⧸ V) ^ 4 = 1 := by
    rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
  have h39 : (QuotientGroup.mk g : A ⧸ V) ^ 39 = 1 := by
    rw [← hq]
    exact pow_card_eq_one'
  have h3 : (QuotientGroup.mk g : A ⧸ V) ^ 3 = 1 := by
    rw [← h39, show (39 : ℕ) = 4 * 9 + 3 by norm_num, pow_add, pow_mul, h4, one_pow, one_mul]
  have h1 : (QuotientGroup.mk g : A ⧸ V) = 1 := by
    calc (QuotientGroup.mk g : A ⧸ V) = (QuotientGroup.mk g : A ⧸ V) ^ 4 *
        ((QuotientGroup.mk g : A ⧸ V) ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, h3]; simp
  exact (QuotientGroup.eq_one_iff g).1 h1

theorem klein_of_card_156 (hcard : Nat.card A = 156) {c : A}
    (hc : orderOf c = 13) (hcc : ∀ g : A, g * c = c * g)
    (hNE : ∀ g z : A, orderOf z = 3 → g * z * g⁻¹ ∈ zpowers z → g ^ 39 = 1) :
    (∀ g : A, g ^ 4 = 1 → g ^ 2 = 1) ∧
      ∀ s t : A, s ≠ 1 → s ^ 2 = 1 → t ≠ 1 → t ^ 2 = 1 → ∃ a : A, a * s * a⁻¹ = t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hVn, hV4⟩ := exists_normal_card_four_of_card_156 hcard hc hcc hNE
  haveI := hVn
  have hmem : ∀ g : A, g ^ 4 = 1 → g ∈ V := fun g hg => mem_of_pow_four_eq_one hcard hV4 hg
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card A by rw [hcard]; norm_num)
  have hz3 : z ^ 3 = 1 := pow_three_eq_one_of_orderOf_eq_three hz
  have key : ∀ s : A, s ≠ 1 → s ^ 2 = 1 → ∀ x ∈ V, x ≠ 1 →
      x = s ∨ x = z * s * z⁻¹ ∨ x = (z * z) * s * (z * z)⁻¹ := by
    intro s hs1 hs2 x hxV hx1
    have hs4 : s ^ 4 = 1 := by rw [show 4 = 2 * 2 by norm_num, pow_mul, hs2, one_pow]
    have hsV : s ∈ V := hmem s hs4
    have hne1 : ∀ u : A, u * s * u⁻¹ ≠ 1 := by
      intro u hu
      apply hs1
      have := congrArg (fun a => u⁻¹ * a * u) hu
      simpa [mul_assoc] using this
    have hzs : s * z ≠ z * s := fun h =>
      hs1 (eq_one_of_pow_four_of_commute hNE hs4 hz h)
    have hab : s ≠ z * s * z⁻¹ := by
      intro h
      apply hzs
      calc s * z = z * s * z⁻¹ * z := by rw [← h]
        _ = z * s := by group
    have hzz4 : z * z * (z * z) = z := by
      calc z * z * (z * z) = z ^ 3 * z := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = z := by rw [hz3, one_mul]
    have had : s ≠ z * z * s * (z * z)⁻¹ := by
      intro h
      apply hzs
      have hc2 : s * (z * z) = (z * z) * s := by
        calc s * (z * z) = z * z * s * (z * z)⁻¹ * (z * z) := by rw [← h]
          _ = z * z * s := by group
      have := (Commute.mul_right (show Commute s (z * z) from hc2)
        (show Commute s (z * z) from hc2))
      rw [hzz4] at this
      exact this.eq
    have hbd : z * s * z⁻¹ ≠ z * z * s * (z * z)⁻¹ := by
      intro h
      apply hab
      calc s = z⁻¹ * (z * s * z⁻¹) * z := by group
        _ = z⁻¹ * (z * z * s * (z * z)⁻¹) * z := by rw [h]
        _ = z * s * z⁻¹ := by group
    set S : Set A := (V : Set A) \ {1} with hS
    have hS3 : S.ncard = 3 := by
      rw [hS, Set.ncard_diff_singleton_of_mem (show (1 : A) ∈ (V : Set A) from V.one_mem),
        ← Nat.card_coe_set_eq]
      have : Nat.card (V : Set A) = 4 := hV4
      omega
    have hT : ({s, z * s * z⁻¹, z * z * s * (z * z)⁻¹} : Set A) ⊆ S := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨hsV, hs1⟩
      · exact ⟨hVn.conj_mem s hsV z, hne1 z⟩
      · exact ⟨hVn.conj_mem s hsV (z * z), hne1 (z * z)⟩
    have hT3 : ({s, z * s * z⁻¹, z * z * s * (z * z)⁻¹} : Set A).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨_, _, _, hab, had, hbd, rfl⟩
    have hTS := Set.eq_of_subset_of_ncard_le hT (by rw [hS3, hT3])
    have hxS : x ∈ S := ⟨hxV, hx1⟩
    rw [← hTS] at hxS
    simpa [mul_assoc] using hxS
  refine ⟨?_, ?_⟩
  · intro g hg
    by_cases hg1 : g = 1
    · rw [hg1, one_pow]
    · obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2
        (show 2 ∣ Nat.card A by rw [hcard]; norm_num)
      have hs2 : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
      have hs1 : s ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hs
        omega
      have hconj : ∀ u : A, (u * s * u⁻¹) ^ 2 = 1 := fun u => by
        calc (u * s * u⁻¹) ^ 2 = u * s ^ 2 * u⁻¹ := conj_pow
          _ = 1 := by rw [hs2]; group
      rcases key s hs1 hs2 g (hmem g hg) hg1 with h | h | h
      · rw [h]; exact hs2
      · rw [h]; exact hconj z
      · rw [h]; exact hconj (z * z)
  · intro s t hs hs2 ht ht2
    have ht4 : t ^ 4 = 1 := by rw [show 4 = 2 * 2 by norm_num, pow_mul, ht2, one_pow]
    rcases key s hs hs2 t (hmem t ht4) ht with h | h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨z, h.symm⟩
    · exact ⟨z * z, h.symm⟩

end Finite

section Isolation

variable {C A : Type*} [Group C] [Group A]

theorem eq_one_or_eq_of_mul_self_eq_one (π : C →* A) (hπ : Function.Surjective π)
    {v : C} (hv1 : v ≠ 1) (hv2 : v * v = 1) (hvc : ∀ g : C, g * v = v * g)
    (hker : ∀ x : C, π x = 1 → x = 1 ∨ x = v)
    (hα : ∀ a : A, a ^ 4 = 1 → a ^ 2 = 1)
    (hβ : ∀ s t : A, s ≠ 1 → s ^ 2 = 1 → t ≠ 1 → t ^ 2 = 1 → ∃ a : A, a * s * a⁻¹ = t)
    {w : C} (hw4 : w ^ 4 = 1) (hw2 : w ^ 2 ≠ 1) {t : C} (ht : t * t = 1) :
    t = 1 ∨ t = v := by
  by_cases hπt : π t = 1
  · exact hker t hπt
  have hπw4 : π w ^ 4 = 1 := by rw [← map_pow, hw4, map_one]
  have hπw2 : π w ^ 2 = 1 := hα _ hπw4
  have hw2v : w ^ 2 = v := by
    rcases hker (w ^ 2) (by rw [map_pow, hπw2]) with h | h
    · exact absurd h hw2
    · exact h
  have hπw1 : π w ≠ 1 := by
    intro h
    rcases hker w h with h' | h'
    · exact hw2 (by rw [h', one_pow])
    · exact hw2 (by rw [h', pow_two, hv2])
  have hπt2 : π t ^ 2 = 1 := by rw [pow_two, ← map_mul, ht, map_one]
  obtain ⟨a, ha⟩ := hβ (π w) (π t) hπw1 hπw2 hπt hπt2
  obtain ⟨b, rfl⟩ := hπ a
  have hπw' : π (b * w * b⁻¹) = π t := by rw [map_mul, map_mul, map_inv]; exact ha
  have hw'2 : (b * w * b⁻¹) ^ 2 = v := by
    calc (b * w * b⁻¹) ^ 2 = b * w ^ 2 * b⁻¹ := conj_pow
      _ = b * v * b⁻¹ := by rw [hw2v]
      _ = v := by rw [hvc b, mul_inv_cancel_right]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hkk : π (b * w * b⁻¹ * t⁻¹) = 1 := by rw [map_mul, hπw', map_inv, mul_inv_cancel]
  exfalso
  apply hv1
  rcases hker _ hkk with h | h
  · have hw' : b * w * b⁻¹ = t := mul_inv_eq_one.1 h
    rw [← hw'2, hw', pow_two, ht]
  · have hw' : b * w * b⁻¹ = v * t := by
      rw [htinv] at h
      exact mul_inv_eq_iff_eq_mul.1 (by rw [htinv]; exact h)
    rw [← hw'2, hw']
    calc (v * t) ^ 2 = v * (t * v) * t := by rw [pow_two]; group
      _ = v * (v * t) * t := by rw [hvc t]
      _ = (v * v) * (t * t) := by group
      _ = 1 := by rw [hv2, ht, one_mul]

end Isolation

end CFSG.HardMathSupport.Dickson.Sec6.I1431

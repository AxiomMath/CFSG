module

public import CFSG.Holt.SmallGroups

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Equiv Equiv.Perm CFSG.Holt.SmallGroups


theorem m11_involution_fixedPoints {s : Perm (Fin 11)} (hs : s ∈ CFSG.Open.M11)
    (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    ∃ a b c : Fin 11, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ x, s x = x ↔ (x = a ∨ x = b ∨ x = c) := by
  have h2 : s ^ 2 = 1 := by rw [pow_two]; exact hs2
  have hct : s.cycleType = Multiset.replicate s.cycleType.card 2 :=
    cycleType_of_pow_prime_eq_one (p := 2) h2
  have hsum : s.support.card = s.cycleType.card * 2 := by
    rw [← sum_cycleType s, hct]
    simp [Multiset.sum_replicate, smul_eq_mul]
  have hsign : s.sign = 1 := by
    have h := m11_le_alternatingGroup hs
    rwa [mem_alternatingGroup] at h
  have hcardpos : 0 < s.cycleType.card := by
    rw [card_cycleType_pos]
    exact hs1
  have hsupport_le : s.support.card ≤ 11 := by
    simpa using Finset.card_le_univ s.support
  have heven : Even s.cycleType.card := by
    have h := sign_of_cycleType s
    rw [hsign, sum_cycleType, hsum] at h
    have h' : Even (s.cycleType.card * 2 + s.cycleType.card) :=
      (neg_one_pow_eq_one_iff_even (show (-1 : ℤˣ) ≠ 1 by decide)).mp h.symm
    simpa [Nat.even_add, Nat.even_mul] using h'
  have hk_cases : s.cycleType.card = 2 ∨ s.cycleType.card = 4 := by
    obtain ⟨m, hm⟩ := heven
    have hk_le : s.cycleType.card ≤ 5 := by omega
    have hm1 : 1 ≤ m := by omega
    have hm2 : m ≤ 2 := by omega
    have hm12 : m = 1 ∨ m = 2 := by omega
    rcases hm12 with rfl | rfl <;> omega
  rcases hk_cases with hk2 | hk4
  ·
    exfalso
    have hcard : s.support.card = 4 := by rw [hsum, hk2]
    have hcompl : (s.supportᶜ : Finset (Fin 11)).card = 7 := by
      rw [Finset.card_compl, hcard]
      simp
    obtain ⟨t, ht_sub, ht_card⟩ :=
      Finset.exists_subset_card_eq (s := s.supportᶜ) (n := 4) (by omega)
    let y : Fin 4 ↪ Fin 11 := (t.orderEmbOfFin ht_card).toEmbedding
    have hy : ∀ i, s (y i) = y i := by
      intro i
      have hi : y i ∈ t := by
        simpa [y] using Finset.orderEmbOfFin_mem t ht_card i
      have hnot : y i ∉ s.support := Finset.mem_compl.mp (ht_sub hi)
      exact Equiv.Perm.notMem_support.mp hnot
    exact absurd (eq_one_of_mem_m11_of_fix hs y hy) hs1
  ·
    have hcard : s.support.card = 8 := by rw [hsum, hk4]
    have hcompl : (s.supportᶜ : Finset (Fin 11)).card = 3 := by
      rw [Finset.card_compl, hcard]
      simp
    obtain ⟨a, b, c, hab, hac, hbc, hsc⟩ := Finset.card_eq_three.mp hcompl
    have hmem : ∀ x : Fin 11, (x ∈ s.supportᶜ) ↔ (x = a ∨ x = b ∨ x = c) := by
      intro x
      rw [hsc]
      simp
    refine ⟨a, b, c, hab, hac, hbc, fun x => ?_⟩
    rw [← hmem x, Finset.mem_compl, Equiv.Perm.notMem_support]

theorem m11_exists_conj_of_involutions {s t : Perm (Fin 11)} (hs : s ∈ CFSG.Open.M11)
    (hs2 : s * s = 1) (hs1 : s ≠ 1) (ht : t ∈ CFSG.Open.M11) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ g ∈ CFSG.Open.M11, g * s * g⁻¹ = t := by
  obtain ⟨a, b, c, hab, hac, hbc, hfixs⟩ := m11_involution_fixedPoints hs hs2 hs1
  obtain ⟨a', b', c', ha'b', ha'c', hb'c', hfixt⟩ := m11_involution_fixedPoints ht ht2 ht1
  obtain ⟨g₁, hg₁M, hg₁0, hg₁1, hg₁2⟩ := exists_mem_m11_apply_eq hab hac hbc
  obtain ⟨g₂, hg₂M, hg₂0, hg₂1, hg₂2⟩ := exists_mem_m11_apply_eq ha'b' ha'c' hb'c'
  let h := g₂ * g₁⁻¹
  have hhM : h ∈ CFSG.Open.M11 := CFSG.Open.M11.mul_mem hg₂M (CFSG.Open.M11.inv_mem hg₁M)
  have hha : h a = a' := by
    have hinv : g₁⁻¹ a = 0 := (Perm.inv_eq_iff_eq (f := g₁)).mpr hg₁0.symm
    simp only [h, Perm.mul_apply, hinv, hg₂0]
  have hhb : h b = b' := by
    have hinv : g₁⁻¹ b = 1 := (Perm.inv_eq_iff_eq (f := g₁)).mpr hg₁1.symm
    simp only [h, Perm.mul_apply, hinv, hg₂1]
  have hhc : h c = c' := by
    have hinv : g₁⁻¹ c = 2 := (Perm.inv_eq_iff_eq (f := g₁)).mpr hg₁2.symm
    simp only [h, Perm.mul_apply, hinv, hg₂2]
  have hconj_apply : ∀ x, (h * s * h⁻¹) (h x) = h (s x) := by
    intro x
    simp only [Perm.mul_apply]
    rw [Perm.inv_def, Equiv.symm_apply_apply]
  have hfix_a' : (h * s * h⁻¹) a' = a' := by
    have hh := hconj_apply a
    rw [hha, (hfixs a).mpr (Or.inl rfl), hha] at hh
    exact hh
  have hfix_b' : (h * s * h⁻¹) b' = b' := by
    have hh := hconj_apply b
    rw [hhb, (hfixs b).mpr (Or.inr (Or.inl rfl)), hhb] at hh
    exact hh
  have hfix_c' : (h * s * h⁻¹) c' = c' := by
    have hh := hconj_apply c
    rw [hhc, (hfixs c).mpr (Or.inr (Or.inr rfl)), hhc] at hh
    exact hh
  have hconj_mem : h * s * h⁻¹ ∈ m11Stab a' b' c' :=
    mem_m11Stab.mpr
      ⟨CFSG.Open.M11.mul_mem (CFSG.Open.M11.mul_mem hhM hs) (CFSG.Open.M11.inv_mem hhM),
        hfix_a', hfix_b', hfix_c'⟩
  have hconj2 : (h * s * h⁻¹) * (h * s * h⁻¹) = 1 := by
    calc (h * s * h⁻¹) * (h * s * h⁻¹) = h * (s * s) * h⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hconj_ne : h * s * h⁻¹ ≠ 1 := by
    intro hc
    apply hs1
    calc s = h⁻¹ * (h * s * h⁻¹) * h := by group
      _ = 1 := by rw [hc]; group
  obtain ⟨z, hz_mem, hz1, hz2, hzu, hzc⟩ :=
    exists_central_involution_m11Stab ha'b' ha'c' hb'c'
  have hz_eq : h * s * h⁻¹ = z := by
    rcases hzu _ hconj_mem hconj2 with h1 | h1
    · exact absurd h1 hconj_ne
    · exact h1
  have ht_mem : t ∈ m11Stab a' b' c' :=
    mem_m11Stab.mpr ⟨ht, (hfixt a').mpr (Or.inl rfl),
      (hfixt b').mpr (Or.inr (Or.inl rfl)), (hfixt c').mpr (Or.inr (Or.inr rfl))⟩
  have ht_eq : t = z := by
    rcases hzu _ ht_mem ht2 with h1 | h1
    · exact absurd h1 ht1
    · exact h1
  exact ⟨h, hhM, hz_eq.trans ht_eq.symm⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3Model

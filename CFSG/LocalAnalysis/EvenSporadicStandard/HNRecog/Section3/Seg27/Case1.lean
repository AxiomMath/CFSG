module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Tools
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Six
public import Mathlib.Data.Nat.Prime.Int

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

theorem seg27_eq_one_of_commute_five {g w : Equiv.Perm (Fin 8)} (hg : orderOf g = 5)
    (hcomm : w * g = g * w) (hfix : ∀ x, g x = x → w x = x) {c : Fin 8} (hc : g c ≠ c)
    (hwc : w c = c) : w = 1 := by
  apply Equiv.ext
  intro x
  change w x = x
  by_cases hx : g x = x
  · exact hfix x hx
  · obtain ⟨n, hn⟩ := seg27_exists_pow_eq_of_orderOf_five hg hc hx
    have hw : w * g ^ n = g ^ n * w := (show Commute w g from hcomm).pow_right n
    rw [← hn]
    calc w ((g ^ n) c) = (g ^ n) (w c) := by
          rw [← Equiv.Perm.mul_apply, hw, Equiv.Perm.mul_apply]
      _ = (g ^ n) c := by rw [hwc]

theorem seg27_conj_eq_inv_of_five {g t : Equiv.Perm (Fin 8)} (hg : orderOf g = 5)
    (ht : orderOf t = 2) (hn : t * g * t⁻¹ ∈ Subgroup.zpowers g)
    (hfix : ∀ x, g x = x → t x = x) {c : Fin 8} (hc : g c ≠ c) (htc : t c = c) :
    t * g * t⁻¹ = g⁻¹ := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hn
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht] at this
  have ht2' : t * t = 1 := by simpa [pow_two] using ht2
  have hsq : g = g ^ (m * m) := by
    have hgg : t * (t * g * t⁻¹) * t⁻¹ = g := by
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2'
      calc t * (t * g * t⁻¹) * t⁻¹ = (t * t) * g * (t⁻¹ * t⁻¹) := by group
        _ = g := by rw [htinv, ht2']; simp
    calc g = t * (t * g * t⁻¹) * t⁻¹ := hgg.symm
      _ = t * g ^ m * t⁻¹ := by rw [← hm]
      _ = (t * g * t⁻¹) ^ m := (conj_zpow (a := t) (b := g)).symm
      _ = (g ^ m) ^ m := by rw [hm]
      _ = g ^ (m * m) := by rw [zpow_mul]
  have hgm : g ^ (m * m - 1) = 1 := by
    rw [zpow_sub, ← hsq]
    simp
  have hdiv : (5 : ℤ) ∣ m * m - 1 := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := g) (i := m * m - 1)).mpr hgm
    simpa [hg] using this
  have hfac : m * m - 1 = (m - 1) * (m + 1) := by ring
  have hp : Prime (5 : ℤ) := (Nat.prime_iff_prime_int (p := 5)).mp Nat.prime_five
  rw [hfac] at hdiv
  rcases (hp.dvd_mul).mp hdiv with h1 | h1
  · exfalso
    have hm1 : g ^ m = g := by
      have h' : (orderOf g : ℤ) ∣ m - 1 := by simpa [hg] using h1
      have := (orderOf_dvd_sub_iff_zpow_eq_zpow (x := g) (a := m) (b := 1)).mp h'
      simpa using this
    have hconj : t * g * t⁻¹ = g := by rw [← hm, hm1]
    have hcomm : t * g = g * t := by
      have := congrArg (· * t) hconj
      simpa [mul_assoc] using this
    have ht1 : t = 1 := seg27_eq_one_of_commute_five hg hcomm hfix hc htc
    rw [ht1] at ht
    simp at ht
  · have hm4 : g ^ m = g⁻¹ := by
      have h' : (orderOf g : ℤ) ∣ m - (-1) := by
        rw [show m - (-1 : ℤ) = m + 1 by ring]
        simpa [hg] using h1
      have := (orderOf_dvd_sub_iff_zpow_eq_zpow (x := g) (a := m) (b := -1)).mp h'
      simpa using this
    rw [← hm, hm4]

theorem seg27_case1 {X₀ X₁ : Subgroup (Equiv.Perm (Fin 8))} {i j k : Fin 8} (hjk : j ≠ k)
    (h₀ : Seg27Six X₀ i j) (h₁ : Seg27Six X₁ i k) : ∃ g ∈ X₀ ⊓ X₁, orderOf g = 2 := by
  have hij : i ≠ j := h₀.ne
  have hik : i ≠ k := h₁.ne
  have hki : k ≠ i := hik.symm
  have hkj : k ≠ j := hjk.symm
  have hji : j ≠ i := hij.symm
  let H₁ : Subgroup (Equiv.Perm (Fin 8)) :=
    X₀ ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) k
  let H₂ : Subgroup (Equiv.Perm (Fin 8)) :=
    X₁ ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) j
  have hH₁card : Nat.card H₁ = 10 := h₀.card_stab k hki hkj
  have hH₂card : Nat.card H₂ = 10 := h₁.card_stab j hji hjk
  have hH₁le : H₁ ≤ seg27AltFix ({i, j, k} : Set (Fin 8)) := by
    intro x hx
    obtain ⟨hxX, hxstab⟩ := Subgroup.mem_inf.mp hx
    rw [seg27_mem_altFix]
    refine ⟨h₀.le_alt hxX, ?_⟩
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact h₀.fix_p x hxX
    · exact h₀.fix_q x hxX
    · simpa [Equiv.Perm.smul_def] using (MulAction.mem_stabilizer_iff.mp hxstab)
  have hH₂le : H₂ ≤ seg27AltFix ({i, j, k} : Set (Fin 8)) := by
    intro x hx
    obtain ⟨hxX, hxstab⟩ := Subgroup.mem_inf.mp hx
    rw [seg27_mem_altFix]
    refine ⟨h₁.le_alt hxX, ?_⟩
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact h₁.fix_p x hxX
    · simpa [Equiv.Perm.smul_def] using (MulAction.mem_stabilizer_iff.mp hxstab)
    · exact h₁.fix_q x hxX
  have hcard60 : Nat.card (seg27AltFix ({i, j, k} : Set (Fin 8))) = 60 :=
    seg27_card_altFix_three hij hik hjk
  let Z : Subgroup (Equiv.Perm (Fin 8)) := H₁ ⊓ H₂
  have hle := seg27_card_mul_card_le hH₁le hH₂le
  rw [hH₁card, hH₂card, hcard60] at hle
  change 10 * 10 ≤ 60 * Nat.card Z at hle
  have hge2 : 2 ≤ Nat.card Z := by omega
  have hdvd : Nat.card Z ∣ 10 := by
    have := Subgroup.card_dvd_of_le (H := Z) (K := H₁) inf_le_left
    rwa [hH₁card] at this
  by_cases heven : 2 ∣ Nat.card Z
  · obtain ⟨g, hg, hg2⟩ := seg27_exists_orderOf_two Z heven
    exact ⟨g, ⟨(Subgroup.mem_inf.mp hg.1).1, (Subgroup.mem_inf.mp hg.2).1⟩, hg2⟩
  · have hodd : Odd (Nat.card Z) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact heven
    have hcop : Nat.Coprime (Nat.card Z) 2 := Nat.coprime_two_right.mpr hodd
    have hdvd5 : Nat.card Z ∣ 5 := by
      apply hcop.dvd_of_dvd_mul_left
      simpa using hdvd
    have hcardZ : Nat.card Z = 5 := by
      have h15 := (Nat.dvd_prime Nat.prime_five).mp hdvd5
      omega
    obtain ⟨g, hg, hgord⟩ :=
      seg27_exists_orderOf_prime Z Nat.prime_five (by rw [hcardZ])
    have hgX₀ : g ∈ X₀ := (Subgroup.mem_inf.mp hg.1).1
    have hgX₁ : g ∈ X₁ := (Subgroup.mem_inf.mp hg.2).1
    have hgi : g i = i := h₀.fix_p g hgX₀
    have hgj : g j = j := h₀.fix_q g hgX₀
    have hgk : g k = k := h₁.fix_q g hgX₁
    have hgfixed : ∀ x, g x = x → x = i ∨ x = j ∨ x = k :=
      seg27_fixed_eq_of_orderOf_five hgord hij hik hjk hgi hgj hgk
    have hlt : ({i, j, k} : Finset (Fin 8)).card < (Finset.univ : Finset (Fin 8)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have := Finset.card_le_three (a := i) (b := j) (c := k)
      omega
    obtain ⟨c, -, hcnot⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card (s := ({i, j, k} : Finset (Fin 8)))
        (t := Finset.univ) hlt
    have hci : c ≠ i := fun h => hcnot (by simp [h])
    have hcj : c ≠ j := fun h => hcnot (by simp [h])
    have hck : c ≠ k := fun h => hcnot (by simp [h])
    have hgc : g c ≠ c := by
      intro h
      rcases hgfixed c h with rfl | rfl | rfl
      · exact hci rfl
      · exact hcj rfl
      · exact hck rfl
    obtain ⟨t, htX₀, htord, htk, htc⟩ := h₀.inv_fix2 k c
    obtain ⟨u, huX₁, huord, huj, huc⟩ := h₁.inv_fix2 j c
    have htH₁ : t ∈ H₁ :=
      Subgroup.mem_inf.mpr
        ⟨htX₀, MulAction.mem_stabilizer_iff.mpr (by simpa [Equiv.Perm.smul_def] using htk)⟩
    have huH₂ : u ∈ H₂ :=
      Subgroup.mem_inf.mpr
        ⟨huX₁, MulAction.mem_stabilizer_iff.mpr (by simpa [Equiv.Perm.smul_def] using huj)⟩
    have htfix : ∀ x, g x = x → t x = x := by
      intro x hx
      rcases hgfixed x hx with rfl | rfl | rfl
      · exact h₀.fix_p t htX₀
      · exact h₀.fix_q t htX₀
      · exact htk
    have hufix : ∀ x, g x = x → u x = x := by
      intro x hx
      rcases hgfixed x hx with rfl | rfl | rfl
      · exact h₁.fix_p u huX₁
      · exact huj
      · exact h₁.fix_q u huX₁
    have hcardH₁ : Nat.card H₁ = 2 * Nat.card Z := by rw [hH₁card, hcardZ]
    have hcardH₂ : Nat.card H₂ = 2 * Nat.card Z := by rw [hH₂card, hcardZ]
    have htconj : t * g * t⁻¹ ∈ Z :=
      seg27_conj_mem_of_card_eq_two_mul (X := Z) (S := H₁) inf_le_left hcardH₁ htH₁ hg
    have huconj : u * g * u⁻¹ ∈ Z :=
      seg27_conj_mem_of_card_eq_two_mul (X := Z) (S := H₂) inf_le_right hcardH₂ huH₂ hg
    have hZeq : Subgroup.zpowers g = Z := by
      apply Subgroup.eq_of_le_of_card_ge
      · exact Subgroup.zpowers_le_of_mem hg
      · rw [Nat.card_zpowers, hgord, hcardZ]
    have htn : t * g * t⁻¹ ∈ Subgroup.zpowers g := by
      rw [hZeq]; exact htconj
    have hun : u * g * u⁻¹ ∈ Subgroup.zpowers g := by
      rw [hZeq]; exact huconj
    have htinv : t * g * t⁻¹ = g⁻¹ :=
      seg27_conj_eq_inv_of_five hgord htord htn htfix hgc htc
    have huinv : u * g * u⁻¹ = g⁻¹ :=
      seg27_conj_eq_inv_of_five hgord huord hun hufix hgc huc
    have hwconj : (t * u) * g * (t * u)⁻¹ = g := by
      calc (t * u) * g * (t * u)⁻¹ = t * (u * g * u⁻¹) * t⁻¹ := by group
        _ = t * g⁻¹ * t⁻¹ := by rw [huinv]
        _ = (t * g * t⁻¹)⁻¹ := by group
        _ = (g⁻¹)⁻¹ := by rw [htinv]
        _ = g := by simp
    have hwcomm : (t * u) * g = g * (t * u) := by
      have := congrArg (· * (t * u)) hwconj
      simpa [mul_assoc] using this
    have hwfix : ∀ x, g x = x → (t * u) x = x := by
      intro x hx
      rw [Equiv.Perm.mul_apply, hufix x hx, htfix x hx]
    have hwc : (t * u) c = c := by rw [Equiv.Perm.mul_apply, huc, htc]
    have hw1 : t * u = 1 := seg27_eq_one_of_commute_five hgord hwcomm hwfix hgc hwc
    have htX₁ : t ∈ X₁ := by
      have htu' : t⁻¹ = u := inv_eq_of_mul_eq_one_right hw1
      have htu : t = u⁻¹ := by rw [← htu', inv_inv]
      rw [htu]
      exact X₁.inv_mem huX₁
    exact ⟨t, ⟨htX₀, htX₁⟩, htord⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3

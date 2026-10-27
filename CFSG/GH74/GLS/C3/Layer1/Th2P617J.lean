module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617H

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Th2

theorem IsRootFour.comm_swap {F : Subgroup (Perm (Fin 7))} {t : Perm (Fin 7)}
    (hdis : ∀ i, (∃ f ∈ F, f i ≠ i) → t i = i) : ∀ f ∈ F, f * t = t * f := by
  intro f hf
  have hd : f.Disjoint t := fun i => by
    by_cases hfi : f i = i
    · exact Or.inl hfi
    · exact Or.inr (hdis i ⟨f, hf, hfi⟩)
  exact hd.commute.eq

theorem IsRootFour.swap_eq_of_mem {F : Subgroup (Perm (Fin 7))} (hF : IsRootFour F)
    {t : Perm (Fin 7)} (ht : t.IsSwap) (hdis : ∀ i, (∃ f ∈ F, f i ≠ i) → t i = i)
    {σ : Perm (Fin 7)} (hσ : σ ∈ F ⊔ zpowers t) (hσs : σ.IsSwap) : σ = t := by
  classical
  have hcomm := IsRootFour.comm_swap hdis
  have ht2 : orderOf t = 2 := ht.orderOf
  obtain ⟨-, -, -, S, hS, hsupp⟩ := hF
  obtain ⟨f, hf, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun f hf s hs => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hs
      exact (Commute.zpow_right (show Commute f t from hcomm f hf) m).eq) hσ
  have hσ2 : (f * q).support.card = 2 := Equiv.Perm.card_support_eq_two.2 hσs
  have ht2c : t.support.card = 2 := Equiv.Perm.card_support_eq_two.2 ht
  rcases mem_zpowers_two ht2 hq with h0 | h0
  · exfalso
    subst h0
    rw [mul_one] at hσ2
    by_cases hf1 : f = 1
    · rw [hf1] at hσ2
      simp at hσ2
    · rw [hsupp f hf hf1, hS] at hσ2
      omega
  · subst h0
    by_cases hf1 : f = 1
    · rw [hf1, one_mul]
    · exfalso
      have hd : f.Disjoint q := fun i => by
        by_cases hfi : f i = i
        · exact Or.inl hfi
        · exact Or.inr (hdis i ⟨f, hf, hfi⟩)
      rw [hd.support_mul, hsupp f hf hf1] at hσ2
      have hdd : Disjoint f.support q.support := Equiv.Perm.disjoint_iff_disjoint_support.1 hd
      rw [hsupp f hf hf1] at hdd
      rw [Finset.card_union_of_disjoint hdd, hS, ht2c] at hσ2
      omega


theorem IsRootFour.centralizes_of_normalizes {F : Subgroup (Perm (Fin 7))} (hF : IsRootFour F)
    {t : Perm (Fin 7)} (ht : t.IsSwap) (hdis : ∀ i, (∃ f ∈ F, f i ≠ i) → t i = i)
    {g : Perm (Fin 7)} (hgN : ∀ w ∈ F ⊔ zpowers t, g * w * g⁻¹ ∈ F ⊔ zpowers t)
    {H : Subgroup (Perm (Fin 7))} (hHW : H ≤ F ⊔ zpowers t) (hH4 : Nat.card ↥H = 4) (htH : t ∉ H)
    (hgH : ∀ h ∈ H, g * h = h * g) : ∀ w ∈ F ⊔ zpowers t, g * w = w * g := by
  classical
  have ht2 : orderOf t = 2 := ht.orderOf
  have htW : t ∈ F ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hcomm := IsRootFour.comm_swap hdis
  have hgt : g * t = t * g := by
    have hsw : (g * t * g⁻¹).IsSwap := by
      obtain ⟨a, b, hab, rfl⟩ := ht
      rw [← Equiv.swap_apply_apply]
      exact ⟨g a, g b, fun h => hab (g.injective h), rfl⟩
    have := IsRootFour.swap_eq_of_mem hF ht hdis (hgN t htW) hsw
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [this]
  have hHt : ∀ h ∈ H, h * t = t * h := by
    intro h hh
    obtain ⟨f, hf, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun f hf s hs => by
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hs
        exact (Commute.zpow_right (show Commute f t from hcomm f hf) m).eq) (hHW hh)
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hq
    calc f * t ^ m * t = f * (t ^ m * t) := by rw [mul_assoc]
      _ = f * (t * t ^ m) := by rw [(Commute.zpow_left (Commute.refl t) m).eq]
      _ = (f * t) * t ^ m := by rw [mul_assoc]
      _ = (t * f) * t ^ m := by rw [hcomm f hf]
      _ = t * (f * t ^ m) := by rw [mul_assoc]
  have hcd : CommDisj H (zpowers t) := by
    refine ⟨fun h hh s hs => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hs
      exact (Commute.zpow_right (show Commute h t from hHt h hh) m).eq
    · refine eq_bot_iff.2 fun w hw => ?_
      rcases mem_zpowers_two ht2 hw.2 with h0 | h0
      · simp [h0]
      · exact absurd (h0 ▸ hw.1) htH
  have hcardHt : Nat.card ↥(H ⊔ zpowers t) = 8 := by
    rw [hcd.card_sup le_rfl le_rfl, hH4, Nat.card_zpowers, ht2]
  have hW8 : Nat.card ↥(F ⊔ zpowers t) = 8 := card_rootFour_sup_swap hF ht hdis
  have hHtW : H ⊔ zpowers t ≤ F ⊔ zpowers t := sup_le hHW (zpowers_le.2 htW)
  have hEq : H ⊔ zpowers t = F ⊔ zpowers t :=
    Subgroup.eq_of_le_of_card_ge hHtW (by rw [hcardHt, hW8])
  intro w hw
  rw [← hEq] at hw
  obtain ⟨h, hh, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute (fun h hh s hs => hcd.comm h hh s hs) hw
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hq
  have hgq : g * t ^ m = t ^ m * g := (Commute.zpow_right (show Commute g t from hgt) m).eq
  calc g * (h * t ^ m) = (g * h) * t ^ m := by rw [mul_assoc]
    _ = (h * g) * t ^ m := by rw [hgH h hh]
    _ = h * (g * t ^ m) := by rw [mul_assoc]
    _ = h * (t ^ m * g) := by rw [hgq]
    _ = (h * t ^ m) * g := by rw [mul_assoc]

theorem orderOf_dvd_four_of_eq_two_pow {σ : Perm (Fin 7)} {k : ℕ} (hσ : orderOf σ = 2 ^ k) :
    orderOf σ ∣ 4 := by
  classical
  rw [← Equiv.Perm.lcm_cycleType] at hσ ⊢
  refine Multiset.lcm_dvd.2 ?_
  intro ℓ hℓ
  have h1 : ℓ ∣ 2 ^ k := hσ ▸ Multiset.dvd_lcm hℓ
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : 2 ^ j ≤ 7 := by
    have h3 := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hℓ
    have h4 := Equiv.Perm.sum_cycleType_le σ
    simp only [Fintype.card_fin] at h4
    omega
  have hj : j ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases j <;> norm_num

end CFSG.GH74.GLS.Th2.Obs

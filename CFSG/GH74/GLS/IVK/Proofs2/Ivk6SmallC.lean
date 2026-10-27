module

public import CFSG.GH74.GLS.IVK.Proofs2.PglKCoatom
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6NI

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section PairFF

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem card_fixedSubgroup_outer_nine (hF : L2Field F) (h9 : Nat.card F = 9) (e : K ≃* L2 F)
    (N : L2Notation e) {y : MulAut K} (hy2 : y ^ 2 = 1) (hyD : y ∉ innDiagSub e) :
    Nat.card ↥(fixedSubgroup K y) = 24 := by
  obtain ⟨q₀, hq₀, hcard⟩ := card_fixedSubgroup_outer hF e N hy2 hyD
  have h3 : q₀ = 3 := by
    have h : q₀ ^ 2 = 3 ^ 2 := by rw [hq₀, h9]; norm_num
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h
  rw [hcard, h3]
  norm_num

theorem mul_mem_innDiagSub_of_outer_nine (hF : L2Field F) (h9 : Nat.card F = 9) (e : K ≃* L2 F)
    {f₁ f₂ : MulAut K} (hD1 : f₁ ∉ innDiagSub e) (hD2 : f₂ ∉ innDiagSub e) :
    f₁ * f₂ ∈ innDiagSub e := by
  obtain ⟨-, ⟨ε⟩, hn⟩ := ivk_1_2e F hF K e
  have hcardF : Nat.card (F ≃+* F) = 2 := by
    have h3 : Nat.card F = 3 ^ 2 := by rw [h9]; norm_num
    rw [← Nat.card_congr ε.toEquiv]
    exact hn 3 2 Nat.prime_three h3
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : F ≃+* F)).1 hcardF
  have hσ1 : fieldProj e f₁ = y := huniq _ (fun h => hD1 ((mem_innDiagSub_iff e f₁).2 h))
  have hσ2 : fieldProj e f₂ = y := huniq _ (fun h => hD2 ((mem_innDiagSub_iff e f₂).2 h))
  rw [mem_innDiagSub_iff, map_mul, hσ1, hσ2]
  have h2 : y ^ 2 = 1 := by
    have := pow_card_eq_one' (G := F ≃+* F) (x := y)
    rwa [hcardF] at this
  rwa [← pow_two]

theorem sup_fixed_eq_top_of_outer_outer (hF : L2Field F) (h9 : Nat.card F = 9) (e : K ≃* L2 F)
    (N : L2Notation e) {f₁ f₂ : MulAut K} (h1 : f₁ ^ 2 = 1) (h2 : f₂ ^ 2 = 1)
    (hD1 : f₁ ∉ innDiagSub e) (hD2 : f₂ ∉ innDiagSub e) (hne : f₁ ≠ f₂)
    (hcomm : f₁ * f₂ = f₂ * f₁) :
    fixedSubgroup K f₁ ⊔ fixedSubgroup K f₂ = ⊤ := by
  have hinj := conj_injective_of_L2 e
  have hC1 := card_fixedSubgroup_outer_nine hF h9 e N h1 hD1
  have hC2 := card_fixedSubgroup_outer_nine hF h9 e N h2 hD2
  have hK360 : Nat.card K = 360 := by
    rw [card_eq_of_L2Field e hF, h9]
    norm_num
  have hcoat : IsCoatom (fixedSubgroup K f₁) :=
    isCoatom_of_card_24 (isSimpleGroup_of_l2 hF e) (Or.inr hK360) _ hC1
  have hnle : ¬ fixedSubgroup K f₂ ≤ fixedSubgroup K f₁ := by
    intro hle
    have heq : fixedSubgroup K f₂ = fixedSubgroup K f₁ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hC1, hC2])
    have hzD : f₁ * f₂ ∈ innDiagSub e := mul_mem_innDiagSub_of_outer_nine hF h9 e hD1 hD2
    have hz1 : f₁ * f₂ ≠ 1 := by
      intro h
      apply hne
      have hf1 : f₁ * f₁ = 1 := by rw [← pow_two]; exact h1
      exact (mul_left_cancel (h.trans hf1.symm)).symm
    have hz2 : (f₁ * f₂) ^ 2 = 1 := by
      rw [pow_two]
      calc f₁ * f₂ * (f₁ * f₂) = f₁ * (f₂ * f₁) * f₂ := by group
        _ = f₁ * (f₁ * f₂) * f₂ := by rw [hcomm]
        _ = (f₁ * f₁) * (f₂ * f₂) := by group
        _ = 1 := by rw [← pow_two, ← pow_two, h1, h2, one_mul]
    have hzo : orderOf (f₁ * f₂) = 2 := orderOf_eq_prime hz2 hz1
    have hCz : fixedSubgroup K f₁ ≤ fixedSubgroup K (f₁ * f₂) := by
      intro c hc
      have hc1 : f₁ c = c := hc
      have hc2' : c ∈ fixedSubgroup K f₂ := by rw [heq]; exact hc
      have hc2 : f₂ c = c := hc2'
      show (f₁ * f₂) c = c
      show f₁ (f₂ c) = c
      rw [hc2, hc1]
    have hdvd := Subgroup.card_dvd_of_le hCz
    rw [hC1] at hdvd
    obtain ⟨dI, dD, hdI, hdD, hne', hI, hD⟩ := card_fixedSubgroup_inndiag hF e
    by_cases hzI : f₁ * f₂ ∈ innAut K
    · obtain ⟨u, hu⟩ := hzI
      have huo : orderOf u = 2 := by
        have := orderOf_injective (MulAut.conj : K →* MulAut K) hinj u
        rw [hu] at this
        exact this.symm.trans hzo
      have := hI u huo
      rw [hu] at this
      rw [this] at hdvd
      rcases hdI with h | h <;> omega
    · have := hD _ hzD hzI hzo
      rw [this] at hdvd
      rcases hdD with h | h <;> omega
  exact hcoat.2 _ (lt_of_le_of_ne le_sup_left fun h => hnle (le_sup_right.trans (le_of_eq h.symm)))

end PairFF

end CFSG.GH74.GLS.IVK.Proofs2

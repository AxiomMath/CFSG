module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Orders
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CaseTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.PSL2ReflectedTorusCard

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.GorensteinWalter

theorem psl2_torus_of_involution {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) {t : PSL2 K} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ c : PSL2 K, t ∈ Subgroup.zpowers c ∧ Even (orderOf c) ∧
      (orderOf c = (Nat.card K - 1) / 2 ∨ orderOf c = (Nat.card K + 1) / 2) ∧
      ∀ s : PSL2 K, s ^ 2 = 1 → s ≠ 1 → s ≠ t → s * t = t * s → s * c * s⁻¹ = c⁻¹ := by
  classical
  obtain ⟨T, w, hTc, htT, hw, hwT, hwinv, hC, hTeven, hTcard⟩ :=
    psl2_reflected_torus_card hK (t := t) ⟨ht1, ht2⟩
  obtain ⟨⟨c, hcT⟩, hgen⟩ := hTc.exists_generator
  have hcord : orderOf c = Nat.card T := by
    rw [← Subgroup.orderOf_mk c hcT, orderOf_eq_card_of_forall_mem_zpowers hgen]
  have hTz : ∀ x ∈ T, x ∈ Subgroup.zpowers c := by
    intro x hx
    obtain ⟨k, hk⟩ := hgen ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hTc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hww : w * w = 1 := by rw [← pow_two]; exact hw.2
  refine ⟨c, hTz t htT, hcord ▸ hTeven, hcord ▸ hTcard, ?_⟩
  intro s hs2 hs1 hst hsc
  have hsC : s ∈ T ⊔ Subgroup.zpowers w := by
    rw [← hC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hsc
  have hsT : s ∉ T := by
    intro hsT
    apply hst
    have := eq_of_sq_eq_one_of_isCyclic (C := T) (u := ⟨s, hsT⟩) (w := ⟨t, htT⟩)
      (Subtype.ext (by simpa using hs2)) (Subtype.ext (by simpa using ht2))
      (fun h => hs1 (congrArg Subtype.val h)) (fun h => ht1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this
  obtain ⟨-, hinv⟩ := inverts_of_mem_sup_not_mem hTcomm hww hwinv hsC hsT
  exact hinv c hcT

theorem subfield_order_absurd {q a n : ℕ} (hq : 11 ≤ q) (ha : a ^ 2 ≤ q) (hn : q ≤ 2 * n + 1)
    (hna : n ≤ a + 1) : False := by
  have h1 : q ≤ 2 * a + 3 := by omega
  have h2 : 4 ≤ a := by omega
  nlinarith

theorem pow_two_mul_le_of_dvd {p f k : ℕ} (hp : 1 ≤ p) (hf : f ≠ 0) (hkf : k ∣ f)
    (hkf' : k ≠ f) : (p ^ k) ^ 2 ≤ p ^ f := by
  obtain ⟨d, rfl⟩ := hkf
  have hd0 : d ≠ 0 := by rintro rfl; simp at hf
  have hd1 : d ≠ 1 := by rintro rfl; simp at hkf'
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hp (Nat.mul_le_mul_left k (by omega))

theorem case_one_psl2 {K : Type} [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) (hK : IsOddPrimePower (Nat.card K)) (hq : 11 ≤ Nat.card K)
    {t₁ t₂ : PSL2 K} (h₁ : t₁ ^ 2 = 1) (h₂ : t₂ ^ 2 = 1) (h₁' : t₁ ≠ 1) (h₂' : t₂ ≠ 1)
    (hne : t₁ ≠ t₂) (hc : t₁ * t₂ = t₂ * t₁) (H : Subgroup (PSL2 K))
    (hP₁ : ∀ y, t₁ ∈ Subgroup.zpowers y → y ∈ H) (hP₂ : ∀ y, t₂ ∈ Subgroup.zpowers y → y ∈ H) :
    H = ⊤ := by
  classical
  obtain ⟨c₁, ht₁c, hc₁even, hc₁ord, hinv₁⟩ := psl2_torus_of_involution hK h₁ h₁'
  obtain ⟨c₂, ht₂c, hc₂even, hc₂ord, -⟩ := psl2_torus_of_involution hK h₂ h₂'
  have hqodd : Odd (Nat.card K) := odd_card_of_isOddPrimePower hK
  have hn₁ : 6 ≤ orderOf c₁ := by
    obtain ⟨k, hk⟩ := hqodd
    obtain ⟨j, hj⟩ := hc₁even
    rcases hc₁ord with h | h <;> omega
  have hn₂ : 6 ≤ orderOf c₂ := by
    obtain ⟨k, hk⟩ := hqodd
    obtain ⟨j, hj⟩ := hc₂even
    rcases hc₂ord with h | h <;> omega
  have hqn : Nat.card K ≤ 2 * orderOf c₁ + 1 := by
    obtain ⟨k, hk⟩ := hqodd
    rcases hc₁ord with h | h <;> omega
  have hc₁H := hP₁ c₁ ht₁c
  have hc₂H := hP₂ c₂ ht₂c
  have ht₂H := hP₂ t₂ (Subgroup.mem_zpowers t₂)
  have hinv : t₂ * c₁ * t₂⁻¹ = c₁⁻¹ := hinv₁ t₂ h₂ h₂' (Ne.symm hne) hc.symm
  have hnc : t₂ * c₁ ≠ c₁ * t₂ := by
    intro h
    have h1 : c₁ = c₁⁻¹ := by rw [← hinv, h]; group
    have hc2 : c₁ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel c₁
    have := orderOf_le_of_pow_eq_one two_pos hc2
    omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hKcard
    omega
  have hpn : Nat.Coprime p (orderOf c₁) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hdvd
    have hpq : p ∣ Nat.card K := by rw [hKcard]; exact dvd_pow_self p hf0
    obtain ⟨k, hk⟩ := hqodd
    have h2 : p ∣ 2 * orderOf c₁ := Dvd.dvd.mul_left hdvd 2
    rcases hc₁ord with h | h
    · have h3 : 2 * orderOf c₁ + 1 = Nat.card K := by omega
      have h4 : p ∣ 1 := by
        have := (Nat.dvd_add_right h2).mp (h3 ▸ hpq)
        exact this
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp h4)
    · have h3 : 2 * orderOf c₁ = Nat.card K + 1 := by omega
      have h4 : p ∣ 1 := (Nat.dvd_add_right hpq).mp (h3 ▸ h2)
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp h4)
  set x₁ : H := ⟨c₁, hc₁H⟩ with hx₁def
  set x₂ : H := ⟨c₂, hc₂H⟩ with hx₂def
  set s : H := ⟨t₂, ht₂H⟩ with hsdef
  have hx₁ : orderOf x₁ = orderOf c₁ := Subgroup.orderOf_mk c₁ hc₁H
  have hx₂ : orderOf x₂ = orderOf c₂ := Subgroup.orderOf_mk c₂ hc₂H
  have hncH : s * x₁ ≠ x₁ * s := fun h => hnc (congrArg Subtype.val h)
  have hinvH : s * x₁ * s⁻¹ = x₁⁻¹ := Subtype.ext hinv
  have hbound : ∀ a : ℕ, (a ^ 2 ≤ Nat.card K) → orderOf x₁ ≤ a + 1 → False := by
    intro a ha hle
    exact subfield_order_absurd hq ha hqn (hx₁ ▸ hle)
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hKcard H with
    hEA | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨eD⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m', r, -, -, N, Cc, hNn, hNea, -, hCc, -, -, hsup⟩ | ⟨k, hk0, hkf, ⟨eL⟩⟩ |
      ⟨k, hk0, hkf, ⟨eG⟩⟩
  · exact absurd (hEA.toIsMulCommutative.is_comm.comm s x₁) hncH
  · exact absurd (hcyc.commGroup.mul_comm s x₁) hncH
  ·
    exfalso
    have h12 : x₁ * x₂ = x₂ * x₁ :=
      commute_of_equiv_dihedral eD (by rw [hx₁]; omega) (by rw [hx₂]; omega)
    have h12' : c₁ * c₂ = c₂ * c₁ := congrArg Subtype.val h12
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht₂c
    apply hnc
    rw [← hk]
    exact ((Commute.zpow_left h12'.symm k).eq)
  · exfalso
    rcases orderOf_dvd_of_equiv_alternating_four eA4 x₁ with h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  · exfalso
    rcases orderOf_dvd_of_equiv_perm_four eS4 x₁ with h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  · exfalso
    rcases orderOf_dvd_of_equiv_alternating_five eA5 x₁ with h | h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    exfalso
    have hN : ∀ x ∈ N, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
    have h1 := orderOf_dvd_of_pow_eq_one (pow_eq_one_of_inverted_of_sup N Cc hN hCc hsup hinvH)
    rw [hx₁] at h1
    have h2 : orderOf c₁ ∣ 2 := (Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_comm.mp hpn) h1)
    have := Nat.le_of_dvd two_pos h2
    omega
  ·
    have hGF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
    by_cases hkf' : k = f
    · subst hkf'
      apply Subgroup.eq_top_of_card_eq
      have hGFodd : IsOddPrimePower (Nat.card (GaloisField p k)) := hGF ▸ hKcard ▸ hK
      rw [Nat.card_congr eL.toEquiv, psl2_card_formula (GaloisField p k) hGFodd,
        psl2_card_formula K hK, hGF, hKcard]
    · exfalso
      apply hbound (p ^ k) (hKcard ▸ pow_two_mul_le_of_dvd hp.out.one_lt.le hf0 hkf hkf')
      rw [← MulEquiv.orderOf_eq eL x₁, ← hGF]
      exact psl2_orderOf_le _ _
  ·
    exfalso
    have hGF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
    have hkf2 : k ∣ f := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hkf
    have hkf' : k ≠ f := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hkf
      omega
    apply hbound (p ^ k) (hKcard ▸ pow_two_mul_le_of_dvd hp.out.one_lt.le hf0 hkf2 hkf')
    rw [← MulEquiv.orderOf_eq eG x₁, ← hGF]
    exact pgl2_orderOf_le _ _

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

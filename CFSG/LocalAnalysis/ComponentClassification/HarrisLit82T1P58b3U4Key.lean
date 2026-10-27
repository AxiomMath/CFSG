module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BX

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open scoped MatrixGroups

namespace P58b3

theorem false_of_two_sl_central {X : Type} [Group X] [Finite X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) {C J : Subgroup X} (ρ₁ ρ₂ : SL(2, K) →* X)
    (hρ₁ : Function.Injective ρ₁) (hρ₂ : Function.Injective ρ₂)
    (hR₁ : ρ₁.range ≤ C) (hR₂ : ρ₂.range ≤ C)
    (hN₁ : (ρ₁.range.subgroupOf C).Normal) (hN₂ : (ρ₂.range.subgroupOf C).Normal)
    (hcomm : ∀ A B, ρ₁ A * ρ₂ B = ρ₂ B * ρ₁ A)
    (hinf₁ : ∀ A B, ρ₁ A = ρ₂ B → A = 1 ∨ A = -1) (hinf₂ : ∀ A B, ρ₁ A = ρ₂ B → B = 1 ∨ B = -1)
    (hdec : ∀ x ∈ C, x ^ 3 = 1 → ∃ A B, x = ρ₁ A * ρ₂ B)
    (hZ₁ : ∀ x ∈ C, ρ₁ (-1) * x = x * ρ₁ (-1)) (hZ₂ : ∀ x ∈ C, ρ₂ (-1) * x = x * ρ₂ (-1))
    (hJC : J ≤ C) (hJs : (J.subgroupOf C).IsSubnormal)
    (hJiso : Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* PSL(2, ZMod 3)) ∨
      Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* SL(2, ZMod 3)))
    {c : X} (hcJ : c ∈ J) (hcZ : ∀ y ∈ J, c * y = y * c) (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hc₁ : c ≠ ρ₁ (-1)) (hc₂ : c ≠ ρ₂ (-1)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoddK : Odd (Nat.card K) := by rw [hK]; decide
  have hodd3 : Odd (Nat.card (ZMod 3)) := by rw [Nat.card_zmod]; decide
  have hneg : (-1 : SL(2, K)) ≠ 1 := CFSG.ClassicalInvolution.sl2_neg_one_ne_one hoddK
  have hneg3 : (-1 : SL(2, K)) ^ 3 = -1 := Odd.neg_one_pow (by decide)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 3 (three_dvd_card_of_coreQuot hJiso)
  have hx3 : ((x : X)) ^ 3 = 1 := by
    rw [← SubgroupClass.coe_pow, ← hx, pow_orderOf_eq_one, OneMemClass.coe_one]
  have hx1 : (x : X) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  obtain ⟨A, B, hAB⟩ := hdec _ (hJC x.2) hx3
  have hpow : ∀ n : ℕ, (ρ₁ A * ρ₂ B) ^ n = ρ₁ (A ^ n) * ρ₂ (B ^ n) := by
    intro n
    rw [(Commute.mul_pow (hcomm A B) n), map_pow, map_pow]
  have h3 : ρ₁ (A ^ 3) = ρ₂ ((B ^ 3)⁻¹) := by
    have h := hpow 3
    rw [← hAB, hx3, eq_comm, mul_eq_one_iff_eq_inv, ← map_inv] at h
    exact h
  have hA3 := hinf₁ _ _ h3
  have hB3 : B ^ 3 = 1 ∨ B ^ 3 = -1 := by
    rcases hinf₂ _ _ h3 with h | h
    · left
      rw [inv_eq_one] at h
      exact h
    · right
      rw [inv_eq_iff_eq_inv] at h
      rw [h]
      exact inv_eq_of_mul_eq_one_right (by rw [neg_one_mul, neg_neg])
  have hk2 : ∀ k₀ : SL(2, K), k₀ ^ 4 = 1 → k₀ ^ 2 ≠ 1 → k₀ ^ 2 = -1 := by
    intro k₀ h4 h2
    refine (CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hoddK _).mp
      (orderOf_eq_prime ?_ h2)
    rw [← pow_mul]
    exact h4
  have hcubeR : ∀ (ρ : SL(2, K) →* X) (D : SL(2, K)), D ^ 3 = 1 ∨ D ^ 3 = -1 →
      ρ D ^ 3 = 1 ∨ ρ D ^ 3 = ρ (-1) := by
    intro ρ D hD
    rcases hD with h | h
    · left
      rw [← map_pow, h, map_one]
    · right
      rw [← map_pow, h]
  have hu : ∃ u, (u = ρ₁ (-1) ∨ u = ρ₂ (-1)) ∧ u ∈ J := by
    by_cases hA : A = 1 ∨ A = -1
    · have hB : ¬ (B = 1 ∨ B = -1) := by
        intro hB
        apply hx1
        have hsq : ((x : X)) ^ 2 = 1 := by
          rw [hAB, hpow 2]
          have e1 : A ^ 2 = 1 := by
            rcases hA with rfl | rfl
            · exact one_pow 2
            · rw [pow_two, neg_one_mul, neg_neg]
          have e2 : B ^ 2 = 1 := by
            rcases hB with rfl | rfl
            · exact one_pow 2
            · rw [pow_two, neg_one_mul, neg_neg]
          rw [e1, e2, map_one, map_one, one_mul]
        calc (x : X) = (x : X) ^ 3 * ((x : X) ^ 2)⁻¹ := by group
          _ = 1 := by rw [hx3, hsq, inv_one, one_mul]
      push Not at hB
      obtain ⟨k, ⟨hkJ, k₀, rfl⟩, hk4, hk2'⟩ := exists_mem_inf_of_noncentral hK ρ₂ hρ₂ hR₂ hN₂
        hJC hJs x.2 hx3 (a := ρ₂ B) (y := ρ₁ A) ⟨B, rfl⟩
        (fun r ⟨B', hB'⟩ => by rw [← hB']; exact (hcomm A B').symm)
        (by rw [hAB, hcomm]) (hcubeR ρ₂ B hB3)
        (fun h => hB.1 (hρ₂ (h.trans (map_one ρ₂).symm)))
        (fun h => hB.2 (hρ₂ h))
      refine ⟨_, Or.inr rfl, ?_⟩
      have h4 : k₀ ^ 4 = 1 := hρ₂ (by rw [map_pow, hk4, map_one])
      have h2 : k₀ ^ 2 ≠ 1 := fun h => hk2' (by rw [← map_pow, h, map_one])
      rw [← hk2 k₀ h4 h2, map_pow]
      exact pow_mem hkJ 2
    · push Not at hA
      obtain ⟨k, ⟨hkJ, k₀, rfl⟩, hk4, hk2'⟩ := exists_mem_inf_of_noncentral hK ρ₁ hρ₁ hR₁ hN₁
        hJC hJs x.2 hx3 (a := ρ₁ A) (y := ρ₂ B) ⟨A, rfl⟩
        (fun r ⟨A', hA'⟩ => by rw [← hA']; exact hcomm A' B) hAB (hcubeR ρ₁ A hA3)
        (fun h => hA.1 (hρ₁ (h.trans (map_one ρ₁).symm)))
        (fun h => hA.2 (hρ₁ h))
      refine ⟨_, Or.inl rfl, ?_⟩
      have h4 : k₀ ^ 4 = 1 := hρ₁ (by rw [map_pow, hk4, map_one])
      have h2 : k₀ ^ 2 ≠ 1 := fun h => hk2' (by rw [← map_pow, h, map_one])
      rw [← hk2 k₀ h4 h2, map_pow]
      exact pow_mem hkJ 2
  obtain ⟨u, hu12, huJ⟩ := hu
  have hu2 : u * u = 1 := by
    rcases hu12 with rfl | rfl <;> rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hu1 : u ≠ 1 := by
    rcases hu12 with rfl | rfl
    · exact fun h => hneg (hρ₁ (h.trans (map_one ρ₁).symm))
    · exact fun h => hneg (hρ₂ (h.trans (map_one ρ₂).symm))
  have hcu : c ≠ u := by
    rcases hu12 with rfl | rfl
    · exact hc₁
    · exact hc₂
  have huZJ : ∀ y ∈ J, u * y = y * u := by
    intro y hy
    rcases hu12 with rfl | rfl
    · exact hZ₁ y (hJC hy)
    · exact hZ₂ y (hJC hy)
  set O := pPrimeCore 2 ↥J with hO
  have hOodd : Odd (Nat.card O) := F3L57.odd_card_pPrimeCore ↥J
  have hinv : ∀ w : ↥J, w * w = 1 → w ∈ O → w = 1 := fun w hw hwO =>
    F3L57.eq_one_of_pow_two_pow_of_mem (k := 1) hOodd hwO (by rw [pow_one, pow_two, hw])
  set cJ : ↥J := ⟨c, hcJ⟩ with hcJdef
  set uJ : ↥J := ⟨u, huJ⟩ with huJdef
  have hcJ2 : cJ * cJ = 1 := Subtype.ext hc2
  have huJ2 : uJ * uJ = 1 := Subtype.ext hu2
  have hcZ' : ∀ y : ↥J, cJ * y = y * cJ := fun y => Subtype.ext (hcZ y y.2)
  have huZ' : ∀ y : ↥J, uJ * y = y * uJ := fun y => Subtype.ext (huZJ y y.2)
  have hπc : (QuotientGroup.mk cJ : ↥J ⧸ O) ≠ 1 := by
    intro h
    exact hc1 (congrArg Subtype.val (hinv cJ hcJ2 ((QuotientGroup.eq_one_iff _).mp h)))
  have hπu : (QuotientGroup.mk uJ : ↥J ⧸ O) ≠ 1 := by
    intro h
    exact hu1 (congrArg Subtype.val (hinv uJ huJ2 ((QuotientGroup.eq_one_iff _).mp h)))
  have hπcu : (QuotientGroup.mk cJ : ↥J ⧸ O) ≠ QuotientGroup.mk uJ := by
    intro h
    have hw : cJ * uJ⁻¹ ∈ O := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h,
        mul_inv_cancel]
    have hw2 : (cJ * uJ⁻¹) * (cJ * uJ⁻¹) = 1 := by
      have hui : uJ⁻¹ = uJ := inv_eq_of_mul_eq_one_right huJ2
      rw [hui, mul_assoc, ← mul_assoc uJ, huZ' cJ, mul_assoc, huJ2, mul_one, hcJ2]
    have h1 := hinv _ hw2 hw
    rw [mul_inv_eq_one] at h1
    exact hcu (congrArg Subtype.val h1)
  have hπZ : ∀ w : ↥J, (∀ y : ↥J, w * y = y * w) →
      (QuotientGroup.mk w : ↥J ⧸ O) ∈ center (↥J ⧸ O) := by
    intro w hw
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hw y]
  rcases hJiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  ·
    have hZc : e (QuotientGroup.mk cJ) ∈ center PSL(2, ZMod 3) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, mem_center_iff.mp (hπZ cJ hcZ') g]
    exact hπc (e.injective ((F3L221.eq_one_of_mem_center_psl23 hZc).trans (map_one e).symm))
  ·
    have hneg1 : ∀ w : ↥J ⧸ O, w ≠ 1 → w * w = 1 → e w = -1 := by
      intro w hw1 hw2
      refine (CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hodd3 _).mp ?_
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two, hw2]) hw1
    have h1 := hneg1 _ hπc (by rw [← QuotientGroup.mk_mul, hcJ2, QuotientGroup.mk_one])
    have h2 := hneg1 _ hπu (by rw [← QuotientGroup.mk_mul, huJ2, QuotientGroup.mk_one])
    exact hπcu (e.injective (h1.trans h2.symm))

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1

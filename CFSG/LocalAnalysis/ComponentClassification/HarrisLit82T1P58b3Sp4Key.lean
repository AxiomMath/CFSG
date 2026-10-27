module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73C
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L221Diag
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QRed
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L57
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open scoped MatrixGroups

namespace P58b3

theorem three_dvd_card_of_isSolvableTwoComponentIn {X : Type} [Group X] [Finite X]
    {J C : Subgroup X} (hJ : IsSolvableTwoComponentIn J C) : 3 ∣ Nat.card J := by
  have hodd : Odd (Nat.card (ZMod 3)) := by rw [Nat.card_zmod]; decide
  have hq : 3 ∣ Nat.card (↥J ⧸ pPrimeCore 2 ↥J) := by
    rcases hJ.2.2.2 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv]
      have h := card_eq_card_quotient_mul_card_subgroup (center SL(2, ZMod 3))
      rw [P51Q.card_sl23, CFSG.ClassicalInvolution.sl2_natCard_center hodd] at h
      change 3 ∣ Nat.card (SL(2, ZMod 3) ⧸ center SL(2, ZMod 3))
      omega
    · rw [Nat.card_congr e.toEquiv, P51Q.card_sl23]
      norm_num
  rw [card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J)]
  exact Dvd.dvd.mul_right hq _

theorem false_of_two_sl {X : Type} [Group X] [Finite X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) {C J : Subgroup X} (ρ₁ ρ₂ : SL(2, K) →* X)
    (hρ₁ : Function.Injective ρ₁) (hρ₂ : Function.Injective ρ₂)
    (hR₁ : ρ₁.range ≤ C) (hR₂ : ρ₂.range ≤ C)
    (hN₁ : (ρ₁.range.subgroupOf C).Normal) (hN₂ : (ρ₂.range.subgroupOf C).Normal)
    (hcomm : ∀ A B, ρ₁ A * ρ₂ B = ρ₂ B * ρ₁ A) (hinf : ∀ A B, ρ₁ A = ρ₂ B → A = 1)
    (hdec : ∀ x ∈ C, x ^ 3 = 1 → ∃ A B, x = ρ₁ A * ρ₂ B)
    (hZ₁ : ∀ x ∈ C, ρ₁ (-1) * x = x * ρ₁ (-1)) (hZ₂ : ∀ x ∈ C, ρ₂ (-1) * x = x * ρ₂ (-1))
    (hJ : IsSolvableTwoComponentIn J C) (hcJ : ρ₁ (-1) * ρ₂ (-1) ∈ J) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoddK : Odd (Nat.card K) := by rw [hK]; decide
  have hodd3 : Odd (Nat.card (ZMod 3)) := by rw [Nat.card_zmod]; decide
  have hneg : (-1 : SL(2, K)) ≠ 1 := CFSG.ClassicalInvolution.sl2_neg_one_ne_one hoddK
  have hJ3 := three_dvd_card_of_isSolvableTwoComponentIn hJ
  obtain ⟨hJC, hJs, -, hJiso⟩ := hJ
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 3 hJ3
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
  have hA3 : A ^ 3 = 1 := by
    have h := hpow 3
    rw [← hAB, hx3, eq_comm, mul_eq_one_iff_eq_inv, ← map_inv] at h
    exact hinf _ _ h
  have hB3 : B ^ 3 = 1 := by
    have h := hpow 3
    rw [← hAB, hx3, hA3, map_one, one_mul] at h
    exact hρ₂ (h.symm.trans (map_one ρ₂).symm)
  have hk2 : ∀ k₀ : SL(2, K), k₀ ^ 4 = 1 → k₀ ^ 2 ≠ 1 → k₀ ^ 2 = -1 := by
    intro k₀ h4 h2
    refine (CFSG.ClassicalInvolution.sl2_orderOf_eq_two_iff hoddK _).mp
      (orderOf_eq_prime ?_ h2)
    rw [← pow_mul]
    exact h4
  have hcube : ∀ g : SL(2, K), g ^ 3 = 1 → g ≠ -1 := by
    rintro g h3 rfl
    apply hneg
    have h : (-1 : SL(2, K)) ^ 3 = -1 := Odd.neg_one_pow (by decide)
    rw [← h, h3]
  have hu : ∃ u, (u = ρ₁ (-1) ∨ u = ρ₂ (-1)) ∧ u ∈ J := by
    by_cases hA1 : A = 1
    · have hB1 : B ≠ 1 := by
        rintro rfl
        rw [hA1, map_one, map_one, one_mul] at hAB
        exact hx1 hAB
      obtain ⟨k, ⟨hkJ, k₀, rfl⟩, hk4, hk2'⟩ := exists_mem_inf_of_noncentral hK ρ₂ hρ₂ hR₂ hN₂
        hJC hJs x.2 hx3 (a := ρ₂ B) (y := 1) ⟨B, rfl⟩ (fun r _ => by rw [mul_one, one_mul])
        (by rw [hAB, hA1, map_one, one_mul, mul_one])
        (Or.inl (by rw [← map_pow, hB3, map_one]))
        (fun h => hB1 (hρ₂ (h.trans (map_one ρ₂).symm)))
        (fun h => hcube B hB3 (hρ₂ h))
      refine ⟨_, Or.inr rfl, ?_⟩
      have h4 : k₀ ^ 4 = 1 := hρ₂ (by rw [map_pow, hk4, map_one])
      have h2 : k₀ ^ 2 ≠ 1 := fun h => hk2' (by rw [← map_pow, h, map_one])
      rw [← hk2 k₀ h4 h2, map_pow]
      exact pow_mem hkJ 2
    · obtain ⟨k, ⟨hkJ, k₀, rfl⟩, hk4, hk2'⟩ := exists_mem_inf_of_noncentral hK ρ₁ hρ₁ hR₁ hN₁
        hJC hJs x.2 hx3 (a := ρ₁ A) (y := ρ₂ B) ⟨A, rfl⟩
        (fun r ⟨A', hA'⟩ => by rw [← hA']; exact hcomm A' B) hAB
        (Or.inl (by rw [← map_pow, hA3, map_one]))
        (fun h => hA1 (hρ₁ (h.trans (map_one ρ₁).symm)))
        (fun h => hcube A hA3 (hρ₁ h))
      refine ⟨_, Or.inl rfl, ?_⟩
      have h4 : k₀ ^ 4 = 1 := hρ₁ (by rw [map_pow, hk4, map_one])
      have h2 : k₀ ^ 2 ≠ 1 := fun h => hk2' (by rw [← map_pow, h, map_one])
      rw [← hk2 k₀ h4 h2, map_pow]
      exact pow_mem hkJ 2
  obtain ⟨u, hu12, huJ⟩ := hu
  set c := ρ₁ (-1) * ρ₂ (-1) with hc
  have hn1 : ρ₁ (-1) * ρ₁ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hn2 : ρ₂ (-1) * ρ₂ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hcen : ∀ w, (w = ρ₁ (-1) ∨ w = ρ₂ (-1) ∨ w = c) → ∀ y ∈ J, w * y = y * w := by
    rintro w (rfl | rfl | rfl) y hy
    · exact hZ₁ y (hJC hy)
    · exact hZ₂ y (hJC hy)
    · rw [hc, mul_assoc, hZ₂ y (hJC hy), ← mul_assoc, hZ₁ y (hJC hy), mul_assoc]
  have hc2 : c * c = 1 := by
    rw [hc, mul_assoc, ← mul_assoc (ρ₂ (-1)), ← hcomm, mul_assoc, hn2, mul_one, hn1]
  have hu2 : u * u = 1 := by rcases hu12 with rfl | rfl <;> assumption
  have hcu : c ≠ u := by
    rcases hu12 with rfl | rfl
    · intro h
      have h' : ρ₂ (-1) = 1 := by
        calc ρ₂ (-1) = (ρ₁ (-1))⁻¹ * c := by rw [hc, inv_mul_cancel_left]
          _ = 1 := by rw [h, inv_mul_cancel]
      exact hneg (hρ₂ (h'.trans (map_one ρ₂).symm))
    · intro h
      have h' : ρ₁ (-1) = 1 := by
        calc ρ₁ (-1) = c * (ρ₂ (-1))⁻¹ := by rw [hc, mul_inv_cancel_right]
          _ = 1 := by rw [h, mul_inv_cancel]
      exact hneg (hρ₁ (h'.trans (map_one ρ₁).symm))
  have hc1 : c ≠ 1 := by
    intro h
    have h' : ρ₁ (-1) = ρ₂ (-1) := by
      calc ρ₁ (-1) = c * (ρ₂ (-1))⁻¹ := by rw [hc, mul_inv_cancel_right]
        _ = (ρ₂ (-1))⁻¹ := by rw [h, one_mul]
        _ = ρ₂ (-1) := inv_eq_of_mul_eq_one_right hn2
    exact hneg (hinf _ _ h')
  set O := pPrimeCore 2 ↥J with hO
  have hOodd : Odd (Nat.card O) := F3L57.odd_card_pPrimeCore ↥J
  have hinv : ∀ w : ↥J, w * w = 1 → w ∈ O → w = 1 := fun w hw hwO =>
    F3L57.eq_one_of_pow_two_pow_of_mem (k := 1) hOodd hwO (by rw [pow_one, pow_two, hw])
  set cJ : ↥J := ⟨c, hcJ⟩ with hcJdef
  set uJ : ↥J := ⟨u, huJ⟩ with huJdef
  have hcJ2 : cJ * cJ = 1 := Subtype.ext hc2
  have huJ2 : uJ * uJ = 1 := Subtype.ext hu2
  have hcZ : ∀ y : ↥J, cJ * y = y * cJ := fun y =>
    Subtype.ext (hcen c (Or.inr (Or.inr rfl)) y y.2)
  have huZ : ∀ y : ↥J, uJ * y = y * uJ := fun y =>
    Subtype.ext (hcen u (hu12.elim Or.inl (fun h => Or.inr (Or.inl h))) y y.2)
  have hπc : (QuotientGroup.mk cJ : ↥J ⧸ O) ≠ 1 := by
    intro h
    exact hc1 (congrArg Subtype.val (hinv cJ hcJ2 ((QuotientGroup.eq_one_iff _).mp h)))
  have hπu : (QuotientGroup.mk uJ : ↥J ⧸ O) ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val (hinv uJ huJ2 ((QuotientGroup.eq_one_iff _).mp h))
    rcases hu12 with rfl | rfl
    · exact hneg (hρ₁ (h'.trans (map_one ρ₁).symm))
    · exact hneg (hρ₂ (h'.trans (map_one ρ₂).symm))
  have hπcu : (QuotientGroup.mk cJ : ↥J ⧸ O) ≠ QuotientGroup.mk uJ := by
    intro h
    have hw : cJ * uJ⁻¹ ∈ O := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h,
        mul_inv_cancel]
    have hw2 : (cJ * uJ⁻¹) * (cJ * uJ⁻¹) = 1 := by
      have hui : uJ⁻¹ = uJ := inv_eq_of_mul_eq_one_right huJ2
      rw [hui, mul_assoc, ← mul_assoc uJ, huZ cJ, mul_assoc, huJ2, mul_one, hcJ2]
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
      rw [← map_mul, ← map_mul, mem_center_iff.mp (hπZ cJ hcZ) g]
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

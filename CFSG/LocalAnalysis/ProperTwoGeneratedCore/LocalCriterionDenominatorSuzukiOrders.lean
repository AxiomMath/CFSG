module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiFamilyOrderIdentity
public import Certificates.Certificate43

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki.MatrixGroups

theorem suzuki_twist_order_square (m : ℕ) :
    (2 ^ (m + 1)) ^ 2 = 2 * 2 ^ (2 * m + 1) := by
  rw [← pow_mul, show (m + 1) * 2 = (2 * m + 1) + 1 by omega, pow_succ]
  ring

theorem full_degree_sum_product_order_roots (q R s r : ℕ)
    (hRsq : R ^ 2 = 2 * q) (hRq : R ≤ q)
    (hproduct : s * r = q ^ 2 + 1) (hsum : s + r = 2 * (q + 1)) :
    s = q - R + 1 ∨ s = q + R + 1 := by
  have hproductZ : (s : ℤ) * (r : ℤ) = (q : ℤ) ^ 2 + 1 := by
    exact_mod_cast hproduct
  have hsumZ : (s : ℤ) + (r : ℤ) = 2 * ((q : ℤ) + 1) := by
    exact_mod_cast hsum
  have hRZ : (R : ℤ) ^ 2 = 2 * (q : ℤ) := by exact_mod_cast hRsq
  have hsumMul := congrArg (fun x : ℤ => (s : ℤ) * x) hsumZ
  have hsq : ((s : ℤ) - ((q : ℤ) + 1)) ^ 2 = (R : ℤ) ^ 2 := by
    nlinarith only [hproductZ, hsumMul, hRZ]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with hplus | hminus
  · right
    omega
  · left
    omega

variable (m : ℕ)

local notation "q" => 2 ^ (2 * m + 1)
local notation "SzG" => SuzukiMatrixGroup m
local notation "Classes" => suzukiDerangementCentralizerClasses m

theorem suzuki_derangement_representative_exact_order
    (hm : 0 < m) (c : Classes) :
    Nat.card (suzukiDerangementCentralizerRepresentative m c).val = q - 2 ^ (m + 1) + 1 ∨
      Nat.card (suzukiDerangementCentralizerRepresentative m c).val = q + 2 ^ (m + 1) + 1 := by
  obtain ⟨d, hdc, _huniq⟩ := (Nat.card_eq_two_iff' c).mp
    (suzuki_derangement_family_card_eq_two m hm)
  obtain ⟨hproduct, hsum⟩ :=
    suzuki_derangement_two_family_order_sum_product m hm c d hdc.symm
  exact full_degree_sum_product_order_roots q (2 ^ (m + 1)) _ _
    (suzuki_twist_order_square m)
    (Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)) hproduct hsum

theorem suzuki_derangement_family_card_representative
    (A : suzukiDerangementCentralizers m) :
    Nat.card A.val = Nat.card
      (suzukiDerangementCentralizerRepresentative m
        (Quotient.mk'' A : Classes)).val := by
  let := suzukiDerangementCentralizerAction m
  let c : Classes := Quotient.mk'' A
  let B := suzukiDerangementCentralizerRepresentative m c
  have hrel : (MulAction.orbitRel SzG (suzukiDerangementCentralizers m)) A B :=
    Quotient.exact (Quotient.out_eq c).symm
  obtain ⟨g, hg⟩ := hrel
  have hmap : B.val.map (MulAut.conj g).toMonoidHom = A.val :=
    congrArg Subtype.val hg
  rw [← hmap]
  exact (Nat.card_congr
    (B.val.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm

theorem suzuki_derangement_family_exact_order (hm : 0 < m)
    (A : suzukiDerangementCentralizers m) :
    Nat.card A.val = q - 2 ^ (m + 1) + 1 ∨ Nat.card A.val = q + 2 ^ (m + 1) + 1 := by
  rw [suzuki_derangement_family_card_representative m A]
  exact suzuki_derangement_representative_exact_order m hm _

theorem suzuki_derangement_entire_centralizer_exact_order (hm : 0 < m)
    (g : SzG) (hg : suzukiDerangement m g) :
    Nat.card (Subgroup.centralizer ({g} : Set SzG)) = q - 2 ^ (m + 1) + 1 ∨
      Nat.card (Subgroup.centralizer ({g} : Set SzG)) = q + 2 ^ (m + 1) + 1 :=
  suzuki_derangement_family_exact_order m hm ⟨_, ⟨g, hg, rfl⟩⟩

theorem suzuki_degree_divisor_entire_centralizer_exact_order
    (hm : 0 < m)
    (g : SzG) (hg : g ≠ 1) (hdiv : orderOf g ∣ q ^ 2 + 1) :
    Nat.card (Subgroup.centralizer ({g} : Set SzG)) = q - 2 ^ (m + 1) + 1 ∨
      Nat.card (Subgroup.centralizer ({g} : Set SzG)) = q + 2 ^ (m + 1) + 1 :=
  suzuki_derangement_entire_centralizer_exact_order m hm g
    (suzuki_degree_divisor_derangement m g hg hdiv)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

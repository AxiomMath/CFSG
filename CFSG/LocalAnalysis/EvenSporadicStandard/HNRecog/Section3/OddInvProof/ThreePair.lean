module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem isElemAbelian_two_of_le {G : Type} [Group G] {A H : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hHA : H ≤ A) : CFSG.Open.IsElemAbelian 2 H := by
  haveI : IsMulCommutative ↥A := hA.1
  refine ⟨IsMulCommutative.of_comm (fun x y => Subtype.ext ?_), fun x hx => hA.2 x (hHA hx)⟩
  exact congrArg (Subtype.val : ↥A → G)
    (mul_comm' (⟨(x : G), hHA x.2⟩ : ↥A) ⟨(y : G), hHA y.2⟩)

theorem oddInv_three_exists_pair {G : Type} [Group G] [Finite G] {C W A : Subgroup G}
    (hCA : C ≤ A) (hWA : W ≤ A) (hA : IsElemTwo 5 A) (hW : IsElemTwo 4 W)
    (hC : 8 ≤ Nat.card ↥C) : ∃ E : Subgroup G, E ≤ C ⊓ W ∧ IsElemTwo 2 E := by
  have hcardA : Nat.card ↥A = 32 := by rw [hA.2]; norm_num
  have hrelA32 : C.relIndex A * Nat.card ↥C = 32 := by
    calc C.relIndex A * Nat.card ↥C
        = C.relIndex A * Nat.card ↥(C ⊓ A) := by rw [inf_eq_left.2 hCA]
      _ = Nat.card ↥A := Subgroup.relIndex_mul_card (H := C) (K := A)
      _ = 32 := hcardA
  have hrelC : C.relIndex A ≤ 4 := by
    have hle : C.relIndex A * 8 ≤ 4 * 8 := by
      calc C.relIndex A * 8 ≤ C.relIndex A * Nat.card ↥C := Nat.mul_le_mul_left _ hC
        _ = 32 := hrelA32
        _ = 4 * 8 := by norm_num
    exact Nat.le_of_mul_le_mul_right hle (by norm_num)
  have hrelW : W.relIndex A = 2 := by
    have h : W.relIndex A * Nat.card ↥W = 32 := by
      calc W.relIndex A * Nat.card ↥W
          = W.relIndex A * Nat.card ↥(W ⊓ A) := by rw [inf_eq_left.2 hWA]
        _ = Nat.card ↥A := Subgroup.relIndex_mul_card (H := W) (K := A)
        _ = 32 := hcardA
    rw [hW.2] at h
    norm_num at h
    omega
  have hInfA : C ⊓ W ≤ A := inf_le_left.trans hCA
  have hrelInf : (C ⊓ W).relIndex A ≤ 8 := by
    calc (C ⊓ W).relIndex A ≤ C.relIndex A * W.relIndex A := Subgroup.relIndex_inf_le
      _ ≤ 4 * 2 := Nat.mul_le_mul hrelC (le_of_eq hrelW)
      _ = 8 := by norm_num
  have hrelInfCard : (C ⊓ W).relIndex A * Nat.card ↥(C ⊓ W) = 32 := by
    calc (C ⊓ W).relIndex A * Nat.card ↥(C ⊓ W)
        = (C ⊓ W).relIndex A * Nat.card ↥((C ⊓ W) ⊓ A) := by rw [inf_eq_left.2 hInfA]
      _ = Nat.card ↥A := Subgroup.relIndex_mul_card (H := C ⊓ W) (K := A)
      _ = 32 := hcardA
  have hcardInf4 : 4 ≤ Nat.card ↥(C ⊓ W) := by
    have h32 : 8 * 4 ≤ 8 * Nat.card ↥(C ⊓ W) := by
      calc 8 * 4 = 32 := by norm_num
        _ = (C ⊓ W).relIndex A * Nat.card ↥(C ⊓ W) := hrelInfCard.symm
        _ ≤ 8 * Nat.card ↥(C ⊓ W) := Nat.mul_le_mul_right _ hrelInf
    exact Nat.le_of_mul_le_mul_left h32 (by norm_num)
  have hdvd : Nat.card ↥(C ⊓ W) ∣ 2 ^ 5 := by
    have h := Subgroup.card_dvd_of_le hInfA
    rwa [hA.2] at h
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj2 : 2 ≤ j := by
    have h22 : 2 ^ 2 ≤ 2 ^ j := by
      rw [← hjeq]
      calc 2 ^ 2 = 4 := by norm_num
        _ ≤ Nat.card ↥(C ⊓ W) := hcardInf4
    exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp h22
  have hdvd4 : 2 ^ 2 ∣ Nat.card ↥(C ⊓ W) := by
    rw [hjeq]
    exact Nat.pow_dvd_pow 2 hj2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(C ⊓ W)) 2 (n := 2) hdvd4
  refine ⟨K.map (C ⊓ W).subtype, Subgroup.map_subtype_le K, ?_⟩
  refine ⟨isElemAbelian_two_of_le hA.1 ((Subgroup.map_subtype_le K).trans hInfA), ?_⟩
  rw [Subgroup.card_subtype, hK]

end CFSG.EvenSporadicStandard.HNRecog.Section3

module

public import CFSG.GroupTheory.CentralizerSylowFusion

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G]

theorem not_isConj_of_isSylowOf_inf_centralizer_of_le {p : ℕ} [Fact p.Prime] {e y : G}
    {H K : Subgroup G} (hHe : H ≤ centralizer ({e} : Set G))
    (hK : IsSylowOf p K (H ⊓ centralizer ({y} : Set G)))
    (hN : ∀ g ∈ centralizer ({y} : Set G), g ∈ normalizer (K : Set G) →
      IsPGroup p (zpowers g) → g ∈ H)
    (hdvd : p ∣ (H ⊓ centralizer ({y} : Set G)).relIndex H) :
    ¬ IsConj e y := by
  intro hconj
  have hKM : IsSylowOf p K (centralizer ({y} : Set G)) :=
    isSylowOf_of_forall_pElement_normalizer_le hK hN
  have hcard : Nat.card (centralizer ({y} : Set G)) = Nat.card (centralizer ({e} : Set G)) :=
    (card_centralizer_singleton_congr_of_isConj hconj).symm
  have hKH : K ≤ H := hK.le.trans inf_le_left
  have hdvdHe : Nat.card H ∣ Nat.card (centralizer ({e} : Set G)) :=
    Subgroup.card_dvd_of_le hHe
  have hv : (Nat.card H).factorization p ≤
      (Nat.card (centralizer ({e} : Set G))).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvdHe p
  have hKcard : Nat.card K = p ^ (Nat.card (centralizer ({e} : Set G))).factorization p := by
    rw [hKM.card_eq, hcard]
  have hKdvd : Nat.card K ∣ Nat.card H := Subgroup.card_dvd_of_le hKH
  have hle : (Nat.card (centralizer ({e} : Set G))).factorization p ≤
      (Nat.card H).factorization p :=
    ((Fact.out : p.Prime).pow_dvd_iff_le_factorization Nat.card_pos.ne').mp (hKcard ▸ hKdvd)
  have hKHcard : Nat.card K = p ^ (Nat.card H).factorization p := by
    rw [hKcard, le_antisymm hle hv]
  have hKHs : IsSylowOf p K H := isSylowOf_of_card hKH hKHcard
  rw [isSylowOf_iff] at hKHs
  obtain ⟨-, -, hndvd⟩ := hKHs
  apply hndvd
  rw [← Subgroup.relIndex_mul_relIndex K (H ⊓ centralizer ({y} : Set G)) H hK.le inf_le_left]
  exact hdvd.mul_left _

end CFSG.GroupTheory

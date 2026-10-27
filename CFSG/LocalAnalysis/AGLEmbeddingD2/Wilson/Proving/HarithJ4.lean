module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.DivisorArithmetic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.NormMaxTI

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Subgroup

variable {G : Type*} [Group G]

theorem index_eq_J4_of_card (N : Subgroup G) (hG : Nat.card G = 86775571046077562880)
    (hN : Nat.card N = 319440) :
    N.index = 2 ^ 17 * 3 ^ 2 * 7 * 23 * 29 * 31 * 37 * 43 := by
  have h := Subgroup.card_mul_index (H := N)
  rw [hN, hG] at h
  have h2 : 319440 * N.index = 319440 * (2 ^ 17 * 3 ^ 2 * 7 * 23 * 29 * 31 * 37 * 43) := by
    rw [h]
    norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

theorem harith_J4 (N R : Subgroup G) (hG : Nat.card G = 86775571046077562880)
    (hN : Nat.card N = 319440) (hR : Nat.card R = 1331) :
    ∀ d : ℕ, d ∣ N.index → d ≡ 1 [MOD Nat.card R] → d = 1 ∨ 2 ∣ d := by
  intro d hd hmod
  rw [index_eq_J4_of_card N hG hN] at hd
  rw [hR] at hmod
  apply divisor_mod_1331_one_or_two_dvd hd
  unfold Nat.ModEq at hmod
  norm_num at hmod
  exact hmod

theorem normMax_of_TI_involution_J4 [Finite G] [Fact (Nat.Prime 11)] (R : Sylow 11 G)
    (hG : Nat.card G = 86775571046077562880)
    (hN : Nat.card (normalizer (R : Set G) : Subgroup G) = 319440)
    (hR : Nat.card (R : Subgroup G) = 1331)
    (hTI : ∀ g : G, g ∉ normalizer (R : Set G) →
      (R : Subgroup G) ⊓ (R : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊥)
    (t : G) (htN : t ∈ normalizer (R : Set G)) (ht : orderOf t = 2)
    (hfuse : ∀ s ∈ normalizer (R : Set G), IsConj t s →
      ∃ m ∈ normalizer (R : Set G), m * t * m⁻¹ = s)
    (hover : ∀ T : Subgroup G, normalizer (R : Set G) ⊓ Subgroup.centralizer {t} < T →
      T ≤ Subgroup.centralizer {t} → normalizer (R : Set G) ⊔ T = ⊤)
    (Y : Subgroup G) (hY : normalizer (R : Set G) ≤ Y) :
    Y = normalizer (R : Set G) ∨ Y = ⊤ :=
  normMax_of_TI_involution R hTI (harith_J4 _ _ hG hN hR) t htN ht hfuse hover Y hY

end CFSG.AGLEmbeddingD2.Wilson.Proving

end

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.L1Burnside

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {z t m : G}
  {T1 F1 F2 : Subgroup G}

theorem K_goodK_of_data (hnonab : ∃ a b : G, a * b ≠ b * a) (hOne : OneClassData L z t)
    (hD : FusionData L t T1 F1 F2 m) (hN : NData L F1) (hX : FixedData L F1)
    (hR : RankFour L) (hgood : GoodK z F1) :
    ∃ L1 : Subgroup G, L1 ≤ Ksub z F1 ∧ F1 ≤ L1 ∧ Nat.card L1 = 256 ∧
      (∀ x ∈ L1, x * x = 1) ∧ (∀ x ∈ L1, ∀ y ∈ L1, x * y = y * x) ∧ z ∉ L1 ∧
      Ksub z F1 = L1 ⊔ zpowers z ∧ (∀ x ∈ L1, x ∈ F1 ⊔ zpowers z → x ∈ F1) ∧
      (∀ x ∈ L1, z * x = x * z → x ∈ F1) ∧
      (∀ n : G, (∀ x, x ∈ F1 ⊔ zpowers z ↔ n * x * n⁻¹ ∈ F1 ⊔ zpowers z) →
        ∀ x, x ∈ L1 ↔ n * x * n⁻¹ ∈ L1) ∧
      (∀ x ∈ L1, ¬ IsConj z x) ∧ IsPGroup 2 (Ksub z F1) ∧
      ¬ 2 ∣ (Ksub z F1).relIndex (centralizer (F1 : Set G)) ∧
      ¬ 2 ∣ L1.relIndex (centralizer (L1 : Set G)) ∧
      (∃ N : Subgroup G, N ≤ centralizer (L1 : Set G) ∧
        (∀ c ∈ centralizer (L1 : Set G), ∀ x ∈ N, c * x * c⁻¹ ∈ N) ∧ ¬ 2 ∣ Nat.card N ∧
        Disjoint N L1 ∧ N ⊔ L1 = centralizer (L1 : Set G)) ∧
      (∀ n : G, (∀ x, x ∈ Ksub z F1 ↔ n * x * n⁻¹ ∈ Ksub z F1) →
        ∀ x, x ∈ L1 ↔ n * x * n⁻¹ ∈ L1) ∧
      (∀ k ∈ Ksub z F1, IsConj z k → ∃ f ∈ F1, k = z * f) := by
  have hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z) := fun u hu hu2 hu1 =>
    fused_all hnonab hOne hu hu2 hu1
  have htr := exists_normalizer_conj_eq_mul hnonab hOne hD hN.trans
  obtain ⟨hK2, hK3⟩ := Ksub_sylow hOne hZ hN hgood hX htr hR
  obtain ⟨-, hL3⟩ := L1_sylow hOne hZ hN hgood hX htr hR
  have hBu := exists_normal_two_complement hOne hZ hN hgood hX htr hR
  exact ⟨L1sub hOne hN hgood, L1sub_le_K hOne hN hgood, F_le_L1sub hOne hN hgood,
    card_L1sub hOne hZ hN hgood hX htr, fun x hx => L1sub_sq hOne hN hgood hx,
    fun x hx y hy => L1sub_comm hOne hN hgood hx hy, z_not_mem_L1sub hOne hN hgood,
    Ksub_eq_L1_sup hOne hZ hN hgood hX, fun x hx hxE => L1sub_inf_E hOne hN hgood hx hxE,
    fun x hx hxz => L1sub_centralizer_z hOne hN hgood hx hxz,
    fun n hn => L1_normalized hOne hZ hN hgood hn,
    fun x hx => L1_not_isConj hOne hZ hN hgood hX htr hR hx, hK2, hK3, hL3, hBu,
    fun n hn => L1_normalized_of_normalizes_K hOne hZ hN hgood hX htr hn,
    fun k hk hconj => eq_mul_of_isConj_of_mem_Ksub hOne hZ hN hgood hX htr hR hk hconj⟩

end CFSG.EvenSporadicStandard.M23Std

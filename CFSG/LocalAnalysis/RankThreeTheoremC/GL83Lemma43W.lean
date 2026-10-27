module

public import CFSG.Quasithin.Background.A4Four
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PCoreQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Quasithin (OTwoQuot)
open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem inf_eq_of_card_three {Y T S : Subgroup G} (hY2 : IsPGroup 2 Y) (hSY : S ≤ Y)
    (hST : S ≤ T) (hT3 : Nat.card T = 3 * Nat.card S) : T ⊓ Y = S := by
  have hSle : S ≤ T ⊓ Y := le_inf hST hSY
  obtain ⟨k, hk⟩ := (hY2.to_inf_right (H := T)).exists_card_eq
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hSle
  have hdvd : Nat.card (T ⊓ Y : Subgroup G) ∣ Nat.card T := Subgroup.card_dvd_of_le inf_le_left
  have hS0 : 0 < Nat.card S := Nat.card_pos
  have hm3 : m ∣ 3 := by
    rw [hm, hT3, mul_comm 3] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hS0 hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h1 | h3
  · exact (Subgroup.eq_of_le_of_card_ge hSle (le_of_eq (by rw [hm, h1, mul_one]))).symm
  · exfalso
    have h3dvd : 3 ∣ 2 ^ k := by
      rw [← hk, hm, h3]
      exact dvd_mul_left _ _
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)

theorem l43_wStructure {Y T S : Subgroup G} (hY2 : IsPGroup 2 Y) (hSY : S ≤ Y) (hST : S ≤ T)
    (hTS : T ≤ normalizer (S : Set G)) (hYS : Y ≤ normalizer (S : Set G))
    (hYT : Y ≤ normalizer (T : Set G)) (hT3 : Nat.card T = 3 * Nat.card S)
    (hnt : ∃ y ∈ Y, ∃ t ∈ T, y * t * y⁻¹ * t⁻¹ ∉ S) :
    IsSylowTwoOf Y (T ⊔ Y) ∧ Nat.card (T ⊔ Y : Subgroup G) = 3 * Nat.card Y ∧
      Nonempty (OTwoQuot (T ⊔ Y) ≃* Equiv.Perm (Fin 3)) := by
  have _ := hTS
  have _ := hYS
  have hTY : T ⊓ Y = S := inf_eq_of_card_three hY2 hSY hST hT3
  have hsecond : T.relIndex (Y ⊔ T) = T.relIndex Y := by
    have _ : (T.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYT
    have _ : (T.subgroupOf (Y ⊔ T)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hYT
    exact (Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient Y T hYT).toEquiv).symm
  have hr1 := Subgroup.relIndex_mul_card (H := T) (K := Y)
  have hr2 := Subgroup.relIndex_mul_card (H := T) (K := Y ⊔ T)
  rw [hTY] at hr1
  rw [inf_eq_left.mpr le_sup_right] at hr2
  have hW : Nat.card (T ⊔ Y : Subgroup G) = 3 * Nat.card Y := by
    rw [sup_comm, ← hr2, hsecond, hT3, ← hr1]
    ring
  have hr3 := Subgroup.relIndex_mul_card (H := Y) (K := T ⊔ Y)
  rw [inf_eq_left.mpr le_sup_right, hW] at hr3
  have hY0 : 0 < Nat.card Y := Nat.card_pos
  have hrel : Y.relIndex (T ⊔ Y) = 3 := Nat.eq_of_mul_eq_mul_right hY0 hr3
  have hnn : ¬ (T ⊔ Y) ≤ normalizer (Y : Set G) := by
    intro hN
    obtain ⟨y, hy, t, ht, hnot⟩ := hnt
    apply hnot
    have h1 : y * t * y⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem ((mem_normalizer_iff.mp (hYT hy) t).mp ht) (T.inv_mem ht)
    have h2 : y * t * y⁻¹ * t⁻¹ ∈ Y := by
      have htn : t ∈ normalizer (Y : Set G) := hN (Subgroup.mem_sup_left ht)
      have h3 : t * y⁻¹ * t⁻¹ ∈ Y := (mem_normalizer_iff.mp htn y⁻¹).mp (Y.inv_mem hy)
      have h4 := Y.mul_mem hy h3
      simpa [mul_assoc] using h4
    rw [← hTY]
    exact ⟨h1, h2⟩
  obtain ⟨e⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.nonempty_quotient_pCore_mulEquiv_perm_three_of_le
      le_sup_right hY2 hrel hnn
  exact ⟨CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.isSylowTwoOf_of_relIndex_three
    le_sup_right hY2 hrel, hW, ⟨e⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

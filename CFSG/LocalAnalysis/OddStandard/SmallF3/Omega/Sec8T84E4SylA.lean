module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem card_sup_mul_card_inf_of_le_normalizer {G : Type} [Group G] [Finite G]
    {H K : Subgroup G} (h : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 : H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K :=
    (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer h).1
  have h2 : H.relIndex (H ⊔ K) * Nat.card ↥H = Nat.card ↥(H ⊔ K) := by
    have := Subgroup.relIndex_mul_card (H := H) (K := H ⊔ K)
    rwa [inf_eq_left.mpr (le_sup_left : H ≤ H ⊔ K)] at this
  have h3 : (H ⊓ K).relIndex K * Nat.card ↥(H ⊓ K) = Nat.card ↥K := by
    have := Subgroup.relIndex_mul_card (H := H ⊓ K) (K := K)
    rwa [inf_eq_left.mpr (inf_le_right : H ⊓ K ≤ K)] at this
  rw [← h2, h1, ← h3]
  ring

theorem sec8t84_le_sylow_of_normal {G : Type} [Group G] [Finite G] {X T E : Subgroup G}
    (hT : IsSylow2Of T X) (hEX : E ≤ X) (hE : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E)
    (hE2 : IsPGroup 2 E) : E ≤ T := by
  obtain ⟨hTX, hT2, hTodd⟩ := hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hEnorm : (E.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEX).mpr (Subgroup.le_normalizer_iff.mpr hE)
  have hE2' : IsPGroup 2 ↥(E.subgroupOf X) :=
    hE2.of_equiv (Subgroup.subgroupOfEquivOfLe hEX).symm
  have hT2' : IsPGroup 2 ↥(T.subgroupOf X) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hle : E.subgroupOf X ≤ (hT2'.toSylow hTodd : Subgroup ↥X) :=
    IsPGroup.le_sylow_of_normal hE2' (hT2'.toSylow hTodd)
  intro e he
  have hx : (⟨e, hEX he⟩ : ↥X) ∈ T.subgroupOf X :=
    hle (show (⟨e, hEX he⟩ : ↥X) ∈ E.subgroupOf X from he)
  exact Subgroup.mem_subgroupOf.mp hx

theorem sec8t84_sylow_inf_normal {G : Type} [Group G] [Finite G] {S H N : Subgroup G}
    (hS : IsSylow2Of S H) (hNH : N ≤ H) (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) :
    IsSylow2Of (S ⊓ N) N := by
  obtain ⟨hSH, hS2, hSodd⟩ := hS
  refine ⟨inf_le_right, hS2.to_inf_left, ?_⟩
  have hSN : S ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun s hs n hn => hN s (hSH hs) n hn
  have h2 : S.relIndex N = S.relIndex (S ⊔ N) := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := S) (K := N) hSN).1
    rw [Subgroup.inf_relIndex_right] at h
    exact h.symm
  have h3 : S.relIndex (S ⊔ N) ∣ S.relIndex H := by
    have hmul := Subgroup.relIndex_mul_relIndex (H := S) (K := S ⊔ N) (L := H)
      le_sup_left (sup_le hSH hNH)
    exact ⟨(S ⊔ N).relIndex H, hmul.symm⟩
  rw [Subgroup.inf_relIndex_right]
  intro h
  rw [h2] at h
  exact hSodd (h.trans h3)

theorem sec8t84_sylow_sup_commuting {G : Type} [Group G] [Finite G] {Y1 Y2 S1 S2 : Subgroup G}
    (h12 : ∀ a ∈ Y1, ∀ b ∈ Y2, a * b * a⁻¹ ∈ Y2)
    (h21 : ∀ b ∈ Y2, ∀ a ∈ Y1, b * a * b⁻¹ ∈ Y1)
    (hodd : Odd (Nat.card ↥(Y1 ⊓ Y2))) (hS1 : IsSylow2Of S1 Y1) (hS2 : IsSylow2Of S2 Y2)
    (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a) (hinf : S1 ⊓ S2 = ⊥) :
    IsSylow2Of (S1 ⊔ S2) (Y1 ⊔ Y2) ∧ Nat.card ↥(S1 ⊔ S2) = Nat.card S1 * Nat.card S2 := by
  obtain ⟨hS1Y1, hS1_2, hS1odd⟩ := hS1
  obtain ⟨hS2Y2, hS2_2, hS2odd⟩ := hS2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY12 : Y1 ≤ Subgroup.normalizer (Y2 : Set G) := Subgroup.le_normalizer_iff.mpr h12
  have hS12 : S1 ≤ Subgroup.normalizer (S2 : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun a ha b hb => by
      rw [hcomm a ha b hb, mul_inv_cancel_right]
      exact hb
  have hcardS : Nat.card ↥(S1 ⊔ S2) = Nat.card S1 * Nat.card S2 := by
    have hrel : S1.relIndex (S1 ⊔ S2) = Nat.card S2 := by
      have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
        (H := S1) (K := S2) hS12).1
      rwa [hinf, Subgroup.relIndex_bot_left] at h
    have hmul := Subgroup.relIndex_mul_card (H := S1) (K := S1 ⊔ S2)
    rw [inf_eq_left.mpr (le_sup_left : S1 ≤ S1 ⊔ S2), hrel, mul_comm] at hmul
    exact hmul.symm
  have hS2group : IsPGroup 2 ↥(S1 ⊔ S2) := by
    obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp hS1_2
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hS2_2
    exact IsPGroup.of_card (n := i + j) (by rw [hcardS, hi, hj, pow_add])
  have hYcard : Nat.card ↥(Y1 ⊔ Y2) * Nat.card ↥(Y1 ⊓ Y2) = Nat.card Y1 * Nat.card Y2 :=
    card_sup_mul_card_inf_of_le_normalizer hY12
  have h1rel : S1.relIndex Y1 * Nat.card S1 = Nat.card Y1 := by
    have := Subgroup.relIndex_mul_card (H := S1) (K := Y1)
    rwa [inf_eq_left.mpr hS1Y1] at this
  have h2rel : S2.relIndex Y2 * Nat.card S2 = Nat.card Y2 := by
    have := Subgroup.relIndex_mul_card (H := S2) (K := Y2)
    rwa [inf_eq_left.mpr hS2Y2] at this
  have hSrel : (S1 ⊔ S2).relIndex (Y1 ⊔ Y2) * Nat.card ↥(S1 ⊔ S2) = Nat.card ↥(Y1 ⊔ Y2) := by
    have := Subgroup.relIndex_mul_card (H := S1 ⊔ S2) (K := Y1 ⊔ Y2)
    rwa [inf_eq_left.mpr (sup_le_sup hS1Y1 hS2Y2)] at this
  have hcancel : (S1 ⊔ S2).relIndex (Y1 ⊔ Y2) * Nat.card ↥(Y1 ⊓ Y2) =
      S1.relIndex Y1 * S2.relIndex Y2 := by
    have hpos : 0 < Nat.card ↥(S1 ⊔ S2) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (S1 ⊔ S2).relIndex (Y1 ⊔ Y2) * Nat.card ↥(Y1 ⊓ Y2) * Nat.card ↥(S1 ⊔ S2)
        = ((S1 ⊔ S2).relIndex (Y1 ⊔ Y2) * Nat.card ↥(S1 ⊔ S2)) *
            Nat.card ↥(Y1 ⊓ Y2) := by ring
      _ = Nat.card ↥(Y1 ⊔ Y2) * Nat.card ↥(Y1 ⊓ Y2) := by rw [hSrel]
      _ = Nat.card Y1 * Nat.card Y2 := hYcard
      _ = (S1.relIndex Y1 * Nat.card S1) * (S2.relIndex Y2 * Nat.card S2) := by
            rw [← h1rel, ← h2rel]
      _ = (S1.relIndex Y1 * S2.relIndex Y2) * Nat.card ↥(S1 ⊔ S2) := by rw [hcardS]; ring
  have hoddidx : ¬ 2 ∣ (S1 ⊔ S2).relIndex (Y1 ⊔ Y2) := by
    intro h
    have h2 : 2 ∣ S1.relIndex Y1 * S2.relIndex Y2 := by
      rw [← hcancel]
      exact dvd_mul_of_dvd_left h _
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with hc | hd
    · exact hS1odd hc
    · exact hS2odd hd
  exact ⟨⟨sup_le_sup hS1Y1 hS2Y2, hS2group, hoddidx⟩, hcardS⟩

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.K54Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.EvenSporadicStandard.TwoFi22

variable {G : Type} [Group G] [Finite G] {t z : G}

section Certified


theorem Level55.card_centPair (d : Level55 G t z) :
    Nat.card ↥(centPair z t) = 2 ^ 24 * 42305421312000 := by
  obtain ⟨e⟩ := d.quot
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(centPair z t))
  have h2 : Nat.card (↥(centPair z t) ⧸ CFSG.pCore 2 ↥(centPair z t)) = 42305421312000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Co2.card_Co2
  have h3 : Nat.card (CFSG.pCore 2 ↥(centPair z t)) = 2 ^ 24 := by
    rw [← d.card_O2K, O2In, Subgroup.card_map_of_injective (centPair z t).subtype_injective]
  rw [h1, h2, h3, mul_comm]


theorem Level55.eq_two_of_card_cases (d : Level55 G t z)
    (hle : centZ z ≤ centralizer ({t} : Set G)) {u : G} (hu : u ∈ centZ z)
    (hunot : u ∉ pair z t) {k : Fin 4}
    (hk : Nat.card ↥(centZ z ⊓ centralizer ({u} : Set G)) = babyCentOrder k ∨
      Nat.card ↥(centZ z ⊓ centralizer ({u} : Set G)) = 2 * babyCentOrder k) : k = 2 := by
  have hKeq : centPair z t = centZ z := by
    rw [centPair_eq_inf]
    exact inf_eq_left.2 hle
  have hK : Nat.card ↥(centZ z) = 2 ^ 24 * 42305421312000 := by
    rw [← hKeq]
    exact d.card_centPair
  set Y : Subgroup G := centZ z ⊓ centralizer ({u} : Set G) with hY
  have hYK : Y ≤ centZ z := inf_le_left
  have hdvd : Nat.card ↥Y ∣ Nat.card ↥(centZ z) := Subgroup.card_dvd_of_le hYK
  rw [hK] at hdvd
  have h13 : ¬ (13 ∣ 2 ^ 24 * 42305421312000) := by norm_num
  fin_cases k
  · exfalso
    apply h13
    have h0 : 13 ∣ babyCentOrder 0 := by norm_num [babyCentOrder]
    rcases hk with hk | hk
    · rw [hk] at hdvd
      exact h0.trans hdvd
    · rw [hk] at hdvd
      exact h0.trans ((Dvd.intro_left 2 rfl).trans hdvd)
  · exfalso
    change (Nat.card ↥Y = babyCentOrder 1 ∨ Nat.card ↥Y = 2 * babyCentOrder 1) at hk
    have hc1 : babyCentOrder 1 = 2 ^ 41 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23 := rfl
    have hKc : 2 ^ 24 * 42305421312000 = 2 * babyCentOrder 1 := by
      rw [hc1]; norm_num
    rw [hKc] at hdvd
    have hKcard : Nat.card ↥(centZ z) = 2 * babyCentOrder 1 := by rw [hK, hKc]
    rcases hk with hk | hk
    ·
      have hr := Subgroup.relIndex_mul_card (H := Y) (K := centZ z)
      rw [inf_of_le_left hYK, hk, hKcard] at hr
      have hpos : 0 < babyCentOrder 1 := by rw [hc1]; norm_num
      have hr2 : Y.relIndex (centZ z) = 2 := by
        apply Nat.eq_of_mul_eq_mul_right hpos
        omega
      have hnorm : (Y.subgroupOf (centZ z)).Normal := by
        apply Subgroup.normal_of_index_eq_two
        exact hr2
      have hinv : ∀ k ∈ centPair z t, ∀ n ∈ Y, k * n * k⁻¹ ∈ Y := by
        intro k hk' n hn
        rw [hKeq] at hk'
        have := hnorm.conj_mem ⟨n, hYK hn⟩ (mem_subgroupOf.2 hn) ⟨k, hk'⟩
        exact mem_subgroupOf.1 this
      have hnle : ¬ Y ≤ O2In (centPair z t) := by
        intro hle2
        have := Subgroup.card_le_of_le hle2
        rw [d.card_O2K, hk, hc1] at this
        norm_num at this
      have heq := d.eq_K_of_not_le_O2K (hKeq ▸ hYK) hinv hnle
      rw [hKeq] at heq
      have : Nat.card ↥Y = Nat.card ↥(centZ z) := by rw [heq]
      rw [hk, hKcard] at this
      omega
    ·
      have heq : Y = centZ z := by
        apply Subgroup.eq_of_le_of_card_ge hYK
        rw [hk, hKcard]
      have hcc : ∀ k ∈ centPair z t, u * k = k * u := by
        intro k hk'
        rw [hKeq] at hk'
        have : k ∈ Y := heq ▸ hk'
        exact (mem_centralizer_singleton_iff.1 (mem_inf.1 this).2).symm
      exact hunot (d.central_K_le_pair (hKeq ▸ hu) hcc)
  · rfl
  · exfalso
    apply h13
    have h0 : 13 ∣ babyCentOrder 3 := by norm_num [babyCentOrder]
    rcases hk with hk | hk
    · rw [hk] at hdvd
      exact h0.trans hdvd
    · rw [hk] at hdvd
      exact h0.trans ((Dvd.intro_left 2 rfl).trans hdvd)

end Certified

end CFSG.EvenSporadicStandard.TwoB

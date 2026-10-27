module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10AutAbRed
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelB0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

theorem card_abelian_two_le_16_A0
    {X : Subgroup P45} (hXA : X ≤ QA45.originalSubgroup)
    (hp : IsPGroup 2 X) (hc : IsMulCommutative X) : Nat.card X ≤ 16 := by
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hc.1.1 ⟨x, hx⟩ ⟨y, hy⟩)
  set X0 := X ⊓ QP45.originalSubgroup with hX0
  have hX0p : IsPGroup 2 X0 := hp.to_le (by rw [hX0]; exact inf_le_left)
  obtain ⟨Q, hQ, hX0Q⟩ := exists_isSylow2Of_ge hX0p (inf_le_right : X0 ≤ QP45.originalSubgroup)
  obtain ⟨a, ha, hmem⟩ := IsSylow2Of.exists_conj_mem hQ isSylow2Of_QT0
  have haA : a ∈ QA45.originalSubgroup := QP45_le_QA45 ha
  have hconj : ∀ x ∈ X0, a * x * a⁻¹ ∈ QT0.originalSubgroup := by
    intro x hx
    rw [hmem]
    have h : a⁻¹ * (a * x * a⁻¹) * a = x := by group
    rw [h]
    exact hX0Q hx
  let cj : P45 →* P45 := (MulAut.conj a).toMonoidHom
  have hcj : Function.Injective cj := (MulAut.conj a).injective
  have hcjx : ∀ x, cj x = a * x * a⁻¹ := fun x => rfl
  set Y0 := X0.map cj with hY0
  have hY0T : Y0 ≤ QT0.originalSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    exact hconj x hx
  have hY0c : ∀ x ∈ Y0, ∀ y ∈ Y0, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hXc x hx.1 y hy.1]
  have hY0le : Nat.card Y0 ≤ 16 := (card_le_of_abelian hY0T hY0c).trans (by norm_num)
  have hY0X : Nat.card Y0 = Nat.card X0 := Subgroup.card_map_of_injective hcj
  have hidx : Nat.card X = QP45.originalSubgroup.relIndex X * Nat.card X0 := by
    have h := Subgroup.relIndex_mul_card (H := QP45.originalSubgroup) (K := X)
    rw [inf_comm] at h
    exact h.symm.trans (by rw [mul_comm])
  have hPA : QP45.originalSubgroup.relIndex QA45.originalSubgroup = 2 := by
    have h := Subgroup.relIndex_mul_card (H := QP45.originalSubgroup) (K := QA45.originalSubgroup)
    rw [inf_eq_left.2 QP45_le_QA45, card_QP45, card_QA45] at h
    generalize QP45.originalSubgroup.relIndex QA45.originalSubgroup = r at h ⊢
    omega
  have hidx2 : QP45.originalSubgroup.relIndex X ≤ 2 := by
    rw [← hPA]
    exact Subgroup.relIndex_le_of_le_right hXA (by rw [hPA]; norm_num)
  by_cases h16 : Nat.card Y0 = 16
  · have hY0B : Y0 = B0 := eq_B0_of_abelian hY0T hY0c (by rw [h16]; norm_num)
    have hXB : X.map cj ≤ B0 := by
      rintro _ ⟨x, hx, rfl⟩
      refine centralizer_B0_le (a := cj x) ?_ ?_
      · rw [hcjx]
        exact QA45.originalSubgroup.mul_mem (QA45.originalSubgroup.mul_mem haA (hXA hx))
          (QA45.originalSubgroup.inv_mem haA)
      · intro b hb
        rw [← hY0B] at hb
        obtain ⟨k, hk, rfl⟩ := hb
        rw [← map_mul, ← map_mul, hXc x hx k hk.1]
    have hcard := Subgroup.card_le_of_le hXB
    rw [card_B0, Subgroup.card_map_of_injective hcj] at hcard
    exact hcard.trans (by norm_num)
  · obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hX0p
    have hn4 : n ≤ 4 := by
      have h1 : 2 ^ n ≤ 2 ^ 4 := by
        rw [← hn, ← hY0X]
        exact hY0le.trans (by norm_num)
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    have hn3 : n ≤ 3 := by
      rcases Nat.lt_or_ge n 4 with h | h
      · omega
      · exfalso
        apply h16
        have : n = 4 := by omega
        rw [hY0X, hn, this]
        norm_num
    have h8 : Nat.card X0 ≤ 8 := by
      rw [hn]
      calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
        _ = 8 := by norm_num
    rw [hidx]
    calc QP45.originalSubgroup.relIndex X * Nat.card X0 ≤ 2 * 8 := Nat.mul_le_mul hidx2 h8
      _ = 16 := by norm_num

theorem card_le_16_of_psp43
    {K : Type} [Group K]
    (hK : LieModel K .PSp 2 3 1) (X : Subgroup (MulAut K)) (hp : IsPGroup 2 X)
    (hc : IsMulCommutative X) : Nat.card X ≤ 16 := by
  obtain ⟨e⟩ := PSp43.equiv_of_lieModel hK
  obtain ⟨M, -, hMA⟩ := PSp43.exists_model e
  have h1 : X.map M.ι ≤ QA45.originalSubgroup := by
    rintro _ ⟨x, -, rfl⟩
    rw [← hMA]
    exact M.ι_mem x
  have h2 : IsPGroup 2 (X.map M.ι) :=
    hp.of_equiv (Subgroup.equivMapOfInjective X M.ι M.ι_injective)
  haveI := hc
  have h3 : Nat.card (X.map M.ι) = Nat.card X := Subgroup.card_map_of_injective M.ι_injective
  rw [← h3]
  exact card_abelian_two_le_16_A0 h1 h2 (Subgroup.map_isMulCommutative X M.ι)

theorem card_le_16_of_psp43_quotient
    {G : Type} [Group G] [Finite G] {I : Subgroup G}
    (hI : IsQuasisimple I) (hK : LieModel (↥I ⧸ oddCore ↥I) .PSp 2 3 1) {Y : Subgroup G}
    (hYN : Y ≤ normalizer (I : Set G)) (hYC : Y ⊓ centralizer (I : Set G) = ⊥)
    (hp : IsPGroup 2 Y) (hc : IsMulCommutative Y) : Nat.card Y ≤ 16 := by
  have hs : IsSimpleGroup (↥I ⧸ oddCore ↥I) := by
    have hmodel := hK.statedClassicalModel_of_ne_zero (by norm_num)
    exact (CFSG.LieType.Simplicity.fam_classical_converse (↥I ⧸ oddCore ↥I)
      ⟨_, _, 3, _, hmodel⟩).2.2
  exact card_le_of_aut_embedding hI hs hYN hYC hp hc fun X hX hXc =>
    card_le_16_of_psp43 hK X hX hXc

end CFSG.OddStandard.SmallF3.Omega

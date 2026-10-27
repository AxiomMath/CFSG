module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneLambdaZeroCore

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup
open scoped Pointwise

section Generic

variable {X : Type*} [Group X] {B N : Subgroup X} [(N.subgroupOf B).Normal]

theorem quotB_card_map_mul {P : Subgroup X} (hNP : N ≤ P) (hPB : P ≤ B) :
    Nat.card ((P.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B))) * Nat.card N =
      Nat.card P := by
  classical
  set f : P.subgroupOf B →* ↥B ⧸ N.subgroupOf B :=
    (QuotientGroup.mk' (N.subgroupOf B)).comp (P.subgroupOf B).subtype with hf
  have hrange : f.range = (P.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B)) := by
    rw [hf, MonoidHom.range_comp, range_subtype]
  have hker : Nat.card f.ker = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun p => ⟨(((p : P.subgroupOf B) : B) : X), ?_⟩
        invFun := fun n => ⟨⟨⟨n, hNP.trans hPB n.2⟩, mem_subgroupOf.2 (hNP n.2)⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have h : (QuotientGroup.mk' (N.subgroupOf B)) ((p : P.subgroupOf B) : B) = 1 := p.2
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
      exact h
    · show (QuotientGroup.mk' (N.subgroupOf B)) ⟨(n : X), hNP.trans hPB n.2⟩ = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact n.2
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker,
    Nat.card_congr (subgroupOfEquivOfLe hPB).toEquiv] at hcard
  exact hcard.symm

theorem quotB_isElementaryAbelian_map {P : Subgroup X}
    (hPsq : ∀ x ∈ P, x ^ 2 ∈ N) (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    IsElementaryAbelian 2 ((P.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B))) := by
  refine
    { toIsMulCommutative := ⟨⟨fun a c => ?_⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_ }
  · obtain ⟨_, ⟨p, hp, rfl⟩⟩ := a
    obtain ⟨_, ⟨q, hq, rfl⟩⟩ := c
    apply Subtype.ext
    change (QuotientGroup.mk' (N.subgroupOf B)) p * (QuotientGroup.mk' (N.subgroupOf B)) q =
      (QuotientGroup.mk' (N.subgroupOf B)) q * (QuotientGroup.mk' (N.subgroupOf B)) p
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hPc _ (mem_subgroupOf.1 hp) _ (mem_subgroupOf.1 hq))
  · obtain ⟨_, ⟨p, hp, rfl⟩⟩ := a
    apply Subtype.ext
    change ((QuotientGroup.mk' (N.subgroupOf B)) p) ^ 2 = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hPsq _ (mem_subgroupOf.1 hp)

theorem quotB_preimage_facts (hNB : N ≤ B) (Yb : Subgroup (↥B ⧸ N.subgroupOf B)) :
    let Y := (Yb.comap (QuotientGroup.mk' (N.subgroupOf B))).map B.subtype
    N ≤ Y ∧ Y ≤ B ∧ (Y.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B)) = Yb ∧
      (IsElementaryAbelian 2 Yb → (∀ y ∈ Y, y ^ 2 ∈ N) ∧
        ∀ y ∈ Y, ∀ y' ∈ Y, y⁻¹ * y'⁻¹ * y * y' ∈ N) := by
  intro Y
  have hYsub : Y.subgroupOf B = Yb.comap (QuotientGroup.mk' (N.subgroupOf B)) :=
    comap_map_eq_self_of_injective B.subtype_injective _
  refine ⟨fun n hn => ⟨⟨n, hNB hn⟩, ?_, rfl⟩, map_subtype_le _, ?_, fun hY => ⟨?_, ?_⟩⟩
  · show (QuotientGroup.mk' (N.subgroupOf B)) ⟨n, hNB hn⟩ ∈ Yb
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hn)]
    exact one_mem _
  · rw [hYsub]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  · rintro _ ⟨k, hk, rfl⟩
    have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Yb) _ hk
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
    exact h
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    have hc : (QuotientGroup.mk' (N.subgroupOf B)) k * (QuotientGroup.mk' (N.subgroupOf B)) k' =
        (QuotientGroup.mk' (N.subgroupOf B)) k' * (QuotientGroup.mk' (N.subgroupOf B)) k :=
      mul_comm_of_isElementaryAbelian hY hk hk'
    have h : (QuotientGroup.mk' (N.subgroupOf B)) (k⁻¹ * k'⁻¹ * k * k') = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc ((QuotientGroup.mk' (N.subgroupOf B)) k)⁻¹ *
            ((QuotientGroup.mk' (N.subgroupOf B)) k')⁻¹ * (QuotientGroup.mk' (N.subgroupOf B)) k *
            (QuotientGroup.mk' (N.subgroupOf B)) k' =
          ((QuotientGroup.mk' (N.subgroupOf B)) k)⁻¹ *
            ((QuotientGroup.mk' (N.subgroupOf B)) k')⁻¹ *
            ((QuotientGroup.mk' (N.subgroupOf B)) k * (QuotientGroup.mk' (N.subgroupOf B)) k') := by
            group
        _ = 1 := by rw [hc]; group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
    exact h

theorem quotB_card_mul_map_mul {Y Q : Subgroup X} (hNY : N ≤ Y) (hYB : Y ≤ B) (hQB : Q ≤ B)
    [hQn : ((Q.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B))).Normal] :
    Nat.card (((Y.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B)) :
        Set (↥B ⧸ N.subgroupOf B)) *
      ((Q.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B)) :
        Set (↥B ⧸ N.subgroupOf B)) : Set (↥B ⧸ N.subgroupOf B)) * Nat.card N =
      Nat.card (Y ⊔ Q : Subgroup X) := by
  rw [← coe_mul_of_left_le_normalizer_right _ _ (by rw [normalizer_eq_top]; exact le_top)]
  change Nat.card ↥((Y.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B)) ⊔
    (Q.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B))) * Nat.card N = _
  rw [← Subgroup.map_sup, ← subgroupOf_sup hYB hQB]
  exact quotB_card_map_mul (hNY.trans le_sup_left) (sup_le hYB hQB)

theorem quotB_unique_iff (hNB : N ≤ B) (hN : Nat.card N = 2) {P : Subgroup X} (hNP : N ≤ P)
    (hPB : P ≤ B) {m : ℕ} (hP : Nat.card P = 2 ^ (m + 1)) (hPsq : ∀ x ∈ P, x ^ 2 ∈ N)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (huniq : ∀ Y : Subgroup X, N ≤ Y → Y ≤ B → Nat.card Y = 2 ^ (m + 1) →
      (∀ y ∈ Y, y ^ 2 ∈ N) → (∀ y ∈ Y, ∀ y' ∈ Y, y⁻¹ * y'⁻¹ * y * y' ∈ N) → Y = P) :
    ∀ Yb : Subgroup (↥B ⧸ N.subgroupOf B),
      (IsElementaryAbelian 2 Yb ∧ Nat.card Yb = 2 ^ m) ↔
        Yb = (P.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B)) := by
  intro Yb
  constructor
  · rintro ⟨hYe, hYc⟩
    obtain ⟨hNY, hYB, hYmap, hYsq⟩ := quotB_preimage_facts hNB Yb
    have hYcard : Nat.card ((Yb.comap (QuotientGroup.mk' (N.subgroupOf B))).map B.subtype) =
        2 ^ (m + 1) := by
      have h := quotB_card_map_mul hNY hYB
      rw [hYmap, hYc, hN] at h
      rw [← h, pow_succ]
    have hYP := huniq _ hNY hYB hYcard (hYsq hYe).1 (hYsq hYe).2
    rw [← hYmap, hYP]
  · rintro rfl
    refine ⟨quotB_isElementaryAbelian_map hPsq hPc, ?_⟩
    have h := quotB_card_map_mul hNP hPB
    rw [hP, hN, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem quotB_unique_prod_iff (hNB : N ≤ B) (hN : Nat.card N = 2) {P Q : Subgroup X}
    (hNP : N ≤ P) (hPB : P ≤ B) (hQB : Q ≤ B) (hBQ : B ≤ normalizer (Q : Set X)) {m k : ℕ}
    (hP : Nat.card P = 2 ^ (m + 1)) (hPsq : ∀ x ∈ P, x ^ 2 ∈ N)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hPQ : Nat.card (P ⊔ Q : Subgroup X) = 2 ^ (k + 1))
    (huniq : ∀ Y : Subgroup X, N ≤ Y → Y ≤ B → Nat.card Y = 2 ^ (m + 1) →
      (∀ y ∈ Y, y ^ 2 ∈ N) → (∀ y ∈ Y, ∀ y' ∈ Y, y⁻¹ * y'⁻¹ * y * y' ∈ N) →
      Nat.card (Y ⊔ Q : Subgroup X) = 2 ^ (k + 1) → Y = P) :
    ∀ Yb : Subgroup (↥B ⧸ N.subgroupOf B),
      (IsElementaryAbelian 2 Yb ∧ Nat.card Yb = 2 ^ m ∧
        Nat.card ((Yb : Set (↥B ⧸ N.subgroupOf B)) *
          ((Q.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B)) :
            Set (↥B ⧸ N.subgroupOf B)) : Set (↥B ⧸ N.subgroupOf B)) = 2 ^ k) ↔
        Yb = (P.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B)) := by
  have hQn : ((Q.subgroupOf B).map (QuotientGroup.mk' (N.subgroupOf B))).Normal :=
    ((normal_subgroupOf_iff_le_normalizer hQB).2 hBQ).map _ (QuotientGroup.mk'_surjective _)
  intro Yb
  constructor
  · rintro ⟨hYe, hYc, hYQ⟩
    obtain ⟨hNY, hYB, hYmap, hYsq⟩ := quotB_preimage_facts hNB Yb
    have hYcard : Nat.card ((Yb.comap (QuotientGroup.mk' (N.subgroupOf B))).map B.subtype) =
        2 ^ (m + 1) := by
      have h := quotB_card_map_mul hNY hYB
      rw [hYmap, hYc, hN] at h
      rw [← h, pow_succ]
    have hYQcard : Nat.card ((Yb.comap (QuotientGroup.mk' (N.subgroupOf B))).map B.subtype ⊔ Q :
        Subgroup X) = 2 ^ (k + 1) := by
      have h := quotB_card_mul_map_mul hNY hYB hQB
      rw [hYmap, hYQ, hN] at h
      rw [← h, pow_succ]
    have hYP := huniq _ hNY hYB hYcard (hYsq hYe).1 (hYsq hYe).2 hYQcard
    rw [← hYmap, hYP]
  · rintro rfl
    refine ⟨quotB_isElementaryAbelian_map hPsq hPc, ?_, ?_⟩
    · have h := quotB_card_map_mul hNP hPB
      rw [hP, hN, pow_succ] at h
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    · have h := quotB_card_mul_map_mul hNP hPB hQB
      rw [hPQ, hN, pow_succ] at h
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

end Generic

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

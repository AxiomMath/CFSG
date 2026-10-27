module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

theorem normalizer_sup_eq_top_of_odd {X : Type} [Group X] [Finite X] {V : Subgroup X}
    (hV : IsPGroup 2 V) {Nn : Subgroup X} [Nn.Normal] (hodd : Odd (Nat.card Nn))
    (hVN : (V ⊔ Nn).Normal) : normalizer (V : Set X) ⊔ Nn = ⊤ := by
  haveI : (V ⊔ Nn).Normal := hVN
  have hcop : Nat.Coprime (Nat.card V) (Nat.card Nn) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV
    rw [hk]
    exact (Nat.coprime_two_left.mpr hodd).pow_left k
  have hdisj : V ⊓ Nn = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hcardV : Nat.card (V.subgroupOf (V ⊔ Nn)) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : V ≤ V ⊔ Nn)).toEquiv
  have hcardN : Nat.card (Nn.subgroupOf (V ⊔ Nn)) = Nat.card Nn :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : Nn ≤ V ⊔ Nn)).toEquiv
  have hcompl : Subgroup.IsComplement' (V.subgroupOf (V ⊔ Nn))
      (Nn.subgroupOf (V ⊔ Nn)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff]
      show V.comap (V ⊔ Nn).subtype ⊓ Nn.comap (V ⊔ Nn).subtype = ⊥
      rw [← Subgroup.comap_inf, hdisj, MonoidHom.comap_bot, MonoidHom.ker_eq_bot_iff]
      exact (V ⊔ Nn).subtype_injective
    · rw [← Subgroup.mul_normal, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
        Subgroup.subgroupOf_self, Subgroup.coe_top]
  have hcardNsup : Nat.card ↥(V ⊔ Nn) = Nat.card V * Nat.card Nn := by
    have h := hcompl.card_mul_card
    rw [hcardV, hcardN] at h
    exact h.symm
  have hindex : (V.subgroupOf (V ⊔ Nn)).index = Nat.card Nn := by
    have hci := Subgroup.card_mul_index (V.subgroupOf (V ⊔ Nn))
    rw [hcardV, hcardNsup] at hci
    exact Nat.mul_left_cancel (Nat.card_pos (α := V)) hci
  have hoddidx : ¬ 2 ∣ (V.subgroupOf (V ⊔ Nn)).index := by
    rw [hindex]
    exact hodd.not_two_dvd_nat
  have hP : IsPGroup 2 (V.subgroupOf (V ⊔ Nn)) :=
    hV.comap_of_injective (V ⊔ Nn).subtype ((V ⊔ Nn).subtype_injective)
  let P : Sylow 2 ↥(V ⊔ Nn) := hP.toSylow hoddidx
  have hPmap : P.map (V ⊔ Nn).subtype = V := by
    change (V.subgroupOf (V ⊔ Nn)).map (V ⊔ Nn).subtype = V
    exact Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hFr := Sylow.normalizer_sup_eq_top P
  rw [hPmap] at hFr
  rwa [← sup_assoc, sup_of_le_left (Subgroup.le_normalizer)] at hFr

theorem isSubnormal_sup_of_sup_eq_top {X : Type} [Group X] {N' Nn A : Subgroup X} [Nn.Normal]
    (hN : N' ⊔ Nn = ⊤) (hA : A ≤ N') (hsub : (A.subgroupOf N').IsSubnormal) :
    (A ⊔ Nn).IsSubnormal := by
  let q : X →* X ⧸ Nn := QuotientGroup.mk' Nn
  let φ : ↥N' →* X ⧸ Nn := q.comp N'.subtype
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    have hrange : φ.range = N'.map q := by
      show (q.comp N'.subtype).range = N'.map q
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hmap_top : N'.map q = ⊤ := by
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective Nn)
      rw [QuotientGroup.comap_map_mk', Subgroup.comap_top, sup_comm, hN]
    rw [hrange, hmap_top]
  have hmap : (A.subgroupOf N').map φ = A.map q := by
    change (A.subgroupOf N').map (q.comp N'.subtype) = A.map q
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hA]
  have hsubq : (A.map q).IsSubnormal := by
    rw [← hmap]
    exact hsub.map hsurj
  have hmap_sup : (A ⊔ Nn).map q = A.map q := by
    show (A ⊔ Nn).map (QuotientGroup.mk' Nn) = A.map (QuotientGroup.mk' Nn)
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  rw [← hmap_sup] at hsubq
  have hker : q.ker ≤ A ⊔ Nn := by
    rw [show q.ker = Nn from QuotientGroup.ker_mk' Nn]
    exact le_sup_right
  have h := hsubq.comap q
  rwa [Subgroup.comap_map_eq_self hker] at h

theorem caseA_subnormal {X : Type} [Group X] [Finite X] {V : Subgroup X} (hV : IsPGroup 2 V)
    {Nn : Subgroup X} [Nn.Normal] (hodd : Odd (Nat.card Nn)) (hVN : (V ⊔ Nn).Normal)
    {A : Subgroup X} (hA : A ≤ normalizer (V : Set X))
    (hsub : (A.subgroupOf (normalizer (V : Set X))).IsSubnormal) : (A ⊔ Nn).IsSubnormal := by
  exact isSubnormal_sup_of_sup_eq_top (normalizer_sup_eq_top_of_odd hV hodd hVN) hA hsub

end CFSG.OddStandard.SmallF3.Omega

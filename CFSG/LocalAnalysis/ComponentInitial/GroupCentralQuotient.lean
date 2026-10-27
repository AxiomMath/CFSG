module

public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G]

theorem index_center_eq_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (center H).index = (center K).index := by
  rw [← map_center_eq e, ← index_map_equiv (center H) e]

theorem index_center_lt_of_lt_top {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    {A : Subgroup B} (hA : A < ⊤) : (center A).index < (center B).index := by
  let π : A →* B ⧸ center B := (QuotientGroup.mk' (center B)).comp A.subtype
  have hker : π.ker ≤ center A := by
    intro x hx
    have hxZ : (x : B) ∈ center B := (QuotientGroup.eq_one_iff _).mp hx
    exact mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp hxZ g)
  have hle : (center A).index ≤ Nat.card π.range := by
    rw [← index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite) (index_dvd_of_le hker)
  have hrange : π.range = A.map (QuotientGroup.mk' (center B)) := by
    rw [MonoidHom.range_comp, range_subtype]
  have hlt : π.range < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => (lt_top_iff_ne_top.mp hA) ?_
    have hsup : A ⊔ center B = ⊤ := by
      have h := comap_map_eq (QuotientGroup.mk' (center B)) A
      rwa [QuotientGroup.ker_mk', ← hrange, htop, comap_top, eq_comm] at h
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central A (center B)
      le_rfl
    rw [hsup, ← commutator_def, Group.IsPerfect.commutator_eq_top] at h
    exact eq_top_iff.mpr (h.le.trans A.commutator_le_self)
  calc (center A).index ≤ Nat.card π.range := hle
    _ < Nat.card (⊤ : Subgroup (B ⧸ center B)) := card_lt_of_lt hlt
    _ = (center B).index := by rw [card_top, index_eq_card]

theorem index_center_lt_of_lt [Finite G] {A B : Subgroup G} [Group.IsPerfect B] (hAB : A < B) :
    (center A).index < (center B).index := by
  have hA : A.subgroupOf B < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact not_le_of_gt hAB
  rw [index_center_eq_of_mulEquiv (subgroupOfEquivOfLe hAB.le).symm]
  exact index_center_lt_of_lt_top hA

theorem card_quotient_center_mul_dvd {L : Type*} [Group L] [Finite L] {J K A : Subgroup L}
    (hJK : ⁅J, K⁆ = ⊥) (hA : A ≤ center L) :
    Nat.card (J ⧸ center J) * Nat.card (K ⧸ center K) ∣ Nat.card (L ⧸ A) := by
  have : A.Normal := normal_of_le_center hA
  have hcomm : ∀ j ∈ J, ∀ k ∈ K, j * k = k * j := fun j hj k hk =>
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hJK hj) k hk).symm
  let f : J × K →* L := J.subtype.noncommCoprod K.subtype fun j k => hcomm j j.2 k k.2
  let ψ : J × K →* L ⧸ A := (QuotientGroup.mk' A).comp f
  have hker : ψ.ker ≤ (center J).prod (center K) := by
    rintro ⟨j, k⟩ hjk
    have hc : (j : L) * k ∈ center L := hA ((QuotientGroup.eq_one_iff _).mp hjk)
    refine ⟨mem_center_iff.mpr fun g => Subtype.ext ?_, mem_center_iff.mpr fun g => Subtype.ext ?_⟩
    · have h := mem_center_iff.mp hc g
      have hgk := hcomm g g.2 k k.2
      change (g : L) * j = j * g
      apply mul_right_cancel (b := (k : L))
      calc (g : L) * j * k = g * (j * k) := mul_assoc _ _ _
        _ = j * k * g := h
        _ = j * (k * g) := mul_assoc _ _ _
        _ = j * g * k := by rw [← hgk, mul_assoc]
    · have h := mem_center_iff.mp hc g
      have hjg := hcomm j j.2 g g.2
      change (g : L) * k = k * g
      apply mul_left_cancel (a := (j : L))
      calc (j : L) * (g * k) = j * g * k := (mul_assoc _ _ _).symm
        _ = g * (j * k) := by rw [hjg, mul_assoc]
        _ = j * k * g := h
        _ = j * (k * g) := mul_assoc _ _ _
  have hdvd := index_dvd_of_le hker
  rw [index_prod, index_ker] at hdvd
  exact hdvd.trans (card_subgroup_dvd_card ψ.range)

theorem card_quotient_center_sq_dvd {L : Type*} [Group L] [Finite L] {J K A : Subgroup L}
    (hJK : ⁅J, K⁆ = ⊥) (hA : A ≤ center L)
    (hcard : Nat.card (J ⧸ center J) = Nat.card (K ⧸ center K)) :
    Nat.card (J ⧸ center J) ^ 2 ∣ Nat.card (L ⧸ A) := by
  rw [sq]
  nth_rw 2 [hcard]
  exact card_quotient_center_mul_dvd hJK hA

theorem commuting_quasisimple_factors_central_quotient_divisor {L : Type*} [Group L] [Finite L]
    {J K A : Subgroup L} (_hJ : CFSG.Assembly.IsQuasisimple J)
    (_hK : CFSG.Assembly.IsQuasisimple K) (hJK : ⁅J, K⁆ = ⊥) (hA : A ≤ center L) :
    Nat.card (J ⧸ center J) * Nat.card (K ⧸ center K) ∣ Nat.card (L ⧸ A) ∧
      (Nonempty (J ⧸ center J ≃* K ⧸ center K) →
        Nat.card (J ⧸ center J) ^ 2 ∣ Nat.card (L ⧸ A)) :=
  ⟨card_quotient_center_mul_dvd hJK hA, fun ⟨e⟩ =>
    card_quotient_center_sq_dvd hJK hA (Nat.card_congr e.toEquiv)⟩

end CFSG.LocalAnalysis.ComponentInitial

module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleB
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

variable {T : Type} [Group T] [Finite T]

theorem card_quot_center_mul_dvd_card_of_commute {X Y : Subgroup T} (hXY : ⁅X, Y⁆ = ⊥) :
    Nat.card (↥X ⧸ center ↥X) * Nat.card (↥Y ⧸ center ↥Y) ∣ Nat.card T := by
  have hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := fun x hx y hy =>
    sig_mul_comm_of_commutator_eq_bot hXY hx hy
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X Y hc).1
  have hX := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥X)
  have hY := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥Y)
  have hdvd : Nat.card ↥(X ⊓ Y) ∣ Nat.card ↥(center ↥X) := by
    have hle : (X ⊓ Y).subgroupOf X ≤ center ↥X := fun z hz => by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2 z (mem_subgroupOf.mp hz).2)
    have h2 : Nat.card ↥((X ⊓ Y).subgroupOf X) = Nat.card ↥(X ⊓ Y) := by
      rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_comm, ← inf_assoc, inf_idem]
    rw [← h2]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Nat.card ↥(X ⊓ Y) := Nat.card_pos
  have h3 : Nat.card ↥(X ⊔ Y) =
      Nat.card (↥X ⧸ center ↥X) * Nat.card (↥Y ⧸ center ↥Y) * (m * Nat.card ↥(center ↥Y)) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, hX, hY, hm]
    ring
  exact (Dvd.intro _ h3.symm).trans (Subgroup.card_dvd_of_le le_top |>.trans
    (by rw [Subgroup.card_top]))

theorem singleComponentCleanAt_of_card {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → P T →
      ∀ (y₁ y₂ : T) (K₁ K₂ : Subgroup T), orderOf y₁ = 2 → orderOf y₂ = 2 →
      IsTwoComponentIn K₁ (centralizer ({y₁} : Set T)) →
      IsTwoComponentIn K₂ (centralizer ({y₂} : Set T)) →
      CFSG.IsQuasisimple K₁ → CFSG.IsQuasisimple K₂ →
      2 ≤ CFSG.Open.pRank 2 K₁ → 2 ≤ CFSG.Open.pRank 2 K₂ →
      ¬ Nat.card (↥K₁ ⧸ center ↥K₁) * Nat.card (↥K₂ ⧸ center ↥K₂) ∣ Nat.card T) :
    SingleComponentCleanAt P := by
  intro T _ _ hT hP X Y hXq hYq hXr hYr hXY hXc hYc
  obtain ⟨y, hyY, hy2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hYr)
  obtain ⟨x, hxX, hx2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hXr)
  exact h T hT hP y x X Y hy2 hx2 (hXc y hyY hy2) (hYc x hxX hx2) hXq hYq hXr hYr
    (card_quot_center_mul_dvd_card_of_commute hXY)

theorem singleComponentCleanAt_of_solvable {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → P T →
      ∀ (y : T) (K : Subgroup T), orderOf y = 2 → IsTwoComponentIn K (centralizer ({y} : Set T)) →
      CFSG.IsQuasisimple K → 2 ≤ CFSG.Open.pRank 2 K →
      Group.IsSolvable ↥(centralizer (K : Set T))) :
    SingleComponentCleanAt P := by
  intro T _ _ hT hP X Y hXq hYq hXr hYr hXY hXc hYc
  obtain ⟨y, hyY, hy2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hYr)
  have hsolv := h T hT hP y X hy2 (hXc y hyY hy2) hXq hXr
  have hYC : Y ≤ centralizer (X : Set T) := fun g hg => mem_centralizer_iff.mpr fun x hx =>
    sig_mul_comm_of_commutator_eq_bot hXY hx hg
  have : Group.IsSolvable ↥Y := Group.isSolvable_of_isSolvable_injective (inclusion_injective hYC)
  exact sig_not_isSolvable_of_isQuasisimple hYq this

end CFSG.ComponentClassification.Sol76.Sig

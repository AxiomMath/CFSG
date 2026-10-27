module

public import CFSG.LocalAnalysis.SteinbergCEFaithfulSuzukiSocle
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

namespace SteinbergCH

theorem lieModel_twistedB2_iff (X : Type) [Group X] (p f : ℕ) :
    CFSG.Blueprint.LieModel X .twistedB2 0 p f ↔ CFSG.Blueprint.SuzukiModel X p f :=
  CFSG.Blueprint.LieModel.twistedB2_iff.trans (and_iff_right rfl)

theorem isComponentOf_centralizer_of_eq_sup {Y : Type*} [Group Y] {a : Y} {J : Subgroup Y}
    (hJq : CFSG.Assembly.IsQuasisimple J) (hJa : J ≤ centralizer ({a} : Set Y))
    (hC : centralizer ({a} : Set Y) = zpowers a ⊔ J) :
    CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set Y)) := by
  have hnorm : centralizer ({a} : Set Y) ≤ normalizer (J : Set Y) := by
    rw [hC]
    refine sup_le ?_ le_normalizer
    rw [zpowers_le, mem_normalizer_iff]
    intro j
    constructor
    · intro hj
      have hja : a * j = j * a := (mem_centralizer_iff.mp (hJa hj)) a rfl
      rwa [hja, mul_inv_cancel_right]
    · intro hj
      have hxa : a * (a * j * a⁻¹) = (a * j * a⁻¹) * a :=
        (mem_centralizer_iff.mp (hJa hj)) a rfl
      have hj' : j = a * j * a⁻¹ := by
        calc j = a⁻¹ * ((a * j * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * j * a⁻¹)) := by rw [← hxa]
          _ = a * j * a⁻¹ := by group
      rw [hj']
      exact hj
  exact ⟨hJa, CFSG.Assembly.IsSubnormal.step hJa
    ((normal_subgroupOf_iff_le_normalizer hJa).mpr hnorm)
    (CFSG.Assembly.IsSubnormal.refl _), hJq⟩

theorem layer_not_suzukiModel {Y : Type} [Group Y] [Finite Y] {D : Subgroup Y} [D.Normal]
    (hDs : IsSimpleGroup D) (hDn : ∃ x y : D, x * y ≠ y * x)
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
    (hJD : J ≤ D) (hJq : CFSG.Assembly.IsQuasisimple J) (hJa : J ≤ centralizer ({a} : Set Y))
    (hC : centralizer ({a} : Set Y) = zpowers a ⊔ J) :
    ∀ p f : ℕ, ¬ CFSG.Blueprint.SuzukiModel D p f ∧
      ¬ CFSG.Blueprint.LieModel D .twistedB2 0 p f := by
  intro p f
  have h := CFSG.LocalAnalysis.faithful_Suzuki_socle_involution_component_exclusion hDs hDn hCD
    ha hJD (isComponentOf_centralizer_of_eq_sup hJq hJa hC) p f
  exact ⟨h, fun h' => h ((lieModel_twistedB2_iff D p f).mp h')⟩

end SteinbergCH

end CFSG.LocalAnalysis.ComponentInitial

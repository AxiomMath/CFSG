module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIE6Coord
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

variable {F : Type} [Field F]

theorem uSL_mul_conj_ne [CharP F 2] {e : F} (he : e ≠ 0) :
    uSL e * (vSL 1 * uSL e * (vSL 1)⁻¹) ≠ vSL 1 * uSL e * (vSL 1)⁻¹ * uSL e := by
  intro h
  have h00 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_uSL,
    coe_vSL, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h00
  simp at h00
  exact he h00

theorem SL2_eq_one_of_commute [CharP F 2] (g : SL2 F) (hu : g * uSL 1 = uSL 1 * g)
    (hv : g * vSL 1 = vSL 1 * g) : g = 1 := by
  have hd := det_SL2 g
  have e1 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) hu
  have e2 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hu
  have e3 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, Matrix.mul_apply,
    Fin.sum_univ_two] at e1 e2 e3
  simp at e1 e2 e3
  have e2' : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -e2
  rw [e1, e3, e2', mul_zero, sub_zero] at hd
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have h' : ((g : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) *
        ((g : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) = 0 := by
      linear_combination hd + ((g : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) * h2
    have := mul_self_eq_zero.mp h'
    linear_combination this - h2
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using ha
  · simpa using e3
  · simpa using e1
  · simpa [e2'] using ha

theorem isRoot_e6Alpha
    (j : Bool) :
    IsRoot TwistTag.E6.tag (e6Alpha j) :=
  isRoot_single _ _

theorem e6Alpha_facts
    (s t : Bool) :
    (if s then -e6Alpha false else e6Alpha false) ≠
        (if t then -e6Alpha true else e6Alpha true) ∧
      (if s then -e6Alpha false else e6Alpha false) ≠
        -(if t then -e6Alpha true else e6Alpha true) ∧
      ¬IsRoot TwistTag.E6.tag ((if s then -e6Alpha false else e6Alpha false) +
        (if t then -e6Alpha true else e6Alpha true)) := by
  have key : ∀ s t : Bool, (if s then -e6Alpha false else e6Alpha false) ≠
        (if t then -e6Alpha true else e6Alpha true) ∧
      (if s then -e6Alpha false else e6Alpha false) ≠
        -(if t then -e6Alpha true else e6Alpha true) ∧
      e6RootB ((if s then -e6Alpha false else e6Alpha false) +
        (if t then -e6Alpha true else e6Alpha true)) = false := by decide
  obtain ⟨h1, h2, h3⟩ := key s t
  refine ⟨h1, h2, fun hr => ?_⟩
  rw [isRoot_iff_e6RootB, h3] at hr
  exact Bool.false_ne_true hr

theorem rootSubgroup_e6Alpha_le_centralizer
    (s t : Bool) :
    rootSubgroup TwistTag.E6.tag F (if s then -e6Alpha false else e6Alpha false) ≤
      centralizer (rootSubgroup TwistTag.E6.tag F
        (if t then -e6Alpha true else e6Alpha true) : Set (ModGL TwistTag.E6.tag F)) := by
  obtain ⟨hne, hne', hnr⟩ := e6Alpha_facts s t
  have hα : IsRoot TwistTag.E6.tag (if s then -e6Alpha false else e6Alpha false) := by
    cases s
    · exact isRoot_e6Alpha false
    · exact isRoot_neg_iff.2 (isRoot_e6Alpha false)
  have hβ : IsRoot TwistTag.E6.tag (if t then -e6Alpha true else e6Alpha true) := by
    cases t
    · exact isRoot_e6Alpha true
    · exact isRoot_neg_iff.2 (isRoot_e6Alpha true)
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact ((simply_laced_root_commutator_unit TwistTag.E6.tag (.inr (.inl rfl)) hα hβ hne hne').2
    hnr F x hx y hy).eq.symm

theorem range_rootSL2_le_centralizer [CharP F 2]
    : (rootSL2 TwistTag.E6.tag F (e6Alpha false)).range ≤
      centralizer ((rootSL2 TwistTag.E6.tag F (e6Alpha true)).range :
        Set (ModGL TwistTag.E6.tag F)) := by
  rw [(CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps TwistTag.E6.tag F
      (isRoot_e6Alpha false)).2.1,
    (CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps TwistTag.E6.tag F
      (isRoot_e6Alpha true)).2.1]
  refine sup_le ?_ ?_ <;> rw [le_centralizer_iff] <;> refine sup_le ?_ ?_ <;>
    rw [le_centralizer_iff]
  · exact rootSubgroup_e6Alpha_le_centralizer false false
  · exact rootSubgroup_e6Alpha_le_centralizer false true
  · exact rootSubgroup_e6Alpha_le_centralizer true false
  · exact rootSubgroup_e6Alpha_le_centralizer true true

theorem e6Alpha_pair_not_commute [CharP F 2]
    {e : F} (he : e ≠ 0) :
    pinnedX TwistTag.E6.tag F (e6Alpha false) e * pinnedX TwistTag.E6.tag F (e6Alpha true) e *
        ((pinnedX TwistTag.E6.tag F (-e6Alpha false) 1 *
            pinnedX TwistTag.E6.tag F (-e6Alpha true) 1) *
          (pinnedX TwistTag.E6.tag F (e6Alpha false) e *
            pinnedX TwistTag.E6.tag F (e6Alpha true) e) *
          (pinnedX TwistTag.E6.tag F (-e6Alpha false) 1 *
            pinnedX TwistTag.E6.tag F (-e6Alpha true) 1)⁻¹) ≠
      (pinnedX TwistTag.E6.tag F (-e6Alpha false) 1 *
          pinnedX TwistTag.E6.tag F (-e6Alpha true) 1) *
        (pinnedX TwistTag.E6.tag F (e6Alpha false) e *
          pinnedX TwistTag.E6.tag F (e6Alpha true) e) *
        (pinnedX TwistTag.E6.tag F (-e6Alpha false) 1 *
          pinnedX TwistTag.E6.tag F (-e6Alpha true) 1)⁻¹ *
        (pinnedX TwistTag.E6.tag F (e6Alpha false) e *
          pinnedX TwistTag.E6.tag F (e6Alpha true) e) := by
  set ρ₁ := rootSL2 TwistTag.E6.tag F (e6Alpha false)
  set ρ₆ := rootSL2 TwistTag.E6.tag F (e6Alpha true)
  obtain ⟨hinj₁, -, -, hgen₁, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps TwistTag.E6.tag F
      (isRoot_e6Alpha false)
  obtain ⟨-, -, -, hgen₆, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps TwistTag.E6.tag F
      (isRoot_e6Alpha true)
  have hcomm : ∀ A B, Commute (ρ₁ A) (ρ₆ B) := fun A B =>
    (mem_centralizer_iff.mp (range_rootSL2_le_centralizer ⟨A, rfl⟩) (ρ₆ B) ⟨B, rfl⟩).symm
  set Φ := MonoidHom.noncommCoprod ρ₁ ρ₆ hcomm
  have hΦ : ∀ A B, Φ (A, B) = ρ₁ A * ρ₆ B := fun A B => rfl
  set u := uSL e
  set v : SL2 F := vSL 1
  have hw : pinnedX TwistTag.E6.tag F (e6Alpha false) e *
      pinnedX TwistTag.E6.tag F (e6Alpha true) e = Φ (u, u) := by
    rw [hΦ, (hgen₁ e).1, (hgen₆ e).1]
  have hy : pinnedX TwistTag.E6.tag F (-e6Alpha false) 1 *
      pinnedX TwistTag.E6.tag F (-e6Alpha true) 1 = Φ (v, v) := by
    rw [hΦ, (hgen₁ 1).2, (hgen₆ 1).2]
  rw [hw, hy, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  intro h
  set s := v * u * v⁻¹
  have hx : Φ (((s * u)⁻¹ * (u * s)), ((s * u)⁻¹ * (u * s))) = 1 := by
    have e1 : ((s * u)⁻¹ * (u * s), (s * u)⁻¹ * (u * s)) =
        ((v, v) * (u, u) * (v, v)⁻¹ * (u, u))⁻¹ * ((u, u) * ((v, v) * (u, u) * (v, v)⁻¹)) := by
      simp only [Prod.mk_mul_mk, Prod.inv_mk, s]
    rw [e1, map_mul, map_inv, h, inv_mul_cancel]
  set x := (s * u)⁻¹ * (u * s) with hxdef
  clear_value x
  rw [hΦ] at hx
  have hx' : ρ₁ x = (ρ₆ x)⁻¹ := eq_inv_of_mul_eq_one_left hx
  have hcx : ∀ A, x * A = A * x := fun A => by
    apply hinj₁
    rw [map_mul, map_mul, hx', ← map_inv]
    exact (hcomm A x⁻¹).eq.symm
  have hx1 : x = 1 := SL2_eq_one_of_commute x (hcx _) (hcx _)
  apply uSL_mul_conj_ne he
  have : u * s = s * u := by
    have := congrArg (fun z => s * u * z) hx1
    rw [hxdef] at this
    simpa [mul_assoc] using this
  exact this

end CFSG.ComponentClassification.RankTwoExcHypII

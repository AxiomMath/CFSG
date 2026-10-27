module

public import CFSG.GH74.QTGen4.Recog.G23.Words
public import CFSG.GH74.QTGen4.Recog.G23.HK2
public import CFSG.GH74.QTGen4.Recog.G23.HSL
public meta import CFSG.GH74.QTGen4.Recog.G23.HSL
public meta import Mathlib.GroupTheory.Nilpotent
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.GH74.QTGen4.Recog.G23

variable {X : Type*} [Group X]

theorem hl_lift_nil (ρ : Fin 6 → X) : FreeGroup.lift ρ (FreeGroup.mk []) = 1 := by
  rw [← FreeGroup.one_eq_mk, map_one]

theorem hl_lift_letter (ρ : Fin 6 → X) (i : Fin 6) (b : Bool) :
    FreeGroup.lift ρ (FreeGroup.mk [(i, b)]) = if b then ρ i else (ρ i)⁻¹ := by
  cases b
  · have : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := rfl
    rw [this, map_inv]
    simp
  · have : FreeGroup.mk [(i, true)] = FreeGroup.of i := rfl
    rw [this]
    simp

theorem hl_lift_cons (ρ : Fin 6 → X) (l : Fin 6 × Bool) (L : List (Fin 6 × Bool)) :
    FreeGroup.lift ρ (FreeGroup.mk (l :: L)) =
      (if l.2 then ρ l.1 else (ρ l.1)⁻¹) * FreeGroup.lift ρ (FreeGroup.mk L) := by
  obtain ⟨i, b⟩ := l
  rw [show (i, b) :: L = [(i, b)] ++ L from rfl, ← FreeGroup.mul_mk, map_mul,
    hl_lift_letter]

theorem hl_comm_rel {a b : X} (h : Commute a b) : a⁻¹ * b⁻¹ * a * b = 1 := by
  have h' : a⁻¹ * b⁻¹ * a * b = (b * a)⁻¹ * (a * b) := by group
  rw [h', h.eq, inv_mul_cancel]

theorem satisfiesWords_g23WordsH_of_relations (e : Fin 6 → X)
    (hA : e 0 * e 0 * e 0 = 1) (hB : e 1 * e 1 * e 1 = 1)
    (hC : (e 1)⁻¹ * (e 0)⁻¹ * e 1 * (e 0)⁻¹ * (e 1)⁻¹ * e 0 = 1)
    (hD : e 2 * e 2 * e 2 = 1) (hE : e 3 * e 3 * e 3 = 1)
    (hF : (e 3)⁻¹ * (e 2)⁻¹ * e 3 * (e 2)⁻¹ * (e 3)⁻¹ * e 2 = 1)
    (hG : e 0 * e 1 * (e 0 * e 1) = e 2 * e 3 * (e 2 * e 3))
    (h02 : Commute (e 0) (e 2)) (h03 : Commute (e 0) (e 3))
    (h12 : Commute (e 1) (e 2)) (h13 : Commute (e 1) (e 3))
    (h4 : e 4 * e 4 = 1)
    (h40 : e 4 * e 0 * (e 4 * e 0) = 1) (h41 : e 4 * e 1 * (e 4 * e 1) = 1)
    (h42 : e 4 * e 2 * (e 4 * e 2) = 1) (h43 : e 4 * e 3 * (e 4 * e 3) = 1) :
    SatisfiesWords g23WordsH e := by
  have hG' : e 0 * e 1 * (e 0 * e 1) * ((e 3)⁻¹ * (e 2)⁻¹ * ((e 3)⁻¹ * (e 2)⁻¹)) = 1 := by
    rw [show (e 3)⁻¹ * (e 2)⁻¹ * ((e 3)⁻¹ * (e 2)⁻¹) = (e 2 * e 3 * (e 2 * e 3))⁻¹ by group, hG,
      mul_inv_cancel]
  intro r hr
  simp only [g23WordsH, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals simp only [hl_lift_cons, hl_lift_nil, mul_one, Bool.false_eq_true, ite_true,
    ite_false]
  · simpa only [mul_assoc] using hA
  · simpa only [mul_assoc] using hB
  · simpa only [mul_assoc] using hC
  · simpa only [mul_assoc] using hD
  · simpa only [mul_assoc] using hE
  · simpa only [mul_assoc] using hF
  · simpa only [mul_assoc] using hG'
  · simpa only [mul_assoc] using hl_comm_rel h02
  · simpa only [mul_assoc] using hl_comm_rel h03
  · simpa only [mul_assoc] using hl_comm_rel h12
  · simpa only [mul_assoc] using hl_comm_rel h13
  · simpa only [mul_assoc] using h4
  · simpa only [mul_assoc] using h40
  · simpa only [mul_assoc] using h41
  · simpa only [mul_assoc] using h42
  · simpa only [mul_assoc] using h43

open CFSG.Quasithin.G23Type

section SLLetters

variable {G : Type} [Group G]

@[expose] def slX : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨mx, by rw [mx_eq]; decide +kernel⟩

@[expose] def slY : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨my, by rw [my_eq]; decide +kernel⟩

@[expose] def slXi : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨mxi, by rw [mxi_eq]; decide +kernel⟩

@[expose] def slYi : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨myi, by rw [myi_eq]; decide +kernel⟩

def slZ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨-1, by decide +kernel⟩

theorem slX_val : slX.1 = mx := rfl

theorem slY_val : slY.1 = my := rfl

theorem slXi_val : slXi.1 = mxi := rfl

theorem slYi_val : slYi.1 = myi := rfl

theorem slX_inv : slX⁻¹ = slXi :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (show mx * mxi = 1 by rw [mx_eq, mxi_eq]; decide +kernel))

theorem slY_inv : slY⁻¹ = slYi :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (show my * myi = 1 by rw [my_eq, myi_eq]; decide +kernel))

theorem sl_letter_rels :
    slX * slX * slX = 1 ∧ slY * slY * slY = 1 ∧
      slY⁻¹ * slX⁻¹ * slY * slX⁻¹ * slY⁻¹ * slX = 1 ∧ slX * slY * (slX * slY) = slZ := by
  obtain ⟨h1, h2, h3⟩ := sl_rel_x
  refine ⟨Subtype.ext h1, Subtype.ext h2, ?_, Subtype.ext sl_xy_sq⟩
  rw [slY_inv, slX_inv]
  exact Subtype.ext h3

theorem invol_eq_slZ {Y : Subgroup G} (ψ : ↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    {z : G} (hzY : z ∈ Y) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) : ψ ⟨z, hzY⟩ = slZ := by
  have hzz : (⟨z, hzY⟩ : ↥Y) * ⟨z, hzY⟩ = 1 :=
    Subtype.ext (show z * z = 1 by rw [← pow_two]; exact hz2)
  have hAA : ψ ⟨z, hzY⟩ * ψ ⟨z, hzY⟩ = 1 := by rw [← map_mul, hzz, map_one]
  have hA1 : ψ ⟨z, hzY⟩ ≠ 1 := fun h =>
    hz1 (congrArg Subtype.val (ψ.injective (h.trans (map_one ψ).symm)))
  exact Subtype.ext (sl_unique_invol (ψ ⟨z, hzY⟩).1 (ψ ⟨z, hzY⟩).2
    (congrArg Subtype.val hAA) (fun h => hA1 (Subtype.ext h)))

end SLLetters

end CFSG.GH74.QTGen4.Recog.G23

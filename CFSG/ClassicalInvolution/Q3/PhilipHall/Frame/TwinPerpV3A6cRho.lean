module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cConj

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3

section Rho

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)}

theorem mul_isConj {n : ℕ} (I : AEIdent P n) {a b : G} (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P)
    (hb : ∀ y ∈ pSpan P, b * y * b⁻¹ ∈ pSpan P) {x x' : AE.AEQ n} (h : IsConj I a x)
    (h' : IsConj I b x') : IsConj I (a * b) (x * x') := by
  intro y hy hy'
  have e : (⟨a * b * y * (a * b)⁻¹, hy'⟩ : pSpan P) =
      ⟨a * (b * y * b⁻¹) * a⁻¹, ha _ (hb y hy)⟩ := Subtype.ext (by group)
  rw [e, h (b * y * b⁻¹) (hb y hy) (ha _ (hb y hy)), h' y hy (hb y hy)]
  group

theorem isConj_self {n : ℕ} (I : AEIdent P n) {y : G} (hy : y ∈ pSpan P) :
    IsConj I y (I.φ ⟨y, hy⟩) := by
  intro w hw hw'
  have e : (⟨y * w * y⁻¹, hw'⟩ : ↥(pSpan P)) = ⟨y, hy⟩ * ⟨w, hw⟩ * ⟨y, hy⟩⁻¹ := Subtype.ext (by simp)
  rw [e, map_mul, map_mul, map_inv]

structure RhoSpec (I : AEIdent P 6) (C : Subgroup G) (ρ : G → AE.AEQ 6) : Prop where
  conj : ∀ g ∈ C, IsConj I g (ρ g)
  mul : ∀ g ∈ C, ∀ h ∈ C, ρ (g * h) = ρ g * ρ h
  one : ρ 1 = 1
  onSpan : ∀ (y : G) (hy : y ∈ pSpan P), ρ y = I.φ ⟨y, hy⟩

theorem exists_rhoSpec (I : AEIdent P 6) (C : Subgroup G) (hP : pSpan P ≤ C)
    (hperm : ∀ g ∈ C, ∀ L ∈ P, conjSub g L ∈ P) : ∃ ρ : G → AE.AEQ 6, RhoSpec I C ρ := by
  classical
  have hn5 : 5 ≤ 6 := by norm_num
  have hex : ∀ g ∈ C, ∃ x : AE.AEQ 6, IsConj I g x := by
    intro g hg
    obtain ⟨x, hx⟩ := exists_conj hn5 I (conj_mem (hperm g hg)) (conj_mem (hperm g⁻¹ (C.inv_mem hg)))
      (hperm g hg)
    exact ⟨x, fun y hy hy' => hx y hy hy'⟩
  let ρ : G → AE.AEQ 6 := fun g => if hg : g ∈ C then Classical.choose (hex g hg) else 1
  have hρ : ∀ g (hg : g ∈ C), IsConj I g (ρ g) := fun g hg => by
    simp only [ρ, dif_pos hg]
    exact Classical.choose_spec (hex g hg)
  have hmem : ∀ g ∈ C, ∀ y ∈ pSpan P, g * y * g⁻¹ ∈ pSpan P := fun g hg => conj_mem (hperm g hg)
  refine ⟨ρ, ⟨hρ, ?_, ?_, ?_⟩⟩
  · intro g hg h hh
    exact eq_of_isConj hn5 I (hmem _ (C.mul_mem hg hh)) (hρ _ (C.mul_mem hg hh))
      (mul_isConj I (hmem g hg) (hmem h hh) (hρ g hg) (hρ h hh))
  · refine eq_of_isConj hn5 I (hmem 1 C.one_mem) (hρ 1 C.one_mem) (one_isConj I)
  · intro y hy
    exact eq_of_isConj hn5 I (hmem y (hP hy)) (hρ y (hP hy)) (isConj_self I hy)

end Rho

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

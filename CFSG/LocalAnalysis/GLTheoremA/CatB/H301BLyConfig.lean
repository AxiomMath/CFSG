module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

open Equiv Equiv.Perm MulAction Subgroup

variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem inv_apply' (f : Perm X) (x : X) : f⁻¹ (f x) = x := f.symm_apply_apply x

private theorem apply_inv' (f : Perm X) (x : X) : f (f⁻¹ x) = x := f.apply_symm_apply x

def setStab (S : Set X) : Subgroup (Perm X) where
  carrier := {e | ∀ x, e x ∈ S ↔ x ∈ S}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {e f} he hf x => by
    show e (f x) ∈ S ↔ x ∈ S
    rw [he, hf]
  inv_mem' := fun {e} he x => by
    show e⁻¹ x ∈ S ↔ x ∈ S
    rw [← he (e⁻¹ x), apply_inv']

theorem mem_setStab {S : Set X} {e : Perm X} : e ∈ setStab S ↔ ∀ x, e x ∈ S ↔ x ∈ S := Iff.rfl

structure Config (E : Subgroup (Perm X)) where
  p : X
  q : X
  a : Fin 3 → Perm X
  p_ne_q : p ≠ q
  a_mem : ∀ i, a i ∈ E
  a_cube : ∀ i, a i ^ 3 = 1
  supp_card : ∀ i, (a i).support.card = 3
  disj : ∀ i j, i ≠ j → Disjoint (a i).support (a j).support
  fix_p : ∀ e ∈ E, e p = p
  fix_q : ∀ e ∈ E, e q = q
  cover : ∀ x, x ≠ p → x ≠ q → ∃ i, x ∈ (a i).support

namespace Config

variable {E : Subgroup (Perm X)} (c : Config E)

theorem fix_of_notMem {i : Fin 3} {x : X} (hx : x ∉ (c.a i).support) : c.a i x = x :=
  notMem_support.1 hx

theorem ne_of_mem {i : Fin 3} {x : X} (hx : x ∈ (c.a i).support) : c.a i x ≠ x :=
  mem_support.1 hx

theorem mem_inj {i j : Fin 3} {x : X} (hi : x ∈ (c.a i).support) (hj : x ∈ (c.a j).support) :
    i = j := by
  by_contra h
  exact Finset.disjoint_left.1 (c.disj i j h) hi hj

theorem p_notMem (i : Fin 3) : c.p ∉ (c.a i).support := fun h =>
  c.ne_of_mem h (c.fix_p _ (c.a_mem i))

theorem q_notMem (i : Fin 3) : c.q ∉ (c.a i).support := fun h =>
  c.ne_of_mem h (c.fix_q _ (c.a_mem i))

theorem eq_of_fixed {x : X} (hx : ∀ e ∈ E, e x = x) : x = c.p ∨ x = c.q := by
  by_contra h
  obtain ⟨h1, h2⟩ := not_or.1 h
  obtain ⟨i, hi⟩ := c.cover x h1 h2
  exact c.ne_of_mem hi (hx _ (c.a_mem i))

theorem support_eq (i : Fin 3) {z : X} (hz : z ∈ (c.a i).support) :
    (c.a i).support = {z, c.a i z, c.a i (c.a i z)} :=
  support_eq_of_three (c.a_cube i) (c.supp_card i) (c.ne_of_mem hz)

end Config

theorem card_modEq_fix {F : Subgroup (Perm X)} {p : ℕ} [Fact p.Prime] (hF : IsPGroup p F)
    (S : Set X) (hS : ∀ f ∈ F, ∀ x ∈ S, f x ∈ S) :
    Nat.card S ≡ Nat.card {x : X // x ∈ S ∧ ∀ f ∈ F, f x = x} [MOD p] := by
  letI : MulAction F S :=
    { smul := fun f s => ⟨(f : Perm X) s.1, hS f f.2 s.1 s.2⟩
      one_smul := fun s => Subtype.ext rfl
      mul_smul := fun f g s => Subtype.ext rfl }
  have h := hF.card_modEq_card_fixedPoints S
  have e : Nat.card (fixedPoints F S) = Nat.card {x : X // x ∈ S ∧ ∀ f ∈ F, f x = x} :=
    Nat.card_congr
      { toFun := fun s => ⟨s.1.1, s.1.2, fun f hf =>
          congrArg Subtype.val (mem_fixedPoints.1 s.2 ⟨f, hf⟩)⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, mem_fixedPoints.2 fun f =>
          Subtype.ext (x.2.2 f f.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rwa [e] at h

theorem mem_setStab_orbit {E W : Subgroup (Perm X)} (hEW : E ≤ normalizer W) {x y : X}
    (hy : y ∈ orbit W x) {e : Perm X} (he : e ∈ E) (hey : e y = y) :
    e ∈ setStab (orbit W x : Set X) := by
  have hΩ : orbit W y = orbit W x := orbit_eq_iff.2 hy
  have key : ∀ f ∈ E, f y = y → ∀ z ∈ orbit W x, f z ∈ orbit W x := by
    intro f hf hfy z hz
    rw [← hΩ] at hz ⊢
    obtain ⟨⟨w, hw⟩, rfl⟩ := mem_orbit_iff.1 hz
    have hw' : f * w * f⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 (hEW hf) w).1 hw
    refine mem_orbit_iff.2 ⟨⟨f * w * f⁻¹, hw'⟩, ?_⟩
    have hfi : f⁻¹ y = y := Equiv.Perm.inv_eq_iff_eq.2 hfy.symm
    show f (w (f⁻¹ y)) = f (w y)
    rw [hfi]
  intro z
  refine ⟨fun hz => ?_, key e he hey z⟩
  have hinv : e⁻¹ y = y := Equiv.Perm.inv_eq_iff_eq.2 hey.symm
  have := key e⁻¹ (E.inv_mem he) hinv _ hz
  rwa [inv_apply'] at this

end CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

end

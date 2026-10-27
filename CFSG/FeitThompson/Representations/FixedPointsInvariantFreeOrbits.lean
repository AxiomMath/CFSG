module

public import Mathlib.GroupTheory.FixedPointFree
import CFSG.FeitThompson.Representations.PrimeOrderAutFixesOnePointPerOrbit

open MulAction

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {D : Type*} [Group D] {X : Type*} [MulAction D X]
  {q : ℕ} {β : MulAut D} {b : Equiv.Perm X}

namespace CoprimeFreeAction

variable (hb : ∀ (d : D) (x : X), b (d • x) = β d • b x)

include hb

theorem symm_apply_smul (d : D) (x : X) : b.symm (d • x) = β.symm d • b.symm x := by
  apply b.injective; simp [hb]

theorem orbitRel_apply_apply_iff {x y : X} : orbitRel D X (b x) (b y) ↔ orbitRel D X x y := by
  simp only [orbitRel_apply, mem_orbit_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨d, hd⟩
    refine ⟨β.symm d, ?_⟩
    have := congrArg b.symm hd
    rwa [symm_apply_smul hb, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  · rintro ⟨d, rfl⟩
    exact ⟨β d, (hb d y).symm⟩

def orbitQuotientPerm : Equiv.Perm (orbitRel.Quotient D X) :=
  Quotient.congr b fun _ _ => (orbitRel_apply_apply_iff hb).symm

@[simp]
theorem orbitQuotientPerm_mk (x : X) :
    orbitQuotientPerm hb (Quotient.mk'' x) = (Quotient.mk'' (b x) : orbitRel.Quotient D X) :=
  Quotient.congr_mk _ _ x

theorem orbitQuotientPerm_pow_mk (n : ℕ) (x : X) :
    (orbitQuotientPerm hb ^ n) (Quotient.mk'' x) =
      (Quotient.mk'' ((b ^ n) x) : orbitRel.Quotient D X) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, orbitQuotientPerm_mk, ih, pow_succ, Equiv.Perm.mul_apply]

theorem orbitQuotientPerm_pow_eq_one (hbq : b ^ q = 1) : orbitQuotientPerm hb ^ q = 1 := by
  ext Q
  induction Q using Quotient.inductionOn' with
  | h x => rw [orbitQuotientPerm_pow_mk, hbq]; rfl

theorem apply_mem_orbit_iff_of_isFixedPt {Q : orbitRel.Quotient D X}
    (hQ : orbitQuotientPerm hb Q = Q) (x : X) : b x ∈ Q.orbit ↔ x ∈ Q.orbit := by
  rw [orbitRel.Quotient.mem_orbit, orbitRel.Quotient.mem_orbit]
  refine ⟨fun h => (orbitQuotientPerm hb).injective ?_, fun h => ?_⟩
  · rw [orbitQuotientPerm_mk, h, hQ]
  · rw [← orbitQuotientPerm_mk hb, h, hQ]

theorem exists_mem_orbit_apply_eq_self [Finite X] (hq : q.Prime) (hqD : ¬ q ∣ Nat.card D)
    (hfree : ∀ (d : D) (x : X), d • x = x → d = 1) (hbq : b ^ q = 1)
    {Q : orbitRel.Quotient D X} (hQ : orbitQuotientPerm hb Q = Q) : ∃ x ∈ Q.orbit, b x = x := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fintype (Q.orbit : Set X) := Fintype.ofFinite _
  have hmem := apply_mem_orbit_iff_of_isFixedPt hb hQ
  have hcard : ¬ q ∣ Fintype.card (Q.orbit : Set X) := by
    have horb : Q.orbit = orbit D Q.out := by
      conv_lhs => rw [← Quotient.out_eq' Q]
      exact orbitRel.Quotient.orbit_mk _
    rw [← Nat.card_eq_fintype_card, horb, natCard_orbit_eq_natCard_of_free hfree]
    exact hqD
  have hσ : (b.subtypePerm hmem) ^ q ^ 1 = 1 := by
    rw [pow_one, Equiv.Perm.subtypePerm_pow]
    ext y
    simp [hbq]
  obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

theorem injOn_mk_fixedPoints (hβ : MonoidHom.FixedPointFree ⇑β)
    (hfree : ∀ (d : D) (x : X), d • x = x → d = 1) :
    Set.InjOn (fun x : X => (Quotient.mk'' x : orbitRel.Quotient D X))
      (Function.fixedPoints ⇑b) := by
  intro x hx y hy hxy
  obtain ⟨d, rfl⟩ := mem_orbit_iff.1 (orbitRel_apply.1 (Quotient.eq''.1 hxy))
  have h1 : b (d • y) = d • y := hx
  rw [hb, hy] at h1
  have h2 : d⁻¹ * β d = 1 := hfree _ y (by rw [mul_smul, h1, inv_smul_smul])
  rw [hβ d (inv_mul_eq_one.1 h2).symm, one_smul]

theorem bijOn_mk_fixedPoints [Finite X] (hq : q.Prime) (hqD : ¬ q ∣ Nat.card D)
    (hβ : MonoidHom.FixedPointFree ⇑β) (hfree : ∀ (d : D) (x : X), d • x = x → d = 1)
    (hbq : b ^ q = 1) :
    Set.BijOn (fun x : X => (Quotient.mk'' x : orbitRel.Quotient D X))
      (Function.fixedPoints ⇑b) (Function.fixedPoints (orbitQuotientPerm hb)) := by
  refine ⟨fun x hx => ?_, injOn_mk_fixedPoints hb hβ hfree, fun Q hQ => ?_⟩
  · change orbitQuotientPerm hb _ = _
    rw [orbitQuotientPerm_mk, (hx : b x = x)]
  · obtain ⟨x, hxQ, hx⟩ := exists_mem_orbit_apply_eq_self hb hq hqD hfree hbq hQ
    exact ⟨x, hx, orbitRel.Quotient.mem_orbit.1 hxQ⟩

noncomputable def fixedPointsEquivFixedPointsOrbitQuotient [Finite X] (hq : q.Prime)
    (hqD : ¬ q ∣ Nat.card D) (hβ : MonoidHom.FixedPointFree ⇑β)
    (hfree : ∀ (d : D) (x : X), d • x = x → d = 1) (hbq : b ^ q = 1) :
    (Function.fixedPoints ⇑b) ≃ (Function.fixedPoints (orbitQuotientPerm hb)) :=
  (bijOn_mk_fixedPoints hb hq hqD hβ hfree hbq).equiv _

@[simp]
theorem coe_fixedPointsEquivFixedPointsOrbitQuotient_apply [Finite X] (hq : q.Prime)
    (hqD : ¬ q ∣ Nat.card D) (hβ : MonoidHom.FixedPointFree ⇑β)
    (hfree : ∀ (d : D) (x : X), d • x = x → d = 1) (hbq : b ^ q = 1)
    (x : Function.fixedPoints ⇑b) :
    (fixedPointsEquivFixedPointsOrbitQuotient hb hq hqD hβ hfree hbq x :
      orbitRel.Quotient D X) = Quotient.mk'' (x : X) := (rfl)

theorem natCard_fixedPoints_eq [Finite X] (hq : q.Prime) (hqD : ¬ q ∣ Nat.card D)
    (hβ : MonoidHom.FixedPointFree ⇑β) (hfree : ∀ (d : D) (x : X), d • x = x → d = 1)
    (hbq : b ^ q = 1) :
    Nat.card (Function.fixedPoints ⇑b) =
      Nat.card (Function.fixedPoints (orbitQuotientPerm hb)) :=
  Nat.card_congr (fixedPointsEquivFixedPointsOrbitQuotient hb hq hqD hβ hfree hbq)

end CoprimeFreeAction

end

end CFSG.FeitThompson

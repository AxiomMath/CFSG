module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type
import CFSG.FeitThompson.Foundations.OrbitStabilizerIndex

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open MulAction

variable {D Ω : Type*} [Group D] [MulAction D Ω] {q : ℕ} {b : MulAut D} {β : Equiv.Perm Ω}
  (hfree : ∀ (d : D) (ω : Ω), d • ω = ω → d = 1)
  (hbfix : ∀ d : D, b d = d → d = 1)
  (hβb : ∀ (d : D) (ω : Ω), β (d • ω) = b d • β ω)
  (hβorb : ∀ ω : Ω, β ω ∈ orbit D ω)

include hfree in
theorem stabilizer_eq_bot_of_free (ω : Ω) : stabilizer D ω = ⊥ :=
  eq_bot_iff.2 fun d hd => Subgroup.mem_bot.2 (hfree d ω (mem_stabilizer_iff.1 hd))

include hfree in
theorem natCard_orbit_eq_natCard_of_free (ω : Ω) : Nat.card (orbit D ω) = Nat.card D := by
  have h := natCard_orbit_mul_natCard_stabilizer (G := D) (x := ω)
  rw [stabilizer_eq_bot_of_free hfree ω] at h
  simpa using h

include hβorb in
theorem orbit_perm_apply_eq (ω : Ω) : orbit D (β ω) = orbit D ω := orbit_eq_iff.2 (hβorb ω)

include hβorb in
theorem perm_inv_apply_mem_orbit (ω : Ω) : β⁻¹ ω ∈ orbit D ω := by
  have h : orbit D ω = orbit D (β⁻¹ ω) := by simpa using orbit_perm_apply_eq hβorb (β⁻¹ ω)
  exact h ▸ mem_orbit_self _

include hβorb in
theorem perm_apply_mem_orbit_iff (ω x : Ω) : β x ∈ orbit D ω ↔ x ∈ orbit D ω := by
  rw [← orbit_eq_iff, ← orbit_eq_iff, orbit_eq_iff.2 (hβorb x)]

include hβorb in
theorem image_orbit_eq_orbit (ω : Ω) : β '' orbit D ω = orbit D ω := by
  refine Set.Subset.antisymm ?_ fun x hx => ⟨β⁻¹ x, ?_, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← orbit_eq_iff.2 hx]
    exact hβorb x
  · rw [← orbit_eq_iff.2 hx]
    exact perm_inv_apply_mem_orbit hβorb x

include hfree hbfix hβb in
theorem eq_of_perm_fixed_of_mem_orbit {v w : Ω} (hvw : w ∈ orbit D v) (hv : β v = v)
    (hw : β w = w) : w = v := by
  obtain ⟨d, rfl⟩ := hvw
  have key : b d • v = d • v := by
    have h := hβb d v
    rw [hv, hw] at h
    exact h.symm
  have hd : d⁻¹ * b d = 1 := hfree _ v (by rw [mul_smul, key, inv_smul_smul])
  have hbd : b d = d := by rw [← mul_left_cancel_iff (a := d⁻¹), hd, inv_mul_cancel]
  simp [hbfix d hbd]

include hfree hβorb in
theorem exists_perm_fixed_mem_orbit [Finite D] (hq : q.Prime) (hqD : ¬ q ∣ Nat.card D)
    (hβq : β ^ q = 1) (ω : Ω) : ∃ v ∈ orbit D ω, β v = v := by
  have : Fact q.Prime := ⟨hq⟩
  have : Finite (orbit D ω) := (Finite.finite_mulAction_orbit ω).to_subtype
  let _ : Fintype (orbit D ω) := Fintype.ofFinite _
  have hσ : (β.subtypePerm (perm_apply_mem_orbit_iff hβorb ω)) ^ q ^ 1 = 1 := by
    refine Equiv.Perm.ext fun x => Subtype.ext ?_
    rw [pow_one, Equiv.Perm.subtypePerm_pow, Equiv.Perm.subtypePerm_apply]
    simp [hβq]
  have hcard : ¬ q ∣ Fintype.card (orbit D ω) := by
    rw [← Nat.card_eq_fintype_card, natCard_orbit_eq_natCard_of_free hfree]
    exact hqD
  obtain ⟨⟨v, hv⟩, hfix⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  exact ⟨v, hv, congrArg Subtype.val hfix⟩

include hfree hbfix hβb hβorb in
theorem existsUnique_perm_fixed_mem_orbit [Finite D] (hq : q.Prime) (hqD : ¬ q ∣ Nat.card D)
    (hβq : β ^ q = 1) (ω : Ω) : ∃! v, v ∈ orbit D ω ∧ β v = v := by
  obtain ⟨v, hv, hfix⟩ := exists_perm_fixed_mem_orbit hfree hβorb hq hqD hβq ω
  exact ⟨v, ⟨hv, hfix⟩, fun w hw =>
    eq_of_perm_fixed_of_mem_orbit hfree hbfix hβb (orbit_eq_iff.2 hv ▸ hw.1) hfix hw.2⟩

include hfree hbfix hβb hβorb in
theorem ncard_orbit_inter_fixedPoints [Finite D] (hq : q.Prime) (hqD : ¬ q ∣ Nat.card D)
    (hβq : β ^ q = 1) (ω : Ω) : (orbit D ω ∩ Function.fixedPoints β).ncard = 1 := by
  obtain ⟨v, hv, huniq⟩ := existsUnique_perm_fixed_mem_orbit hfree hbfix hβb hβorb hq hqD hβq ω
  rw [Set.ncard_eq_one]
  exact ⟨v, Set.eq_singleton_iff_unique_mem.2 ⟨hv, fun w hw => huniq w hw⟩⟩

include hfree hbfix hβb hβorb in
theorem natCard_fixedPoints_eq_natCard_orbitRel_quotient [Finite D] (hq : q.Prime)
    (hqD : ¬ q ∣ Nat.card D) (hβq : β ^ q = 1) :
    Nat.card (Function.fixedPoints β) = Nat.card (Quotient (orbitRel D Ω)) := by
  refine Nat.card_eq_of_bijective (fun v => Quotient.mk (orbitRel D Ω) (v : Ω)) ⟨?_, ?_⟩
  · rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    have hvw : v ∈ orbit D w := (orbitRel_apply (G := D)).1 (Quotient.exact h)
    exact Subtype.ext (eq_of_perm_fixed_of_mem_orbit hfree hbfix hβb hvw hw hv)
  · intro x
    induction x using Quotient.inductionOn with
    | _ ω =>
      obtain ⟨v, hv, hfix⟩ := exists_perm_fixed_mem_orbit hfree hβorb hq hqD hβq ω
      exact ⟨⟨v, hfix⟩, Quotient.sound ((orbitRel_apply (G := D)).2 hv)⟩

include hfree hbfix hβb hβorb in
theorem natCard_eq_natCard_mul_natCard_fixedPoints [Finite D] (hq : q.Prime)
    (hqD : ¬ q ∣ Nat.card D) (hβq : β ^ q = 1) :
    Nat.card Ω = Nat.card D * Nat.card (Function.fixedPoints β) := by
  rw [natCard_fixedPoints_eq_natCard_orbitRel_quotient hfree hbfix hβb hβorb hq hqD hβq,
    Nat.card_congr (selfEquivOrbitsQuotientProd (stabilizer_eq_bot_of_free hfree)),
    Nat.card_prod, Nat.mul_comm]

end

end CFSG.FeitThompson

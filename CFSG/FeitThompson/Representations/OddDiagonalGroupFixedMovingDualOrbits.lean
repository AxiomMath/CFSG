module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Field.ZMod
public import CFSG.FeitThompson.Representations.FixedPointsInvariantFreeOrbits
public import CFSG.FeitThompson.Representations.PrimeOrderAutFixesOnePointPerOrbit
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Field.IsField
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module MulAction

section DualAction

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]

instance dualMulAction : MulAction (E ≃ₗ[k] E) (Module.Dual k E) where
  smul f ℓ := ℓ ∘ₗ (f.symm : E →ₗ[k] E)
  one_smul _ := LinearMap.ext fun _ => rfl
  mul_smul _ _ _ := LinearMap.ext fun _ => rfl

@[simp] lemma smul_dual_apply (f : E ≃ₗ[k] E) (ℓ : Module.Dual k E) (v : E) :
    (f • ℓ) v = ℓ (f.symm v) := (rfl)

lemma conj_smul_dual (f d : E ≃ₗ[k] E) (ℓ : Module.Dual k E) :
    (f * d * f⁻¹) • (f • ℓ) = f • (d • ℓ) := by
  rw [← mul_smul, ← mul_smul]
  congr 1
  group

end DualAction

section Diagonal

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E] {ι : Type*}

def diagAutSubgroup (e : Basis ι k E) : Subgroup (E ≃ₗ[k] E) where
  carrier := {f | ∀ i, ∃ c : k, f (e i) = c • e i}
  one_mem' i := ⟨1, by simp⟩
  mul_mem' := by
    intro f g hf hg i
    obtain ⟨c, hc⟩ := hg i
    obtain ⟨d, hd⟩ := hf i
    exact ⟨c * d, by simp [hc, hd, mul_smul]⟩
  inv_mem' := by
    intro f hf i
    obtain ⟨c, hc⟩ := hf i
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp only [zero_smul] at hc
      exact e.ne_zero i (by simpa using congrArg f.symm hc)
    refine ⟨c⁻¹, ?_⟩
    have h : f (c⁻¹ • e i) = e i := by rw [map_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    change f.symm (e i) = _
    conv_lhs => rw [← h]
    rw [f.symm_apply_apply]

lemma mem_diagAutSubgroup_iff {e : Basis ι k E} {f : E ≃ₗ[k] E} :
    f ∈ diagAutSubgroup e ↔ ∀ i, ∃ c : k, f (e i) = c • e i := Iff.rfl

lemma exists_scalar_of_mem_diagAutSubgroup {e : Basis ι k E} {f : E ≃ₗ[k] E}
    (hf : f ∈ diagAutSubgroup e) (i : ι) :
    ∃ c : k, c ≠ 0 ∧ f (e i) = c • e i ∧ f.symm (e i) = c⁻¹ • e i := by
  obtain ⟨c, hc⟩ := mem_diagAutSubgroup_iff.1 hf i
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hc
    exact e.ne_zero i (by simpa using congrArg f.symm hc)
  refine ⟨c, hc0, hc, ?_⟩
  have h : f (c⁻¹ • e i) = e i := by rw [map_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  conv_lhs => rw [← h]
  rw [f.symm_apply_apply]

def fullSupportDualSet (e : Basis ι k E) : Set (Module.Dual k E) := {ℓ | ∀ i, ℓ (e i) ≠ 0}

@[simp] lemma mem_fullSupportDualSet {e : Basis ι k E} {ℓ : Module.Dual k E} :
    ℓ ∈ fullSupportDualSet e ↔ ∀ i, ℓ (e i) ≠ 0 := Iff.rfl

lemma smul_mem_fullSupportDualSet {e : Basis ι k E} {f : E ≃ₗ[k] E}
    (hf : f ∈ diagAutSubgroup e) {ℓ : Module.Dual k E} (hℓ : ℓ ∈ fullSupportDualSet e) :
    f • ℓ ∈ fullSupportDualSet e := by
  intro i
  obtain ⟨c, hc0, _, hsymm⟩ := exists_scalar_of_mem_diagAutSubgroup hf i
  rw [smul_dual_apply, hsymm, map_smul, smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero hc0) (hℓ i)

variable {D : Subgroup (E ≃ₗ[k] E)}

def fullSupportDual (e : Basis ι k E) (hD : D ≤ diagAutSubgroup e) :
    SubMulAction ↥D (Module.Dual k E) where
  carrier := fullSupportDualSet e
  smul_mem' d _ hℓ := smul_mem_fullSupportDualSet (hD d.2) hℓ

@[simp] lemma mem_fullSupportDual {e : Basis ι k E} {hD : D ≤ diagAutSubgroup e}
    {ℓ : Module.Dual k E} : ℓ ∈ fullSupportDual e hD ↔ ∀ i, ℓ (e i) ≠ 0 := Iff.rfl

@[simp] lemma coe_smul_fullSupportDual {e : Basis ι k E} {hD : D ≤ diagAutSubgroup e}
    (d : ↥D) (x : ↥(fullSupportDual e hD)) :
    ((d • x : ↥(fullSupportDual e hD)) : Module.Dual k E) =
      (d : E ≃ₗ[k] E) • (x : Module.Dual k E) := (rfl)

theorem eq_one_of_smul_eq_self {e : Basis ι k E} {hD : D ≤ diagAutSubgroup e}
    (d : ↥D) (x : ↥(fullSupportDual e hD)) (hx : d • x = x) : d = 1 := by
  have key : ∀ i, (d : E ≃ₗ[k] E) (e i) = e i := by
    intro i
    obtain ⟨c, hc0, hc, hsymm⟩ := exists_scalar_of_mem_diagAutSubgroup (hD d.2) i
    have h : (x : Module.Dual k E) ((d : E ≃ₗ[k] E).symm (e i)) = (x : Module.Dual k E) (e i) := by
      have h2 : ((d • x : ↥(fullSupportDual e hD)) : Module.Dual k E) (e i)
          = (x : Module.Dual k E) (e i) := by rw [hx]
      rwa [coe_smul_fullSupportDual, smul_dual_apply] at h2
    rw [hsymm, map_smul, smul_eq_mul] at h
    have hc1 : c⁻¹ = 1 := mul_right_cancel₀ (x.2 i) (by rw [h, one_mul])
    rw [hc, inv_eq_one.1 hc1, one_smul]
  exact Subtype.ext (LinearEquiv.toLinearMap_injective (e.ext key))

theorem natCard_orbit_fullSupportDual {e : Basis ι k E} (hD : D ≤ diagAutSubgroup e)
    (x : ↥(fullSupportDual e hD)) : Nat.card (orbit ↥D x) = Nat.card ↥D :=
  natCard_orbit_eq_natCard_of_free eq_one_of_smul_eq_self x

noncomputable def fullSupportDualEquiv (e : Basis ι k E) (hD : D ≤ diagAutSubgroup e) :
    ↥(fullSupportDual e hD) ≃ (ι → {c : k // c ≠ 0}) :=
  (Equiv.subtypeEquiv (e.constr k).toEquiv
    (fun f => by simp [Basis.constr_basis])).symm.trans Equiv.subtypePiEquivPi

theorem natCard_fullSupportDual [Finite k] [Finite ι] (e : Basis ι k E)
    (hD : D ≤ diagAutSubgroup e) :
    Nat.card ↥(fullSupportDual e hD) = (Nat.card k - 1) ^ Nat.card ι := by
  rw [Nat.card_congr (fullSupportDualEquiv e hD), Nat.card_fun,
    Nat.card_congr unitsEquivNeZero.symm, Nat.card_units]

lemma finite_dual [Finite k] [Finite ι] (e : Basis ι k E) : Finite (Module.Dual k E) := by
  have h1 : Module.Finite k E := Module.Finite.of_basis e
  have h2 : Finite E := Module.finite_iff_finite.mp h1
  exact Finite.of_injective (fun f : Module.Dual k E => (f : E → k))
    fun _ _ h => LinearMap.ext fun x => congrFun h x

lemma finite_fullSupportDual [Finite k] [Finite ι] (e : Basis ι k E)
    (hD : D ≤ diagAutSubgroup e) : Finite ↥(fullSupportDual e hD) :=
  have := finite_dual e
  Subtype.finite

end Diagonal

section Shift

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E] {q : ℕ}

noncomputable def shift (e : Basis (ZMod q) k E) : E ≃ₗ[k] E :=
  e.equiv e (Equiv.addRight (1 : ZMod q))

variable (e : Basis (ZMod q) k E)

@[simp] lemma shift_basis (i : ZMod q) : shift e (e i) = e (i + 1) := by
  simp [shift, Basis.equiv_apply]

@[simp] lemma shift_symm_basis (i : ZMod q) : (shift e).symm (e i) = e (i - 1) := by
  rw [LinearEquiv.symm_apply_eq]; simp

lemma shift_inv_eq_symm : ((shift e)⁻¹ : E ≃ₗ[k] E) = (shift e).symm := rfl

lemma shift_pow_basis (n : ℕ) (i : ZMod q) : ((shift e) ^ n) (e i) = e (i + n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    simp only [LinearEquiv.mul_apply, shift_basis, ih]
    push_cast
    ring_nf

lemma shift_pow_eq_one : (shift e) ^ q = 1 :=
  LinearEquiv.toLinearMap_injective (e.ext fun i => by
    change ((shift e) ^ q) (e i) = e i
    rw [shift_pow_basis]; simp)

omit [Field k] in
lemma eq_apply_zero_of_shift_invariant [NeZero q] {f : ZMod q → k}
    (h : ∀ i, f (i + 1) = f i) (i : ZMod q) : f i = f 0 := by
  have hn : ∀ n : ℕ, f (n : ZMod q) = f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => push_cast; rw [h, ih]
  have h2 := hn i.val
  rwa [ZMod.natCast_val, ZMod.cast_id] at h2

end Shift

section Main

variable {p q : ℕ} [Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
  (e : Basis (ZMod q) (ZMod p) E) {D : Subgroup (E ≃ₗ[ZMod p] E)}
  (hD : D ≤ diagAutSubgroup e)

lemma shift_smul_mem_fullSupportDual_iff (ℓ : Module.Dual (ZMod p) E) :
    shift e • ℓ ∈ fullSupportDual e hD ↔ ℓ ∈ fullSupportDual e hD := by
  simp only [mem_fullSupportDual, smul_dual_apply, shift_symm_basis]
  exact ⟨fun h i => by simpa using h (i + 1), fun h i => h _⟩

noncomputable def shiftDualPerm : Equiv.Perm ↥(fullSupportDual e hD) :=
  (MulAction.toPerm (shift e)).subtypePerm (shift_smul_mem_fullSupportDual_iff e hD)

@[simp] lemma coe_shiftDualPerm (x : ↥(fullSupportDual e hD)) :
    ((shiftDualPerm e hD x : ↥(fullSupportDual e hD)) : Module.Dual (ZMod p) E) =
      shift e • (x : Module.Dual (ZMod p) E) := (rfl)

lemma coe_shiftDualPerm_pow (n : ℕ) (x : ↥(fullSupportDual e hD)) :
    (((shiftDualPerm e hD ^ n) x : ↥(fullSupportDual e hD)) : Module.Dual (ZMod p) E) =
      (shift e ^ n) • (x : Module.Dual (ZMod p) E) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, coe_shiftDualPerm, pow_succ, mul_smul]

lemma shiftDualPerm_pow_eq_one : shiftDualPerm e hD ^ q = 1 :=
  Equiv.ext fun x => Subtype.ext (by
    rw [coe_shiftDualPerm_pow, shift_pow_eq_one, one_smul]; rfl)

variable (hconj : ∀ d : E ≃ₗ[ZMod p] E, shift e * d * (shift e)⁻¹ ∈ D ↔ d ∈ D)

include hconj

lemma map_conj_shift : Subgroup.map (MulAut.conj (shift e)).toMonoidHom D = D := by
  apply le_antisymm
  · rintro _ ⟨d, hd, rfl⟩
    exact (hconj d).2 hd
  · intro d hd
    refine ⟨(shift e)⁻¹ * d * shift e, (hconj _).1 (by group; exact hd), ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    group

noncomputable def shiftConj : MulAut ↥D :=
  ((MulAut.conj (shift e)).subgroupMap D).trans
    (MulEquiv.subgroupCongr (map_conj_shift e hconj))

@[simp] lemma coe_shiftConj (d : ↥D) :
    ((shiftConj e hconj d : ↥D) : E ≃ₗ[ZMod p] E) = shift e * d * (shift e)⁻¹ := (rfl)

lemma fixedPointFree_shiftConj
    (hcent : ∀ d : ↥D, (d : E ≃ₗ[ZMod p] E) * shift e = shift e * d → d = 1) :
    MonoidHom.FixedPointFree ⇑(shiftConj e hconj) := by
  intro d hd
  refine hcent d ?_
  have h : shift e * (d : E ≃ₗ[ZMod p] E) * (shift e)⁻¹ = (d : E ≃ₗ[ZMod p] E) := by
    rw [← coe_shiftConj e hconj d, hd]
  calc (d : E ≃ₗ[ZMod p] E) * shift e
      = (shift e * (d : E ≃ₗ[ZMod p] E) * (shift e)⁻¹) * shift e := by rw [h]
    _ = shift e * (d : E ≃ₗ[ZMod p] E) := by group

lemma shiftDualPerm_smul (d : ↥D) (x : ↥(fullSupportDual e hD)) :
    shiftDualPerm e hD (d • x) = shiftConj e hconj d • shiftDualPerm e hD x :=
  Subtype.ext (by
    rw [coe_shiftDualPerm, coe_smul_fullSupportDual, coe_smul_fullSupportDual, coe_shiftDualPerm,
      coe_shiftConj, conj_smul_dual])

omit hconj

lemma apply_basis_eq_of_isFixedPt [NeZero q] {x : ↥(fullSupportDual e hD)}
    (hx : shiftDualPerm e hD x = x) (i : ZMod q) :
    (x : Module.Dual (ZMod p) E) (e i) = (x : Module.Dual (ZMod p) E) (e 0) := by
  refine eq_apply_zero_of_shift_invariant (f := fun j => (x : Module.Dual (ZMod p) E) (e j))
    (fun j => ?_) i
  have h : ((shiftDualPerm e hD x : ↥(fullSupportDual e hD)) : Module.Dual (ZMod p) E) (e (j + 1))
      = (x : Module.Dual (ZMod p) E) (e (j + 1)) := by rw [hx]
  rw [coe_shiftDualPerm, smul_dual_apply, shift_symm_basis, add_sub_cancel_right] at h
  exact h.symm

noncomputable def fixedPointsShiftDualPermEquiv [NeZero q] :
    Function.fixedPoints ⇑(shiftDualPerm e hD) ≃ {c : ZMod p // c ≠ 0} := by
  refine Equiv.ofBijective (fun x => ⟨(x.1 : Module.Dual (ZMod p) E) (e 0), x.1.2 0⟩) ⟨?_, ?_⟩
  · intro x y hxy
    refine Subtype.ext (Subtype.ext (e.ext fun i => ?_))
    rw [apply_basis_eq_of_isFixedPt e hD x.2, apply_basis_eq_of_isFixedPt e hD y.2]
    exact congrArg Subtype.val hxy
  · rintro ⟨c, hc⟩
    have hmem : (e.constr (ZMod p) (fun _ => c)) ∈ fullSupportDual e hD := fun i => by
      rw [Basis.constr_basis]; exact hc
    refine ⟨⟨⟨_, hmem⟩, Subtype.ext (e.ext fun i => ?_)⟩,
      Subtype.ext (Basis.constr_basis e (ZMod p) (fun _ => c) 0)⟩
    rw [coe_shiftDualPerm, smul_dual_apply, shift_symm_basis, Basis.constr_basis,
      Basis.constr_basis]

theorem natCard_fixedPoints_shiftDualPerm [NeZero q] :
    Nat.card (Function.fixedPoints ⇑(shiftDualPerm e hD)) = p - 1 := by
  rw [Nat.card_congr (fixedPointsShiftDualPermEquiv e hD),
    Nat.card_congr unitsEquivNeZero.symm, Nat.card_units, Nat.card_zmod]

theorem exists_isFixedPt_shiftDualPerm [NeZero q] :
    ∃ ℓ₀ : ↥(fullSupportDual e hD), shiftDualPerm e hD ℓ₀ = ℓ₀ :=
  ⟨((fixedPointsShiftDualPermEquiv e hD).symm ⟨1, one_ne_zero⟩ : ↥(fullSupportDual e hD)),
    ((fixedPointsShiftDualPermEquiv e hD).symm ⟨1, one_ne_zero⟩).2⟩

include hconj

theorem natCard_fixedPoints_orbitQuotientPerm (hq : q.Prime) (hqD : ¬ q ∣ Nat.card ↥D)
    (hcent : ∀ d : ↥D, (d : E ≃ₗ[ZMod p] E) * shift e = shift e * d → d = 1) :
    Nat.card (Function.fixedPoints
      (CoprimeFreeAction.orbitQuotientPerm (shiftDualPerm_smul e hD hconj))) = p - 1 := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have := finite_fullSupportDual e hD
  rw [← CoprimeFreeAction.natCard_fixedPoints_eq (shiftDualPerm_smul e hD hconj) hq hqD
      (fixedPointFree_shiftConj e hconj hcent) eq_one_of_smul_eq_self
      (shiftDualPerm_pow_eq_one e hD),
    natCard_fixedPoints_shiftDualPerm e hD]

theorem exists_not_isFixedPt_orbitQuotientPerm (hq : q.Prime) (hqD : ¬ q ∣ Nat.card ↥D)
    (hcent : ∀ d : ↥D, (d : E ≃ₗ[ZMod p] E) * shift e = shift e * d → d = 1)
    (hp : Odd p) (hDodd : Odd (Nat.card ↥D)) :
    ∃ Q : orbitRel.Quotient ↥D ↥(fullSupportDual e hD),
      CoprimeFreeAction.orbitQuotientPerm (shiftDualPerm_smul e hD hconj) Q ≠ Q := by
  have hqne : NeZero q := ⟨hq.ne_zero⟩
  have hfin := finite_fullSupportDual e hD
  by_contra hcon
  have hall : Function.fixedPoints
      (CoprimeFreeAction.orbitQuotientPerm (shiftDualPerm_smul e hD hconj)) = Set.univ :=
    Set.eq_univ_of_forall fun Q => not_ne_iff.1 fun h => hcon ⟨Q, h⟩
  have horb : Nat.card (orbitRel.Quotient ↥D ↥(fullSupportDual e hD)) = p - 1 := by
    rw [← natCard_fixedPoints_orbitQuotientPerm e hD hconj hq hqD hcent, hall]
    exact (Nat.card_congr (Equiv.Set.univ _)).symm
  have hX : Nat.card ↥(fullSupportDual e hD)
      = Nat.card (orbitRel.Quotient ↥D ↥(fullSupportDual e hD)) * Nat.card ↥D := by
    rw [Nat.card_congr (selfEquivOrbitsQuotientProd
      (stabilizer_eq_bot_of_free (eq_one_of_smul_eq_self (hD := hD)))), Nat.card_prod]
  have hXcard : Nat.card ↥(fullSupportDual e hD) = (p - 1) ^ q := by
    have h := natCard_fullSupportDual e hD
    rwa [Nat.card_zmod, Nat.card_zmod] at h
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hcomb : (p - 1) * (p - 1) ^ (q - 1) = (p - 1) * Nat.card ↥D := by
    rw [← pow_succ']
    have hqs : q - 1 + 1 = q := by omega
    rw [hqs, ← hXcard, hX, horb]
  have hDeq : Nat.card ↥D = (p - 1) ^ (q - 1) :=
    (Nat.eq_of_mul_eq_mul_left (by omega) hcomb).symm
  have hpe : Even (p - 1) := Nat.Odd.sub_odd hp odd_one
  have heven : Even (Nat.card ↥D) := by
    rw [hDeq]
    exact (Nat.even_pow' (by omega)).mpr hpe
  exact (Nat.not_odd_iff_even.2 heven) hDodd

theorem exists_minimalPeriod_orbitQuotientPerm_eq (hq : q.Prime) (hqD : ¬ q ∣ Nat.card ↥D)
    (hcent : ∀ d : ↥D, (d : E ≃ₗ[ZMod p] E) * shift e = shift e * d → d = 1)
    (hp : Odd p) (hDodd : Odd (Nat.card ↥D)) :
    ∃ Q : orbitRel.Quotient ↥D ↥(fullSupportDual e hD),
      CoprimeFreeAction.orbitQuotientPerm (shiftDualPerm_smul e hD hconj) Q ≠ Q ∧
      Function.minimalPeriod
        (CoprimeFreeAction.orbitQuotientPerm (shiftDualPerm_smul e hD hconj)) Q = q := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, hQ⟩ :=
    exists_not_isFixedPt_orbitQuotientPerm e hD hconj hq hqD hcent hp hDodd
  refine ⟨Q, hQ, Function.minimalPeriod_eq_prime ?_ hQ⟩
  have hpow := CoprimeFreeAction.orbitQuotientPerm_pow_eq_one (shiftDualPerm_smul e hD hconj)
    (shiftDualPerm_pow_eq_one e hD)
  have : ((CoprimeFreeAction.orbitQuotientPerm (shiftDualPerm_smul e hD hconj)) ^ q) Q = Q := by
    rw [hpow]; rfl
  rwa [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow]

theorem exists_fixed_and_moving_fullSupportDual (hq : q.Prime) (hqD : ¬ q ∣ Nat.card ↥D)
    (hcent : ∀ d : ↥D, (d : E ≃ₗ[ZMod p] E) * shift e = shift e * d → d = 1)
    (hp : Odd p) (hDodd : Odd (Nat.card ↥D)) :
    (∃ ℓ₀ : ↥(fullSupportDual e hD), shiftDualPerm e hD ℓ₀ = ℓ₀) ∧
      ∃ ℓ₁ : ↥(fullSupportDual e hD),
        CoprimeFreeAction.orbitQuotientPerm (shiftDualPerm_smul e hD hconj)
          (Quotient.mk'' ℓ₁) ≠ Quotient.mk'' ℓ₁ := by
  have : NeZero q := ⟨hq.ne_zero⟩
  refine ⟨exists_isFixedPt_shiftDualPerm e hD, ?_⟩
  obtain ⟨Q, hQ⟩ :=
    exists_not_isFixedPt_orbitQuotientPerm e hD hconj hq hqD hcent hp hDodd
  induction Q using Quotient.inductionOn' with
  | h x => exact ⟨x, hQ⟩

end Main

end

end CFSG.FeitThompson

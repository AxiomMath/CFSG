module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence
import CFSG.FeitThompson.Representations.CommutingOperatorFiniteScalarField

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open MulAction

namespace CFSG.FeitThompson

variable {p a : ℕ} [Fact p.Prime] {A V : Type*} [Group A] [AddCommGroup V]
  [Module (ZMod p) V] {U : Subgroup A} {ρ : Representation (ZMod p) A V}

theorem mem_invariants_comp_subtype_iff (v : V) :
    v ∈ Representation.invariants (ρ.comp U.subtype) ↔ ∀ u ∈ U, ρ u v = v := by
  rw [Representation.mem_invariants]
  exact ⟨fun h u hu => h ⟨u, hu⟩, fun h u => h u u.2⟩

theorem apply_mem_invariants_comp_subtype [U.Normal] (a : A) {v : V}
    (hv : v ∈ Representation.invariants (ρ.comp U.subtype)) :
    ρ a v ∈ Representation.invariants (ρ.comp U.subtype) := by
  rw [mem_invariants_comp_subtype_iff] at hv ⊢
  intro u hu
  have h1 : a⁻¹ * u * a ∈ U := by simpa using ‹U.Normal›.conj_mem u hu a⁻¹
  have h2 := hv _ h1
  have hcalc : ρ u (ρ a v) = ρ a (ρ (a⁻¹ * u * a) v) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 1
    group
  rw [hcalc, h2]

noncomputable def invariantsSubrepresentation (ρ : Representation (ZMod p) A V) (U : Subgroup A)
    [U.Normal] : Subrepresentation ρ where
  toSubmodule := Representation.invariants (ρ.comp U.subtype)
  apply_mem_toSubmodule a _ hv := apply_mem_invariants_comp_subtype a hv

@[simp]
theorem invariantsSubrepresentation_toSubmodule [U.Normal] :
    (invariantsSubrepresentation ρ U).toSubmodule
      = Representation.invariants (ρ.comp U.subtype) := (rfl)

theorem dvd_natCard_of_nontrivial [FiniteDimensional (ZMod p) V] [Nontrivial V] :
    p ∣ Nat.card V := by
  have : Finite V := Module.finite_of_finite (ZMod p)
  rw [← FiniteField.pow_finrank_eq_natCard p V]
  exact dvd_pow_self p Module.finrank_pos.ne'

theorem dvd_natCard_invariants_comp_subtype [FiniteDimensional (ZMod p) V] [Nontrivial V]
    (hU : Nat.card U = p ^ a) :
    p ∣ Nat.card (Representation.invariants (ρ.comp U.subtype)) := by
  have hfin : Finite V := Module.finite_of_finite (ZMod p)
  let _inst : MulAction U V := MulAction.compHom V (ρ.comp U.subtype)
  have hset : fixedPoints U V = (Representation.invariants (ρ.comp U.subtype) : Set V) := by
    ext v
    simp only [mem_fixedPoints, SetLike.mem_coe, Representation.mem_invariants]
    rfl
  have hcong := natCard_modEq_natCard_fixedPoints (P := U) (X := V) hU
  rw [hset] at hcong
  exact Nat.modEq_zero_iff_dvd.mp
    (hcong.symm.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_natCard_of_nontrivial (p := p) (V := V))))

theorem invariants_comp_subtype_ne_bot [FiniteDimensional (ZMod p) V] [Nontrivial V]
    (hU : Nat.card U = p ^ a) : Representation.invariants (ρ.comp U.subtype) ≠ ⊥ := by
  have : Finite V := Module.finite_of_finite (ZMod p)
  rw [← Submodule.nontrivial_iff_ne_bot, ← Finite.one_lt_card_iff_nontrivial]
  exact lt_of_lt_of_le (Fact.out (p := p.Prime)).one_lt
    (Nat.le_of_dvd Nat.card_pos (dvd_natCard_invariants_comp_subtype hU))

theorem le_ker_of_isIrreducible [FiniteDimensional (ZMod p) V] [U.Normal]
    (hU : Nat.card U = p ^ a) (hirr : ρ.IsIrreducible) : U ≤ ρ.ker := by
  have : Nontrivial V := haveI := hirr; nontrivial_of_isIrreducible ρ
  have htop : invariantsSubrepresentation ρ U = ⊤ :=
    (eq_bot_or_eq_top (invariantsSubrepresentation ρ U)).resolve_left fun h =>
      invariants_comp_subtype_ne_bot hU (congrArg Subrepresentation.toSubmodule h)
  have hall : Representation.invariants (ρ.comp U.subtype) = ⊤ := by
    have h := congrArg Subrepresentation.toSubmodule htop
    rw [invariantsSubrepresentation_toSubmodule] at h
    rw [h]
    rfl
  intro u hu
  exact LinearMap.ext fun v =>
    (mem_invariants_comp_subtype_iff v).mp (hall ▸ Submodule.mem_top) u hu

theorem isTrivial_comp_subtype_of_isIrreducible [FiniteDimensional (ZMod p) V] [U.Normal]
    (hU : Nat.card U = p ^ a) (hirr : ρ.IsIrreducible) :
    Representation.IsTrivial (ρ.comp U.subtype) :=
  ⟨fun u => le_ker_of_isIrreducible hU hirr u.2⟩

theorem eq_one_of_isIrreducible_generalLinearGroup [FiniteDimensional (ZMod p) V] [U.Normal]
    (σ : A →* LinearMap.GeneralLinearGroup (ZMod p) V) (hU : Nat.card U = p ^ a)
    (hirr : Representation.IsIrreducible ((Units.coeHom (Module.End (ZMod p) V)).comp σ))
    {u : A} (hu : u ∈ U) : σ u = 1 := by
  have h := le_ker_of_isIrreducible hU hirr hu
  ext v
  exact congrFun (congrArg (fun f : Module.End (ZMod p) V => f.toFun) h) v

end CFSG.FeitThompson

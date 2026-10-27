module

public import Mathlib.RepresentationTheory.Character
public import CFSG.FeitThompson.Representations.CommutingOperatorFiniteScalarField
public import CFSG.FeitThompson.Representations.SchurLemmaAlgebraicallyClosed

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module Representation

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] [Finite G]

noncomputable def conjClassFinset (x : G) : Finset G :=
  (ConjClasses.mk x).carrier.toFinite.toFinset

@[simp]
theorem mem_conjClassFinset {x u : G} : u ∈ conjClassFinset x ↔ IsConj x u := by
  rw [conjClassFinset, Set.Finite.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj, isConj_comm]

theorem self_mem_conjClassFinset (x : G) : x ∈ conjClassFinset x :=
  mem_conjClassFinset.2 (IsConj.refl x)

theorem card_conjClassFinset (x : G) :
    (conjClassFinset x).card = Nat.card (ConjClasses.mk x).carrier :=
  (Nat.card_eq_card_finite_toFinset _).symm

theorem conj_mem_conjClassFinset {x u : G} (hu : u ∈ conjClassFinset x) (g : G) :
    g * u * g⁻¹ ∈ conjClassFinset x :=
  mem_conjClassFinset.2 ((mem_conjClassFinset.1 hu).trans (isConj_iff.2 ⟨g, rfl⟩))

noncomputable def conjClassSum (k : Type*) [Semiring k] (x : G) : MonoidAlgebra k G :=
  ∑ u ∈ conjClassFinset x, MonoidAlgebra.of k G u

theorem conjClassSum_def (k : Type*) [Semiring k] (x : G) :
    conjClassSum k x = ∑ u ∈ conjClassFinset x, MonoidAlgebra.of k G u := (rfl)

theorem conjClassSum_mem_center (k : Type*) [CommSemiring k] (x : G) :
    conjClassSum k x ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of g =>
      rw [conjClassSum_def, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_nbij' (i := fun u => g * u * g⁻¹) (j := fun u => g⁻¹ * u * g)
        (fun u hu => conj_mem_conjClassFinset hu g) (fun u hu => ?_) (fun u _ => by group)
        (fun u _ => by group) (fun u _ => ?_)
      · simpa using conj_mem_conjClassFinset hu g⁻¹
      · rw [← map_mul, ← map_mul]
        congr 1
        group
  | add p q hp hq => simp [mul_add, add_mul, hp, hq]
  | smul r p hp => rw [Algebra.smul_def, mul_assoc, hp, ← mul_assoc, Algebra.commutes, mul_assoc]

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

omit [Finite G] in
theorem char_eq_of_isConj (ρ : Representation k G V) {x u : G} (h : IsConj x u) :
    ρ.character u = ρ.character x := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact ρ.char_conj x c

theorem commute_asAlgebraHom_conjClassSum (ρ : Representation k G V) (x g : G) :
    Commute (ρ.asAlgebraHom (conjClassSum k x)) (ρ g) := by
  have h := (Subalgebra.mem_center_iff.1 (conjClassSum_mem_center k x)) (MonoidAlgebra.of k G g)
  have h2 := congrArg ρ.asAlgebraHom h
  rw [map_mul, map_mul, Representation.asAlgebraHom_of] at h2
  exact h2.symm

theorem trace_asAlgebraHom_conjClassSum [FiniteDimensional k V] (ρ : Representation k G V) (x : G) :
    LinearMap.trace k V (ρ.asAlgebraHom (conjClassSum k x)) =
      (Nat.card (ConjClasses.mk x).carrier : k) * ρ.character x := by
  rw [conjClassSum_def, map_sum, map_sum, Finset.sum_congr rfl
    (g := fun _ => ρ.character x) (fun u hu => ?_), Finset.sum_const, card_conjClassFinset,
    nsmul_eq_mul]
  rw [Representation.asAlgebraHom_of]
  exact char_eq_of_isConj ρ (mem_conjClassFinset.1 hu)

omit [Finite G] in
theorem character_one_ne_zero [CharZero k] [FiniteDimensional k V] (ρ : Representation k G V)
    [ρ.IsIrreducible] : ρ.character 1 ≠ 0 := by
  have : Nontrivial V := nontrivial_of_isIrreducible ρ
  rw [Representation.char_one]
  exact Nat.cast_ne_zero.2 (Module.finrank_pos (R := k) (M := V)).ne'

theorem asAlgebraHom_conjClassSum_eq_smul_one [IsAlgClosed k] [CharZero k] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] (x : G) :
    ρ.asAlgebraHom (conjClassSum k x) =
      ((Nat.card (ConjClasses.mk x).carrier : k) * ρ.character x / ρ.character 1) •
        (1 : Module.End k V) := by
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.exists_eq_smul_one_of_commute ρ
    (ρ.asAlgebraHom (conjClassSum k x)) (commute_asAlgebraHom_conjClassSum ρ x)
  have htr := trace_asAlgebraHom_conjClassSum ρ x
  rw [hc, map_smul, LinearMap.trace_one, ← Representation.char_one ρ, smul_eq_mul] at htr
  rw [hc]
  congr 1
  exact (eq_div_iff (character_one_ne_zero ρ)).2 htr

theorem asAlgebraHom_conjClassSum_apply [IsAlgClosed k] [CharZero k] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] (x : G) (v : V) :
    ρ.asAlgebraHom (conjClassSum k x) v =
      ((Nat.card (ConjClasses.mk x).carrier : k) * ρ.character x / ρ.character 1) • v := by
  rw [asAlgebraHom_conjClassSum_eq_smul_one ρ x]
  simp

end CFSG.FeitThompson

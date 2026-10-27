module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Cycle.Concrete
public meta import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Aut6Inputs
public import Certificates.Certificate4035

public section

namespace CFSG.QuasithinUnique.A5.Aut6

open Equiv

theorem map_ev {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (a b : M) (w : List Bool) :
    f (ev a b w) = ev (f a) (f b) w := by
  induction w with
  | nil => simp [ev]
  | cons c w ih => cases c <;> simp [ev, ih]

theorem a6_fixed_five_of_word (w : P6 → List Bool)
    (hw : ∀ g : A6, ev ga gb (w (g : P6)) = (g : P6))
    (hfin : ∀ x y : A6, IsCand w x y → IsInv w x y → ¬ IsConj w x y → HasFix w x y)
    (ι : A6 ≃* A6) (hι : ∀ a, ι (ι a) = a)
    (hnc : ¬ ∃ σ : P6, ∀ a : A6, ((ι a : A6) : P6) = σ⁻¹ * (a : P6) * σ) :
    ∃ a : A6, orderOf a = 5 ∧ ι a = a := by
  obtain ⟨x, hx⟩ : ∃ x : A6, x = ι ga' := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : A6, y = ι gb' := ⟨_, rfl⟩
  have hphi : ∀ g : A6, phi w (x : P6) (y : P6) (g : P6) = ((ι g : A6) : P6) := by
    intro g
    have h1 : ev ga' gb' (w (g : P6)) = g := by
      apply Subtype.ext
      have := map_ev (alternatingGroup (Fin 6)).subtype ga' gb' (w (g : P6))
      simp only [Subgroup.coe_subtype] at this
      rw [this]
      exact hw g
    have h2 : ι (ev ga' gb' (w (g : P6))) = ev (ι ga') (ι gb') (w (g : P6)) :=
      map_ev (ι.toMonoidHom) ga' gb' _
    have h3 := map_ev (alternatingGroup (Fin 6)).subtype x y (w (g : P6))
    simp only [Subgroup.coe_subtype] at h3
    have h4 : ev x y (w (g : P6)) = ι g := by
      rw [h1] at h2
      rw [hx, hy]
      exact h2.symm
    unfold phi
    rw [← h3, h4]
  have hcand : IsCand w x y := by
    intro g
    constructor
    · have : ((g : P6) * ga) = ((g * ga' : A6) : P6) := rfl
      rw [this, hphi (g * ga'), hphi g]
      rw [hx]
      simp
    · have : ((g : P6) * gb) = ((g * gb' : A6) : P6) := rfl
      rw [this, hphi (g * gb'), hphi g]
      rw [hy]
      simp
  have hinv : IsInv w x y := by
    intro g
    rw [hphi g, hphi (ι g)]
    simp [hι]
  have hconj : ¬ IsConj w x y := by
    rintro ⟨σ, hσ⟩
    exact hnc ⟨σ, fun a => by rw [← hphi a]; exact hσ a⟩
  obtain ⟨a, ha5, ha1, hfix⟩ := hfin x y hcand hinv hconj
  refine ⟨a, ?_, ?_⟩
  · have h5 : a ^ 5 = 1 := Subtype.ext (by simpa using ha5)
    have h1 : a ≠ 1 := fun h => ha1 (by simp [h])
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime h5 h1
  · apply Subtype.ext
    rw [← hphi a]
    exact hfix

theorem finite_fact :
    ∀ x y : A6, IsCand word x y → IsInv word x y → ¬ IsConj word x y →
    HasFix word x y :=
  Certificates.certificate4035.1

theorem word_spec : ∀ g : A6, ev ga gb (word (g : P6)) = (g : P6) :=
  Certificates.certificate4035.2

theorem a6_fixed_five (ι : A6 ≃* A6) (hι : ∀ a, ι (ι a) = a)
    (hnc : ¬ ∃ σ : P6, ∀ a : A6, ((ι a : A6) : P6) = σ⁻¹ * (a : P6) * σ) :
    ∃ a : A6, orderOf a = 5 ∧ ι a = a :=
  a6_fixed_five_of_word word word_spec finite_fact ι hι hnc

end CFSG.QuasithinUnique.A5.Aut6

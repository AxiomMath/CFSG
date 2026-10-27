module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Quat

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open scoped commutatorElement

section Aut

variable {A : Type*} [Group A] (T : Subgroup A) [T.Normal]

@[expose] def autCentOf (X : Subgroup A) : Subgroup (MulAut ↥T) :=
  Subgroup.centralizer ((MulAut.conjNormal (H := T)) '' (X : Set A))

variable {T}

theorem mem_autCentOf_iff {X : Subgroup A} {ψ : MulAut ↥T} :
    ψ ∈ autCentOf T X ↔ ∀ s ∈ X, ψ * MulAut.conjNormal s = MulAut.conjNormal s * ψ := by
  unfold autCentOf
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    exact (h _ ⟨s, hs, rfl⟩).symm
  · rintro h _ ⟨s, hs, rfl⟩
    exact (h s hs).symm

theorem conjNormal_eq_one (hC : Subgroup.centralizer (T : Set A) = ⊥) {g : A}
    (h : MulAut.conjNormal (H := T) g = 1) : g = 1 := by
  have : g ∈ Subgroup.centralizer (T : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := congrArg (fun φ : MulAut ↥T => ((φ ⟨t, ht⟩ : ↥T) : A)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [hC, Subgroup.mem_bot] at this
  exact this

theorem conjNormal_injective (hC : Subgroup.centralizer (T : Set A) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := T)) := by
  rw [injective_iff_map_eq_one]
  exact fun g => conjNormal_eq_one hC

theorem conjNormal_mem_autCentOf {X : Subgroup A} {g : A} (hg : ∀ s ∈ X, g * s = s * g) :
    (MulAut.conjNormal (H := T) g) ∈ autCentOf T X :=
  mem_autCentOf_iff.mpr fun s hs => by rw [← map_mul, ← map_mul, hg s hs]

end Aut

section Perfect

variable {A : Type*} [Group A]

@[expose] noncomputable def perfectCore (H : Subgroup A) : Subgroup A :=
  (derivedSeries ↥H (Nat.card ↥H)).map H.subtype

theorem perfectCore_le (H : Subgroup A) : perfectCore H ≤ H :=
  Subgroup.map_subtype_le _

end Perfect

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

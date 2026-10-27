module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Subgroup

variable {X Y : Type*} [Group X] [Group Y]

theorem map_centralizer_eq_image (e : X ≃* Y) (S : Set X) :
    (centralizer S).map e.toMonoidHom = centralizer (e '' S) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    rintro _ ⟨s, hs, rfl⟩
    have h := congrArg e (hx s hs)
    simpa [map_mul] using h
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply e.injective
    rw [map_mul, map_mul]
    exact hy (e s) ⟨s, hs, rfl⟩

end CFSG.AGLEmbeddingD2.Wilson.Proving

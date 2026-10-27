module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.SL2Modules

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

@[expose] def subgroupRep (L : Subgroup (V ≃ₗ[F] V)) : Representation F L V :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp L.subtype

theorem exists_smul_of_finrank_one {D W : Type*} [Field D] [AddCommGroup W] [Module D W]
    (h : Module.finrank D W = 1) (f : Module.End D W) : ∃ c : D, ∀ w, f w = c • w := by
  obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.mp h
  obtain ⟨c, hc⟩ := hspan (f v)
  refine ⟨c, fun w => ?_⟩
  obtain ⟨d, rfl⟩ := hspan w
  rw [map_smul, ← hc, smul_comm]

theorem commute_of_finrank_one {D W : Type*} [Field D] [AddCommGroup W] [Module D W]
    (h : Module.finrank D W = 1) (f f' : Module.End D W) : f * f' = f' * f := by
  obtain ⟨c, hc⟩ := exists_smul_of_finrank_one h f
  obtain ⟨c', hc'⟩ := exists_smul_of_finrank_one h f'
  apply LinearMap.ext
  intro w
  simp only [Module.End.mul_apply, hc, hc']
  exact smul_comm c c' w

theorem eq_smul_of_commute_irreducible [Finite F] [Module.Finite F V]
    (hV : Module.finrank F V = 3) (L : Subgroup (V ≃ₗ[F] V))
    (hirr : ∀ W : Submodule F V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnc : ∃ g ∈ L, ∃ h ∈ L, g * h ≠ h * g)
    (a : V →ₗ[F] V) (ha : ∀ g ∈ L, ∀ v, a (g v) = g (a v)) :
    ∃ c : F, ∀ v, a v = c • v := by
  classical
  have hVnt : Nontrivial V := by
    rw [← Module.finrank_pos_iff (R := F)]
    omega
  have hVfin : Finite V := Module.finite_of_finite F
  let ρ := subgroupRep L
  have : Fact ρ.IsIrreducible := ⟨(isIrreducible_iff ρ).2 ⟨hVnt, fun U hU =>
    hirr U (fun g hg w hw => hU ⟨g, hg⟩ w hw)⟩⟩
  have hmul : Module.finrank F (EndRing ρ) * Module.finrank (EndRing ρ) V = 3 := by
    rw [Module.finrank_mul_finrank F (EndRing ρ) V, hV]
  have hdvd : Module.finrank F (EndRing ρ) ∣ 3 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with he | he
  ·
    obtain ⟨ψ, hψ⟩ := (mem_endRing_iff ρ a).mpr (fun g v => ha g.1 g.2 v)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : EndRing ρ) one_ne_zero).mp he ψ
    refine ⟨c, fun v => ?_⟩
    have h1 : a v = ψ v := (congrFun hψ v).symm
    rw [h1, ← hc]
    simp
  ·
    rw [he] at hmul
    have hm : Module.finrank (EndRing ρ) V = 1 := by omega
    exfalso
    obtain ⟨g, hg, h, hh, hne⟩ := hnc
    apply hne
    have := commute_of_finrank_one hm (repD ρ ⟨g, hg⟩) (repD ρ ⟨h, hh⟩)
    apply LinearEquiv.ext
    intro v
    have h2 := congrArg (fun f : Module.End (EndRing ρ) V => f v) this
    exact h2

end CFSG.QuasithinUnique.Setup.X3

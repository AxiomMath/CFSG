module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CayleyIso

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

theorem nonempty_mulEquiv_of_cayley_enum {G T : Type*} [Group G] [Group T] (X : Subgroup G)
    (gS : List G) (gT : List T) (hlen : gS.length = gT.length) (hX : X = closure {x | x ∈ gS})
    {n : ℕ} (e : Fin n → G) (fv : Fin n → T) (he : Function.Injective e) (heX : ∀ k, e k ∈ X)
    (hcov : ∀ x ∈ X, ∃ k, e k = x) (k₀ : Fin n) (he0 : e k₀ = 1) (hf0 : fv k₀ = 1)
    (hstep : ∀ (k : Fin n) (i : Fin gS.length),
      ∃ j : Fin n, e j = e k * gS.get i ∧ fv j = fv k * gT.get (Fin.cast hlen i))
    (hinj : Function.Injective fv) (hsurj : Function.Surjective fv) : Nonempty (↥X ≃* T) := by
  haveI : Nonempty (Fin n) := ⟨k₀⟩
  classical
  let f : G → T := fun g => fv (Function.invFun e g)
  have hef : ∀ k, Function.invFun e (e k) = k := fun k => Function.leftInverse_invFun he k
  have hfe : ∀ k, f (e k) = fv k := fun k => by simp only [f, hef]
  have hrange : ∀ x ∈ X, e (Function.invFun e x) = x := by
    intro x hx
    obtain ⟨k, hk⟩ := hcov x hx
    rw [← hk, hef]
  refine nonempty_mulEquiv_of_cayley X gS gT hlen hX f ?_ ?_ ?_ ?_
  · rw [← he0, hfe, hf0]
  · intro x hx i
    obtain ⟨k, rfl⟩ := hcov x hx
    obtain ⟨j, hj1, hj2⟩ := hstep k i
    rw [← hj1, hfe, hfe, hj2]
  · intro x hx y hy hxy
    have h1 : Function.invFun e x = Function.invFun e y := hinj hxy
    rw [← hrange x hx, ← hrange y hy, h1]
  · intro t
    obtain ⟨k, rfl⟩ := hsurj t
    exact ⟨e k, heX k, hfe k⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData

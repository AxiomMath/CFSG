module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95ExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint

theorem ivk95_g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk95Empty (fun X _ => LieModel X .G2 0 p f) := by
  intro p f hp hp2 hf
  refine ivk95_empty_of_cfg fun J _ _ hJ z h => ?_
  obtain ⟨F, hF, hFin, S, hcard, -⟩ := GHInv.exists_shape_G2 hp hp2 hJ z h.ord
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  exact h.false_of_shape hodd hodd S

theorem ivk95_d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk95Empty (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro p f hp hp2 hf
  refine ivk95_empty_of_cfg fun J _ _ hJ z h => ?_
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, -⟩ :=
    GHInv.exists_shape_D4 hp hp2 hJ z h.ord
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  refine h.false_of_shape ?_ ?_ S
  · rw [hc₁]
    exact hodd.pow
  · rw [hc₂]
    exact hodd

end CFSG.GH74.GLS.IVK.Proofs2

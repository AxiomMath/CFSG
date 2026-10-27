module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FG2SModel
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FD4SChar
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87D4Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Certs


theorem fd4_noPNorm_model {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (hm : LieModel Y .trialityD4 0 r f) :
    ∀ g : Y, g * g = 1 → g ≠ 1 → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup Y,
      IsPGroup p ↥X → X ≠ ⊥ → centralizer ({g} : Set Y) ≤ normalizer (X : Set Y) → False := by
  intro g hg hg1 p _ hp2 X hX hX1 hN
  by_cases hpr : p = r
  · subst hpr
    exact td4_noPNorm_char hr hr2 hf hm hg hg1 hX hX1 hN
  · exact td4_noPNorm_cross hr hr2 hf hm hg hg1 hp2 hpr hX hX1 hN

theorem fd4_invol_S {Y : Type} [Group Y] [Finite Y] (h : FD4 Y) (α : MulAut Y) (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : InvolFactS α := by
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  by_cases hin : α ∈ (MulAut.conj : Y →* MulAut Y).range
  · obtain ⟨ψ⟩ := equiv_modelUniv_d4 hp hp2 hf hm
    have hZ : center Y = ⊥ :=
      center_eq_bot_of_mulEquiv_target ψ
        (RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0 hf)
    exact Or.inr (noPNorm_of_inner hZ (fd4_noPNorm_model hp hp2 hf hm) hin hα2 hα1)
  · refine Or.inl (Or.inr ?_)
    have hα : α ^ 2 = 1 := by rw [sq]; exact hα2
    obtain ⟨e', he', hsimple, hnab, hmod⟩ := td4_outer_involution_fixed hp hp2 hf hm α hα hin
    have : IsSimpleGroup ↥(fixSub α) := hsimple
    exact ⟨fixSub α, le_rfl, hsimple, hnab, td4_bad_of_model hnab hp hp2 he' hmod⟩

theorem cellFacts_FD4_S (hMult : D4Mult) : CellFactsS FD4 where
  iso := fun e h => fd4_iso e h
  mult := fun _ _ _ hL hZ2 hF => fd4_mult hMult hL hZ2 hF
  outAbel := fun _ _ _ h => fd4_outAbel h
  invol := fun _ _ _ h α hα2 hα1 => fd4_invol_S h α hα2 hα1

theorem cell87_FD4_S (hMult : D4Mult) : Cell87 FD4 :=
  cell87_of_factsS (cellFacts_FD4_S hMult)

end Certs

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

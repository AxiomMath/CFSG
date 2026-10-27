module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911OddCycFix
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911ExcCommon
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FD4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87D4Out
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTD4Odd

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Cell

theorem td4_fixOddFree {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hm : LieModel Y .trialityD4 0 p f) (α : MulAut Y) (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : FixOddFree α := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases hin : α ∈ (MulAut.conj : Y →* MulAut Y).range
  · obtain ⟨ψ⟩ := equiv_modelUniv_d4 hp hp2 hf hm
    have hadm : StatedLieAdmissible .trialityD4 0 p f := ⟨Fact.out, hf, rfl⟩
    have hZ : center Y = ⊥ :=
      center_eq_bot_of_mulEquiv_target ψ
        (CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0 hf)
    have hO : InvOddCore Y :=
      invOddCore_of_equiv ψ (CFSG.ClassicalInvolution.Asc77.thm5IH_td4_oddCoreTrivial hp2 hadm)
    exact fixOddFree_of_inner hZ hO hin hα2 hα1
  · have hα : α ^ 2 = 1 := by rw [sq]; exact hα2
    obtain ⟨e', he', hsimple, hnab, -⟩ := td4_outer_involution_fixed hp hp2 hf hm α hα hin
    exact fixOddFree_of_simple_nonabelian α hsimple hnab

theorem oddCoreCyclic_td4 {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hm : LieModel Y .trialityD4 0 p f) :
    ∃ (C : Type) (_ : Group C) (_ : Finite C) (_ : Y ≃* C), OddCoreCyclic C := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have htw : TwistedChevalleyModel Y .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  have : Finite (graphFixedRootGroup TwistTag.D4 M σ.toRingHom) := Finite.of_equiv Y e.toEquiv
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, -, -, -, hcen, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf M hM σ hσ
  have : IsCyclic (M ≃+* M) := by
    obtain ⟨-, -, -, hcyc, -⟩ := odd_triality_exact_automorphism_normal_form hp hp2 hf M hM σ hσ
    exact hcyc
  have hmC : LieModel (graphFixedRootGroup TwistTag.D4 M σ.toRingHom) .trialityD4 0 p f :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm
  refine ⟨graphFixedRootGroup TwistTag.D4 M σ.toRingHom, inferInstance, inferInstance, e, ?_⟩
  exact oddCoreCyclic_of_outCyc_fix hcen (isCyclic_outer_of_hom Θ hΘker)
    fun α hα2 hα1 => td4_fixOddFree hp hp2 hf hmC α hα2 hα1

theorem core911_d4 : Core911D4 := by
  intro Y _ _ _ _ hF
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := hF
  obtain ⟨C, _, _, e, hC⟩ := oddCoreCyclic_td4 hp hp2 hf hm
  exact no911_of_mulEquiv e (no911_of_oddCoreCyclic hC)

end Cell

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KNGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FD4
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTD4Odd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87D4Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem kay_D4 :
    KAY FD4 := by
  refine kay_of_kaAll ?_
  intro Y _ _ hY _ α hα2 hα1
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := hY
  have : Fact p.Prime := ⟨hp⟩
  have htw : TwistedChevalleyModel Y .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  obtain ⟨-, -, ⟨Θ₀, -, -, hker₀, -⟩, hcyc, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf M hM σ hσ
  have : IsCyclic (M ≃+* M) := hcyc
  obtain ⟨Θ, hΘ⟩ := kn_hom_of_mulEquiv e Θ₀ hker₀
  have hZY : center Y = ⊥ := center_eq_bot_of_mulEquiv_target e hZ
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    kn_conj_injective_of_center_bot hZY
  have hNoP : KANoP α := by
    by_cases hin : α ∈ innSub Y
    · have hadm : StatedLieAdmissible .trialityD4 0 p f := ⟨Fact.out, hf, rfl⟩
      obtain ⟨ψ⟩ := equiv_modelUniv_d4 hp hp2 hf hm
      have hO : InvOddCore Y := invOddCore_of_equiv ψ
        (fun u hu2 hu1 N hN hNn hNodd =>
          CFSG.ClassicalInvolution.Asc77.thm5IH_td4_oddCoreTrivial hp2 hadm u hu2 hu1 N hN hNn
            hNodd)
      exact kaNoP_of_fixOddFree (fixOddFree_of_inner hZY hO hin hα2 hα1)
    · obtain ⟨e', -, hsimple, hnab, -⟩ :=
        td4_outer_involution_fixed hp hp2 hf hm α (by rw [sq]; exact hα2) hin
      exact kaNoP_of_simple hsimple hnab
  exact ka_all_of_noP hinj hNoP (kaOutCyc_of_hom Θ hΘ) (ka_hOut_of_hom Θ hΘ α)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

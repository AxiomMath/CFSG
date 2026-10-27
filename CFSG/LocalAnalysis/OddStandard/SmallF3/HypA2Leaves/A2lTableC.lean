module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Bridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCQuot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCAlt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCOdd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCSpor
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEven
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddAssemblyHolds
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpOddChar

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup _root_.Certificates CFSG.Blueprint CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem res_hs {K : Type} [Group K] (h : NativeSporadic.IsSporadic (K ⧸ center K) .HS) :
    HypA2.IsResidualA2 K :=
  Or.inr (Or.inr (Or.inl h))

private theorem res_psp {K : Type} [Group K] (h : LieModel (K ⧸ center K) .PSp 2 2 2) :
    HypA2.IsResidualA2 K :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem res_psl5 {K : Type} [Group K] (h : LieModel (K ⧸ center K) .PSL 5 2 1) :
    HypA2.IsResidualA2 K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

private theorem res_psu5 {K : Type} [Group K] (h : LieModel (K ⧸ center K) .PSU 5 2 1) :
    HypA2.IsResidualA2 K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

private theorem res_g2 {K : Type} [Group K] (h : LieModel (K ⧸ center K) .G2 0 2 2) :
    HypA2.IsResidualA2 K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

private theorem res_psl42 {K : Type} [Group K] (h : LieModel (K ⧸ center K) .PSL 4 2 2) :
    HypA2.IsResidualA2 K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

private theorem res_alt {K : Type} [Group K] {m : ℕ} (hm : 4 ≤ m) (hbot : center K = ⊥)
    (e : K ≃* alternatingGroup (Fin (2 * m))) : HypA2.IsResidualA2 K :=
  Or.inr (Or.inl ⟨m, hm, hbot, ⟨e⟩⟩)

section


theorem tableC_holds : HypA2.TableC := by
  intro K _ _ hK hZ hcat σ hσ X hXF hX hF hI hnF
  have hS : TCSmall (↥X ⧸ Open.fusionZStar ↥X) := a2l_tcSmall_of_isFStar hF hI
  have hXtop : X ≠ ⊤ := by
    intro htop
    exact hnF ((HypA2.isFStar_congr ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)).mp hF)
  obtain ⟨σ', -, hP, ⟨eP⟩⟩ := a2l_properFixedComponent_quotient hK hσ hXF hX hXtop
  have hS' := hS.of_mulEquiv eP
  have hsimple : IsSimpleGroup (K ⧸ center K) := hK.2.1
  have hna : ∃ a b : K ⧸ center K, a * b ≠ b * a := hK.2.2
  have halt : ∀ m : ℕ, 5 ≤ m → (K ⧸ center K ≃* alternatingGroup (Fin m)) →
      HarrisLit.IsSimpleChevalleyOver 3 (K ⧸ center K) ∨ HypA2.IsResidualA2 K := by
    intro m hm5 θ
    rcases a2l_alt_arm hm5 θ hP hS' with hm6 | ⟨m', hm', rfl, u, hu, p, q, s, t, hpq, hps, hpt,
        hqs, hqt, hst, hθu⟩
    · subst hm6
      exact Or.inl (a2l_isSimpleChevalleyOver_three_of_alt_six ⟨θ⟩)
    · have hu2 : u * u = 1 := by
        apply θ.injective
        apply Subtype.ext
        rw [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, hθu]
        exact a2l_doubleSwap_sq hpq hst hps hpt hqs hqt
      obtain ⟨g, hg, hgu⟩ := a2l_exists_involution_lift hZ hF hS hu hu2
      have hbot : center K = ⊥ :=
        a2l_center_eq_bot_of_lift_deg hK hZ (by omega) θ hg hpq hps hpt hqs hqt hst (by
          rw [show (QuotientGroup.mk g : K ⧸ center K) = u from hgu]
          exact hθu)
      exact Or.inr (res_alt hm' hbot
        (((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans θ))
  haveI := hsimple
  rcases (Milestones.ct_catalog_nonabelian_type_partition _ hna).mp hcat with
    ⟨m, hm, ⟨θ⟩⟩ | ho | ⟨τ, n, f, -, hL⟩ | hsp
  · exact halt m hm θ
  · exact Or.inl (a2l_odd_arm CatLeafProof.gls3OddLieAutComponentsInput_holds
      CatLeafProof.lieOrderFormulasInput GS82PumpInputs.oddLieCharUnique_holds
      (fixedTwoComponentsQuasisimple_of_oddLieType hna ho) ho hP hS')
  · rcases a2l_even_arm CatLeafProof.lieOrderFormulasInput hsimple hna hL hP hS' with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨θ⟩ := GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hL
      exact halt 8 (by norm_num) θ
    · exact Or.inr (res_psl42 hL)
    · exact Or.inr (res_psl5 hL)
    · exact Or.inl ⟨.PSp, 2, 1, GH74.Exceptional.lieModel_PSp_two_three_of_lieModel_PSU_four_two hL⟩
    · exact Or.inr (res_psu5 hL)
    · exact Or.inr (res_psp hL)
    · exact Or.inr (res_g2 hL)
  · exact Or.inr (res_hs (a2l_spor_arm hna hsp hP hS'))

end

end CFSG.OddStandard.SmallF3.HypA2Leaves

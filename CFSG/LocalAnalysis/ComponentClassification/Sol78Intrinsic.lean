module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankOneCover
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalSimpleFitting
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X]

noncomputable def generalizedFittingEquiv (hnonab : ∃ a b : X, a * b ≠ b * a) :
    GeneralizedFitting.subgroup X ≃* X :=
  (MulEquiv.subgroupCongr (SmallLocal.simple_generalized_fitting_self_local X hnonab).2.2.2.2).trans
    Subgroup.topEquiv

omit [Finite X] [IsSimpleGroup X] in
theorem open_isSubnormal_of_isPComponent' {C J : Subgroup X} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) : Open.IsSubnormal J C := by
  obtain ⟨-, -, hsub, -, -⟩ := hJ
  have h := Components.chain_of_mathlib_subnormal hsub
  have hmap : ∀ {H K : Subgroup C}, Open.IsSubnormal H K →
      Open.IsSubnormal (H.map C.subtype) (K.map C.subtype) := by
    intro H K hHK
    induction hHK with
    | refl H => exact .refl _
    | @step H M K hHM hn _ ih =>
      refine .step (map_mono hHM) ?_ ih
      rw [normal_subgroupOf_iff (map_mono hHM)]
      rintro _ _ ⟨h, hh, rfl⟩ ⟨m, hm, rfl⟩
      exact ⟨m * h * m⁻¹, (normal_subgroupOf_iff hHM).mp hn h m hh hm, by simp⟩
  have h' := hmap h
  rwa [subgroupOf_map_subtype, inf_eq_left.mpr hJC, ← MonoidHom.range_eq_map,
    range_subtype] at h'

theorem sporadic_of_isDoublePair_of_mem (h2An : GSThmB.Solomon2AnInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hS : SolAltLit.SchurAlternatingMultiplierInput)
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hU : ¬ OutcomeLocal.UOutcome X) {x : X}
    {L : Subgroup X} {m : ℕ} (hP : IsDoublePair x L m) (hxL : x ∈ L) :
    Nonempty (X ≃* Blueprint.NativeSporadic.M11) ∨ Nonempty (X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.Ly) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hperf, hq, hZ2, ⟨e⟩⟩ := hP.coreQuotient hS
  obtain ⟨hx, hLx, hL, hmo, hm7, -, -⟩ := hP
  rcases (show m = 7 ∨ 8 ≤ m by omega) with rfl | hm8
  ·
    have hrank : CFSG.pRank 2 L ≤ 1 := by
      have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 L) := fun h =>
        Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
      rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd]
      exact pRank_two_le_one_of_alternating_seven hZ2 e
    have hA : IsQuasisimple (L ⧸ CFSG.oddCore L) :=
      LocalCores.isQuasisimple_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore L)).symm hq
    obtain ⟨-, -, -, -, -, -, r, hr, hSJ, -⟩ :=
      UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrank hA
    obtain ⟨S⟩ : Nonempty (Sylow 2 L) := inferInstance
    obtain ⟨eS⟩ := hSJ S
    let eF : Open.genFittingFStar X ≃* X :=
      (MulEquiv.subgroupCongr
        (StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnonab)).trans
        Subgroup.topEquiv
    have : IsSimpleGroup (Open.genFittingFStar X) := eF.isSimpleGroup
    have hFnonab : ∃ a b : Open.genFittingFStar X, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnonab
      exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
    have hcore : Open.classicalInvolutionOddCore L = pPrimeCore 2 L :=
      oddCore_eq_pPrimeCore L
    have hwit : Open.classicalInvolutionWitness L := by
      refine .inr ?_
      have key : ∀ (N : Subgroup L) [N.Normal], N = pPrimeCore 2 L →
          Open.IsQuasisimple (L ⧸ N) ∧ Nat.card (center (L ⧸ N)) = 2 ∧
            Nonempty ((L ⧸ N) ⧸ center (L ⧸ N) ≃* alternatingGroup (Fin 7)) := by
        intro N _ hN
        subst hN
        exact ⟨⟨hq.1.commutator_eq_top, hq.2.1⟩, hZ2, ⟨e⟩⟩
      exact key _ hcore
    have hout := (hCI X hFnonab x hx L hxL (open_isSubnormal_of_isPComponent' hLx hL) S
      ⟨r, hr, ⟨eS⟩⟩).1 hwit
    rcases hout with h | h
    · exact absurd (Or.inl ((ClassicalInvolution.oddLieType_congr
        (generalizedFittingEquiv hnonab)).2 ((ClassicalInvolution.oddLieType_congr eF).1 h))) hU
    · exact Or.inl ((ClassicalInvolution.isSporadic_congr eF).1 h)
  ·
    rcases h2An X x hx L m hm8 hLx hL hxL hperf hZ2 ⟨e⟩ with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end CFSG.ComponentClassification.Sol78

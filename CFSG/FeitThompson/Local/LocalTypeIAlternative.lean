module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NonTIFittingNilpotentCoreBetaExclusion
import CFSG.FeitThompson.Local.HallCoreLargestNilpotentNormalHall
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.Local.Omega1CentralizerCommutatorBound
import CFSG.FeitThompson.Representations.TINormalCentralSectionGeometry
import CFSG.FeitThompson.OddOrder.FreeActionKernelCongruence
import CFSG.FeitThompson.Definitions.NormalSylowHallCore
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise _root_.CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] [Finite G] {M K U : Subgroup G}

namespace LocalTypeIAlternative

omit [Finite G] in
theorem le_normalizer_hallCoreIn (M : Subgroup G) :
    M ≤ normalizer ((hallCoreIn M : Subgroup G) : Set G) := by
  rw [hallCoreIn_eq]
  exact le_normalizer_map_subtype_of_characteristic _ M.le_normalizer

theorem exists_isSylowProduct (X : Subgroup G) (π : Set ℕ) :
    ∃ Y : Subgroup G, IsSylowProduct Y X π := by
  classical
  refine ⟨_, fun p => if hp : p.Prime then
      have := Fact.mk hp
      ((Classical.arbitrary (Sylow p ↥X) : Subgroup ↥X)).map X.subtype
    else ⊥, fun p _ _ => ?_, rfl⟩
  by_cases hp : p.Prime
  · have := Fact.mk hp
    refine ⟨?_, ?_⟩
    · simp only [dif_pos hp]
      exact Subgroup.map_subtype_le _
    · simp only [dif_pos hp]
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact (Classical.arbitrary (Sylow p ↥X)).card_eq_multiplicity
  · refine ⟨?_, ?_⟩
    · simp only [dif_neg hp]
      exact bot_le
    · simp only [dif_neg hp, Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero,
        Subgroup.card_bot]

end LocalTypeIAlternative

open LocalTypeIAlternative

theorem hallCoreIn_le_mixedFitting (M : Subgroup G) : hallCoreIn M ≤ mixedFitting M := by
  rw [hallCoreIn_eq, mixedFitting_eq]
  exact Subgroup.map_mono hallCore_le_fittingRaw

theorem normalizer_sharp_hallCoreIn_eq (hG : IsFBGAmbient G) (hM : IsCoatom M)
    (hne : hallCoreIn M ≠ ⊥) : normalizer (sharp (hallCoreIn M)) = M := by
  have := hG.isSimpleGroup
  rw [sharp_eq, normalizer_sdiff_singleton_one]
  exact normalizer_eq_of_isCoatom hM hne (hallCoreIn_le M) (le_normalizer_hallCoreIn M)

theorem natCard_dvd_sub_one_of_forall_inf_centralizer_eq_bot {H Z W : Subgroup G} (hZH : Z ≤ H)
    (hWZ : W ≤ normalizer (Z : Set G))
    (hfree : ∀ w ∈ W, w ≠ 1 → H ⊓ centralizer {w} = ⊥) :
    Nat.card ↥W ∣ Nat.card ↥Z - 1 := by
  let _ : MulDistribMulAction ↥W ↥Z := MulDistribMulAction.compHom ↥Z (Subgroup.inclusion hWZ)
  refine card_dvd_card_sub_one_of_smul_eq_self ↥W ↥Z ?_
  intro z hz w hw
  by_contra hw1
  have hcoe : ((w : G)) * (z : G) * ((w : G))⁻¹ = (z : G) := congrArg Subtype.val hw
  have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hmem : (z : G) ∈ H ⊓ centralizer {(w : G)} :=
    Subgroup.mem_inf.2 ⟨hZH z.2, Subgroup.mem_centralizer_singleton_iff.2 (by
      calc (z : G) * (w : G) = ((w : G) * (z : G) * ((w : G))⁻¹) * (w : G) := by rw [hcoe]
        _ = (w : G) * (z : G) := by group)⟩
  rw [hfree (w : G) w.2 hw1', Subgroup.mem_bot] at hmem
  exact hz (Subtype.ext hmem)

theorem ne_bot_of_isLocalKappaSetup_of_eq_bot
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_local_nilpotent_hall_core.{u})
    (hG : IsFBGAmbient G) (hsetup : IsLocalKappaSetup M K U) (hK : K = ⊥) : U ≠ ⊥ := by
  intro hU
  obtain ⟨⟨hHbot, -, hSM, -⟩, -⟩ := h₃ G hG M K U hsetup
  have hMS : M = sigmaCore M := by
    have h := hsetup.semidirect_M.sup_eq
    rw [hK, hU] at h
    simpa using h.symm
  have : Group.IsSolvable ↥M := hG.isSolvable M hsetup.isCoatom.1
  have hMbot : M = ⊥ := eq_bot_of_isSolvable_of_le_commutator_self M (hMS.le.trans hSM)
  exact absurd (le_bot_iff.1 (hMbot ▸ hallCoreIn_le M)) hHbot.ne'

theorem exists_isFittingOverlapSetup_of_not_disjoint (hM : IsCoatom M) {g : G} (hgM : g ∉ M)
    (hd : ¬ Disjoint (sharp (hallCoreIn M)) (MulAut.conj g '' sharp (hallCoreIn M))) :
    ∃ X : Subgroup G, IsFittingOverlapSetup M X g⁻¹ := by
  rw [Set.not_disjoint_iff] at hd
  obtain ⟨x, ⟨hxH, hx1⟩, y, ⟨hyH, hy1⟩, hxy⟩ := hd
  refine ⟨mixedFitting M ⊓ conjSubgroup (mixedFitting M) g⁻¹, hM, ?_, rfl, ?_⟩
  · exact fun hc => hgM (by simpa using M.inv_mem hc)
  · refine fun hbot => hx1 ?_
    have hxmem : x ∈ mixedFitting M ⊓ conjSubgroup (mixedFitting M) g⁻¹ := by
      refine ⟨hallCoreIn_le_mixedFitting M hxH, ?_⟩
      refine mem_conjSubgroup.2 ⟨y, hallCoreIn_le_mixedFitting M hyH, ?_⟩
      simpa [MulAut.conj_apply] using hxy
    rw [hbot, Subgroup.mem_bot] at hxmem
    exact hxmem

theorem exponent_dvd_sub_one_of_characteristic_of_natCard_eq
    {H Z U₀ : Subgroup G} (hZH : Z ≤ H) (hchar : (Z.subgroupOf H).Characteristic)
    (hU₀N : U₀ ≤ normalizer (H : Set G))
    (hfree : ∀ x ∈ U₀, x ≠ 1 → H ⊓ centralizer {x} = ⊥) {q : ℕ} (hZcard : Nat.card ↥Z = q) :
    Monoid.exponent ↥U₀ ∣ q - 1 := by
  have hU₀Z : U₀ ≤ normalizer (Z : Set G) := by
    have h := le_normalizer_map_subtype_of_characteristic (Z.subgroupOf H) hU₀N
    rwa [Subgroup.map_subgroupOf_eq_of_le hZH] at h
  have hdvd : Nat.card ↥U₀ ∣ Nat.card ↥Z - 1 :=
    natCard_dvd_sub_one_of_forall_inf_centralizer_eq_bot hZH hU₀Z hfree
  rw [← hZcard]
  exact Group.exponent_dvd_nat_card.trans hdvd

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson CFSG.FeitThompson.LocalTypeIAlternative
  Subgroup _root_.CFSG.FeitThompson

universe u

theorem FBG_local_type_I_alternative
    (h₁ : Statements.FBG_abelian_fitting_overlap_rank_two.{u})
    (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₅ : Statements.FBG_nonabelian_fitting_overlap_central_lines.{u})
    (h₆ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₇ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₈ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_local_type_I_alternative.{u} := by
  intro G _ _ hG M K U hsetup hK
  obtain ⟨⟨hHbot, -, -, -, -, -, -⟩, -⟩ := h₃ G hG M K U hsetup
  by_cases hTI : IsTIWithNormalizer (sharp (hallCoreIn M)) M
  · exact Or.inl hTI
  have hg : ∃ g : G, g ∉ M ∧
      ¬ Disjoint (sharp (hallCoreIn M)) (MulAut.conj g '' sharp (hallCoreIn M)) := by
    by_contra hc
    refine hTI ⟨sharp_nonempty_iff.2 hHbot.ne', one_notMem_sharp _,
      normalizer_sharp_hallCoreIn_eq hG hsetup.isCoatom hHbot.ne', fun g hgM => ?_⟩
    by_contra hdis
    exact hc ⟨g, hgM, hdis⟩
  obtain ⟨g, hgM, hd⟩ := hg
  obtain ⟨X, hX⟩ := exists_isFittingOverlapSetup_of_not_disjoint hsetup.isCoatom hgM hd
  by_cases habel : IsMulCommutative ↥(hallCoreIn M)
  ·
    exact Or.inr (Or.inl ⟨habel, (h₁ G hG M X g⁻¹ hX habel).1⟩)
  obtain ⟨hXprime, hcyc, hZ⟩ := h₅ G hG M X g⁻¹ hX habel
  have hU : U ≠ ⊥ := ne_bot_of_isLocalKappaSetup_of_eq_bot h₃ hG hsetup hK
  obtain ⟨-, U₁, U₀, -, hU₀U, -, -, -, hexp, hfree⟩ := h₂ G hG M K U hsetup hU
  obtain ⟨Y, hY⟩ := exists_isSylowProduct (mixedFitting M) {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M}
  obtain ⟨-, hHS, hXS, -⟩ :=
    FBG_nonti_fitting_nilpotent_core_and_beta_exclusion h₄ h₆ h₇ h₈ G hG M X g⁻¹ hX Y hY
  have hXH : X ≤ hallCoreIn M := hHS ▸ hXS
  have hU₀N : U₀ ≤ normalizer ((hallCoreIn M : Subgroup G) : Set G) :=
    (hU₀U.trans hsetup.le_M_U).trans (le_normalizer_hallCoreIn M)
  refine Or.inr (Or.inr ⟨fun r hr => ?_, Nat.card ↥X, ?_, hcyc⟩)
  · obtain ⟨Z₀, hZ₀set, hZ₀char, hZ₀card⟩ := hZ r hr
    have hZ₀H : Z₀ ≤ hallCoreIn M := by
      intro z hz
      have hmem : z ∈ pTorsionSet r
          (centreIn (_root_.CFSG.FeitThompson.pCoreIn r (hallCoreIn M))) := by
        rw [← hZ₀set]; exact hz
      exact _root_.CFSG.FeitThompson.pCoreIn_le r (hallCoreIn M)
        (centreIn_le _ (pTorsionSet_subset hmem))
    rw [← hexp]
    exact exponent_dvd_sub_one_of_characteristic_of_natCard_eq hZ₀H hZ₀char hU₀N hfree hZ₀card
  · exact Nat.mem_primeFactors.2 ⟨hXprime, Subgroup.card_dvd_of_le hXH, Nat.card_pos.ne'⟩

end

end CFSG.FeitThompson.Proofs

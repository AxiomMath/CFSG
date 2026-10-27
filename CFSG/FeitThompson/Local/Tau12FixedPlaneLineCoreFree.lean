module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TauOneTwoDoubleFixedReflection
import CFSG.FeitThompson.Local.NonregularPlaneLineUniqueCentralizer
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.ReflectedPlaneNonsigmaNormalizerOvergroup
import CFSG.FeitThompson.Local.UniqueMaximalOvergroupCentralizerTauOneThree
import CFSG.FeitThompson.Local.TypeINonfrobeniusWitness
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

theorem FNI_tau12_fixed_plane_line_core_free
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau12_fixed_plane_line_core_free.{u} := by
  intro G _ _ hG p q M E P A hE hp hPE hPcard hq hAE hAplane hCA
  by_contra hCS
  have : IsSimpleGroup G := hG.isSimpleGroup
  let _ : Fintype G := Fintype.ofFinite G
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG9 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hqprime, hqσ, -⟩ := mem_tauTwoPrimes_iff.1 hq
  obtain ⟨hpprime, -, -, -, -⟩ := mem_tau1Primes_iff.1 hp
  have hOSP : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane q M A :=
    ⟨hE.isCoatom, hqprime, hqσ, hAE.trans hE.le, hAplane⟩
  obtain ⟨hYcard, hYunique, hTdata⟩ :=
    FNI_tau12_double_fixed_reflection h₁ h₂ h₃ h₄ h₅ h₆ h₇ G hG p q M E P A hE hp hPE hPcard hq
      hAE hAplane hCA hCS
  have hAne : A ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot A).1 (by
    rw [hAplane.natCard']; exact Nat.one_lt_pow (by norm_num) hqprime.one_lt)
  have hNAne : normalizer (A : Set G) ≠ ⊤ :=
    (normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hqprime hAne
      (IsPGroup.of_card hAplane.natCard')).ne
  obtain ⟨T, hTcoatom, hNAT⟩ := exists_isCoatom_ge_of_ne_top hNAne
  obtain ⟨hTM, hET, hAST, hpT⟩ := hTdata T hTcoatom hNAT
  have hPT : P ≤ T := hPE.trans hET
  have hpσT : p ∉ sigmaPrimes T := by
    rcases hpT with h | h
    · exact notMem_sigmaPrimes_of_mem_tau1Primes h
    · exact (mem_tauTwoPrimes_iff.1 h).2.1
  have hsolvT : Group.IsSolvable ↥T := hG.isSolvable_of_ne_top T hTcoatom.1
  obtain ⟨hHallT, -, -⟩ := h₁ G hG2 T hTcoatom
  obtain ⟨F, hPF, hFT, hsdF⟩ :=
    exists_sigmaComplement_ge (L := T) (U := P) hHallT.2 hPT
      (isPiSubgroup_subgroupOf_of_natCard_prime hPT hpprime hPcard hpσT)
  have hsigF : _root_.CFSG.FeitThompson.IsSigmaComplement T F := ⟨hTcoatom, hsdF⟩
  have hYS : A ⊓ centralizer (P : Set G) ≤ sigmaCore T ⊓ centralizer (P : Set G) :=
    le_inf (inf_le_left.trans hAST) inf_le_right
  rcases hpT with hpT1 | hpT2
  ·
    have hFne : F ≠ ⊤ := fun h => hTcoatom.1 (top_le_iff.1 (h ▸ hFT))
    have hsolvF : Group.IsSolvable ↥F := hG.isSolvable_of_ne_top F hFne
    obtain ⟨F₁, hF₁F, hPF₁, hHall₁⟩ := exists_isHallPiSubgroup_tau1_ge (M := T) hPF
      (isPiSubgroup_subgroupOf_of_natCard_prime hPF hpprime hPcard hpT1)
    have hPne : P ≠ ⊥ := ne_bot_of_natCard_prime hpprime hPcard
    have huniqT := (h₈ G hG9 T hTcoatom F hFT hsdF F₁ hF₁F hHall₁ P hPF₁ hPne q hqprime
      (A ⊓ centralizer (P : Set G)) (by rw [Prep09.centIn_def]; exact hYS) hYcard).1
    exact hTM (huniqT.unique hYunique)
  ·
    obtain ⟨-, hranks, -⟩ := FNI_sigma_complement_prime_data h₁ G hG T F hsigF
    have hpF : p ∈ _root_.CFSG.FeitThompson.primeDivisorsOf ↥F :=
      ⟨hpprime, hPcard ▸ Subgroup.card_dvd_of_le hPF⟩
    have hrankF : elementaryAbelianPRank p ↥F = 2 := by
      rw [(hranks p hpF).1, (mem_tauTwoPrimes_iff.1 hpT2).2.2]
    obtain ⟨B, hBF, hBplane⟩ := exists_isPPlane_le hpprime hrankF
    have hOSPT : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p T B :=
      ⟨hTcoatom, hpprime, hpσT, hBF.trans hFT,
        isElementaryAbelianPlane_of_isPPlane hpprime hBplane⟩
    have hCPT : centralizer (P : Set G) ≤ T :=
      (FNI_nonregular_plane_line_unique_centralizer h₃ h₄ G hG p T B F P hOSPT hsigF hBF hPF
        hPcard (fun hbot => hCA (le_bot_iff.1 (hbot ▸ hYS)))).1.le
    have hAT : A ≤ T := le_trans le_normalizer hNAT
    have hdisj : sigmaCore M ⊓ T = ⊥ := h₄ G hG q M A T hOSP hTcoatom hTM hAT
    refine hCS (le_bot_iff.1 ?_)
    rw [← hdisj]
    exact le_inf inf_le_left (inf_le_right.trans hCPT)

end

end CFSG.FeitThompson.Proofs

module

public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SignalizerCosetsDisjoint
import CFSG.FeitThompson.Local.PacketConjugationDescription
import CFSG.FeitThompson.Local.SigmaOvergroupConjugacy
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep08

universe u

variable {G : Type*} [Group G]

theorem conjSub_eq_conjSubgroup (g : G) (Y : Subgroup G) :
    Prep09.conjSub g Y = conjSubgroup Y g := rfl

theorem isCoatom_conjSubgroup {M : Subgroup G} (hM : IsCoatom M) (g : G) :
    IsCoatom (conjSubgroup M g) := isCoatom_conj_smul hM g⁻¹

theorem exists_isCoatom_sigmaPrimes_eq_of_mem_conjSet_sigmaCore_sdiff [Finite G] {M : Subgroup G}
    (hM : IsCoatom M) {x : G} (hx : x ∈ ⋃ g : G, conjSet ((sigmaCore M : Set G) \ {1}) g) :
    ∃ N : Subgroup G, IsCoatom N ∧ sigmaPrimes N = sigmaPrimes M ∧ x ∈ sigmaCore N ∧ x ≠ 1 := by
  obtain ⟨g, hxg⟩ := Set.mem_iUnion.1 hx
  rw [conjSet_sdiff_one] at hxg
  refine ⟨conjSubgroup M g, isCoatom_conjSubgroup hM g, sigmaPrimes_conj_smul M g⁻¹, ?_, hxg.2⟩
  rw [← SetLike.mem_coe, coe_sigmaCore_conjSubgroup]
  exact hxg.1

theorem FTS_nonconjugate_packets_disjoint
    (h₁ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_nonconjugate_packets_disjoint.{u} := by
  intro G _ _ hG M T hM hT hnc
  have hG9 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hsep : sigmaPrimes M ∩ sigmaPrimes T = ∅ :=
    h₂ G hG9 M T hM hT fun g => by rw [conjSub_eq_conjSubgroup]; exact hnc g
  have hcd := FTS_signalizer_cosets_disjoint h₁ h₂ G hG9
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro z ⟨hzM, hzT⟩
  rw [sigmaPacketSupport_eq_biUnion] at hzM hzT
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 hzM
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 hzT
  obtain ⟨N, hN, hNM, hxN, hx1⟩ :=
    exists_isCoatom_sigmaPrimes_eq_of_mem_conjSet_sigmaCore_sdiff hM hx
  obtain ⟨P, hP, hPT, hyP, hy1⟩ :=
    exists_isCoatom_sigmaPrimes_eq_of_mem_conjSet_sigmaCore_sdiff hT hy
  have hxy : x ≠ y := by
    rintro rfl
    obtain ⟨q, hq⟩ : (orderOf x).primeFactors.Nonempty := by
      rw [Nat.nonempty_primeFactors]
      have h0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
      have h1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
      omega
    have hmem : q ∈ sigmaPrimes M ∩ sigmaPrimes T :=
      ⟨hNM ▸ primeFactors_orderOf_subset_sigmaPrimes hxN q hq,
        hPT ▸ primeFactors_orderOf_subset_sigmaPrimes hyP q hq⟩
    rw [hsep] at hmem
    exact hmem
  have hdisj := hcd x (mem_sigmaSupport.2 ⟨N, hN, hxN, hx1⟩) y
    (mem_sigmaSupport.2 ⟨P, hP, hyP, hy1⟩) hxy
  rw [Set.eq_empty_iff_forall_notMem] at hdisj
  exact hdisj z ⟨by rwa [← sigmaCoreSignalizer_eq_sigmaSignalizer],
    by rwa [← sigmaCoreSignalizer_eq_sigmaSignalizer]⟩

end

end CFSG.FeitThompson.Proofs

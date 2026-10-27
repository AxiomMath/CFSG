module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.AllTypeICoreCentralizerControl
import CFSG.FeitThompson.Local.DisjointDSetsNonconjugateMaximals
import CFSG.FeitThompson.Local.PacketConjugationDescription
import CFSG.FeitThompson.Local.SignalizerPacketCardinality
import CFSG.FeitThompson.OddOrder.PSubgroupInSigmaCoreOfMaximal
import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsRoots
import CFSG.FeitThompson.Local.SigmaPrimeCoverage
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson Prep06
open CFSG.FeitThompson.Prep08

universe u

variable {G : Type u} [Group G]

theorem map_conj_eq_smul (M : Subgroup G) (g : G) :
    Subgroup.map (MulAut.conj g : G ≃* G) M = MulAut.conj g • M := by
  rw [Subgroup.pointwise_smul_def]; rfl

theorem map_conj_eq_conjSubgroup (M : Subgroup G) (g : G) :
    Subgroup.map (MulAut.conj g : G ≃* G) M = Prep08.conjSubgroup M g⁻¹ := by
  rw [map_conj_eq_smul, Prep08.conjSubgroup, inv_inv]

theorem map_conj_one (M : Subgroup G) :
    Subgroup.map (MulAut.conj (1 : G) : G ≃* G) M = M := by
  rw [map_conj_eq_conjSubgroup, inv_one, Prep08.conjSubgroup_one]

theorem sigSignalizer_eq_sigmaCoreSignalizer [Finite G] (x : G) :
    sigSignalizer x = sigmaCoreSignalizer G x := (rfl)

theorem sigDelta_eq_sigmaPacketSupport [Finite G] (M : Subgroup G) :
    sigDelta M = sigmaPacketSupport G M := by
  rw [sigDelta_eq, sigmaPacketSupport]
  ext z
  simp only [Set.mem_iUnion, Prep08.conjSet, sigmaPacket, Set.mem_image, Set.mem_smul_set, smul_eq_mul,
    exists_prop, sigSignalizer_eq_sigmaCoreSignalizer]
  tauto

theorem ne_conjSubgroup_of_mem_transversal {𝓣 : Set (Subgroup G)}
    (htrans : ∀ M ∈ Prep06.maximalSubgroups G, ∃! T, T ∈ 𝓣 ∧
      ∃ g : G, Subgroup.map (MulAut.conj g : G ≃* G) M = T)
    {M T : Subgroup G} (hM𝓣 : M ∈ 𝓣) (hT𝓣 : T ∈ 𝓣) (hMco : IsCoatom M) (hMT : M ≠ T) :
    ∀ g : G, T ≠ Prep08.conjSubgroup M g := by
  intro g hg
  obtain ⟨N, -, huniq⟩ := htrans M hMco
  have h1 : M = N := huniq M ⟨hM𝓣, 1, map_conj_one M⟩
  have h2 : T = N := huniq T ⟨hT𝓣, g⁻¹, by rw [map_conj_eq_conjSubgroup, inv_inv, hg]⟩
  exact hMT (h1.trans h2.symm)

theorem ne_conjSub_of_mem_transversal {𝓣 : Set (Subgroup G)}
    (htrans : ∀ M ∈ Prep06.maximalSubgroups G, ∃! T, T ∈ 𝓣 ∧
      ∃ g : G, Subgroup.map (MulAut.conj g : G ≃* G) M = T)
    {M T : Subgroup G} (hM𝓣 : M ∈ 𝓣) (hT𝓣 : T ∈ 𝓣) (hMco : IsCoatom M) (hMT : M ≠ T) :
    ∀ g : G, T ≠ CFSG.FeitThompson.Prep09.conjSub g M := fun g =>
  ne_conjSubgroup_of_mem_transversal htrans hM𝓣 hT𝓣 hMco hMT g

theorem exists_mem_transversal_conj [Finite G] {𝓣 : Set (Subgroup G)}
    (htrans : ∀ M ∈ Prep06.maximalSubgroups G, ∃! T, T ∈ 𝓣 ∧
      ∃ g : G, Subgroup.map (MulAut.conj g : G ≃* G) M = T)
    {L : Subgroup G} (hL : IsCoatom L) :
    ∃ T ∈ 𝓣, sigmaPacketSupport G T = sigmaPacketSupport G L ∧
      Nat.card ↥(sigmaCore T) = Nat.card ↥(sigmaCore L) := by
  obtain ⟨T, ⟨hT𝓣, g, hgT⟩, -⟩ := htrans L hL
  rw [map_conj_eq_conjSubgroup] at hgT
  subst hgT
  exact ⟨_, hT𝓣, sigmaPacketSupport_conjSubgroup L g⁻¹, natCard_sigmaCore_conjSubgroup L g⁻¹⟩

theorem dvd_natCard_sigmaCore_of_mem_sigmaPrimes [Finite G] {M : Subgroup G}
    (hHall : IsHallPiSubgroup (sigmaPrimes M) (sigmaCore M)) {p : ℕ} (hp : p.Prime)
    (hpσ : p ∈ sigmaPrimes M) (hpG : p ∣ Nat.card G) : p ∣ Nat.card ↥(sigmaCore M) := by
  have hidx : ¬ p ∣ (sigmaCore M).index := fun h =>
    hHall.notMem_of_mem_primeFactors_index p
      (Nat.mem_primeFactors.2 ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩) hpσ
  have hmul := (sigmaCore M).card_mul_index
  rcases (Nat.Prime.dvd_mul hp).1 (hmul ▸ hpG) with h | h
  · exact h
  · exact absurd h hidx

theorem mem_sigmaPrimes_of_dvd_natCard_sigmaCore [Finite G] {M : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card ↥(sigmaCore M)) : p ∈ sigmaPrimes M :=
  isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
    (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩)

theorem mem_hallCoreIn_of_pow_mem
    (h₁ : _root_.CFSG.FeitThompson.Statements.FPF_type_I_frobenius.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    [Finite G] (hG : IsMinimalOddSimple G)
    (hallI : ∀ M ∈ Prep06.maximalSubgroups G, IsTypeI M)
    {L : Subgroup G} (hL : IsCoatom L) {x : G} {n : ℕ}
    (hx : x ^ n ∈ Prep06.hallCoreIn L) (hx1 : x ^ n ≠ 1) : x ∈ Prep06.hallCoreIn L := by
  have hfin : Fintype G := Fintype.ofFinite G
  have hG05 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  obtain ⟨E, -, -, hsemi, hfree⟩ := h₁ G hG05 L hL (hallI L hL)
  have hmul : ((Prep06.hallCoreIn L : Subgroup G) : Set G) * (E : Set G) = (L : Set G) :=
    hsemi.coe_eq_mul.symm
  have hdisj : Prep06.hallCoreIn L ⊓ E = ⊥ := hsemi.inf_eq_bot
  have hnorm : ((Prep06.hallCoreIn L).subgroupOf L).Normal := hsemi.normal_subgroupOf
  have := hnorm
  have hCH : ∀ e ∈ E, e ≠ 1 → Prep06.hallCoreIn L ⊓ centralizer ({e} : Set G) = ⊥ := by
    intro e he he1
    have h := hfree e he he1
    rwa [CFSG.FeitThompson.Prep05.centralizerIn,
      centralizer_coe_zpowers] at h
  have hCG : ∀ h ∈ Prep06.hallCoreIn L, h ≠ 1 → centralizer ({h} : Set G) ≤ L := by
    intro h hh hh1
    exact ((FTS_all_type_I_core_centralizer_control h₁ h₂ G hG hallI L hL).1 h ⟨hh, by
      simpa using hh1⟩).1
  exact mem_of_pow_mem_of_ne_one hmul hdisj hCH hCG hx hx1

theorem exists_isCoatom_mem_hallCoreIn
    (h₁ : _root_.CFSG.FeitThompson.Statements.FPF_type_I_frobenius.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    [Finite G] (hG : IsMinimalOddSimple G)
    (hallI : ∀ M ∈ Prep06.maximalSubgroups G, IsTypeI M)
    {x : G} (hx1 : x ≠ 1) : ∃ L : Subgroup G, IsCoatom L ∧ x ∈ Prep06.hallCoreIn L := by
  have hG05 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hG09 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hm0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hm1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
  have hou : orderOf (x ^ (orderOf x / p)) = p := orderOf_pow_orderOf_div hm0 hpm
  have hune : (zpowers (x ^ (orderOf x / p))) ≠ ⊥ := by
    rw [ne_eq, Subgroup.eq_bot_iff_card, Nat.card_zpowers, hou]
    exact hp.ne_one
  have hpg : IsPGroup p ↥(zpowers (x ^ (orderOf x / p))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hou, pow_one])
  obtain ⟨L, hL, hle⟩ := FPF_p_subgroup_sigma_core_placement G hG05 p hp _ hune hpg
  refine ⟨L, hL, ?_⟩
  have hSH : Prep06.hallCoreIn L = sigmaCore L := (h₂ G hG09 L hL (hallI L hL)).2.1
  have humem : x ^ (orderOf x / p) ∈ Prep06.hallCoreIn L := by
    rw [hSH]; exact hle (mem_zpowers _)
  have hune1 : x ^ (orderOf x / p) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hou; exact hp.ne_one hou.symm
  exact mem_hallCoreIn_of_pow_mem h₁ h₃ hG hallI hL humem hune1

theorem FTS_all_type_I_packet_cover
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FPF_type_I_frobenius.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_all_type_I_packet_cover.{u} := by
  intro G _ _ hG hallI 𝓣 h𝓣 htrans
  have hG02 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hG08 : IsMinimalSimpleOddOrder G := ⟨hG.simple, hG.nonabelian, hG.odd, hG.solvable⟩
  have hG09 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hsimple := hG.simple
  have hcoatom : ∀ M ∈ 𝓣, IsCoatom M := fun M hM => h𝓣 hM
  have hpc := fun (M : Subgroup G) (hM : IsCoatom M) => FTS_packet_cardinality h₁ h₃ h₄ G hG08 M hM
  have hcd := fun (M : Subgroup G) (hM : IsCoatom M) =>
    FTS_packet_conjugation_description h₃ h₄ G hG08 M hM _ rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro M hM
    rw [sigDelta_eq_sigmaPacketSupport]
    exact (hpc M (hcoatom M hM)).2
  ·
    intro M hM T hT hMT
    rw [sigDelta_eq_sigmaPacketSupport, sigDelta_eq_sigmaPacketSupport]
    exact FTS_nonconjugate_packets_disjoint h₃ h₄ G hG08 M T (hcoatom M hM) (hcoatom T hT)
      (ne_conjSubgroup_of_mem_transversal htrans hM hT (hcoatom M hM) hMT)
  ·
    ext z
    simp only [Set.mem_iUnion, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and,
      exists_prop]
    constructor
    ·
      rintro ⟨M, hM, hz⟩ rfl
      rw [sigDelta_eq_sigmaPacketSupport] at hz
      exact (hcd M (hcoatom M hM)).2.2.2.2 hz
    ·
      intro hz1
      obtain ⟨L, hL, hzL⟩ := exists_isCoatom_mem_hallCoreIn h₂ h₅ h₆ hG hallI hz1
      have hdel : sigDelta L = ⋃ g : G, (fun x => g⁻¹ * x * g) '' ((Prep06.hallCoreIn L : Set G) \ {1}) :=
        (FTS_all_type_I_core_centralizer_control h₂ h₆ G hG hallI L hL).2
      have hzdel : z ∈ sigDelta L := by
        rw [hdel]
        exact Set.mem_iUnion.2 ⟨1, ⟨z, ⟨hzL, hz1⟩, by group⟩⟩
      obtain ⟨T, hT𝓣, hTL, -⟩ := exists_mem_transversal_conj htrans hL
      refine ⟨T, hT𝓣, ?_⟩
      rw [sigDelta_eq_sigmaPacketSupport, hTL, ← sigDelta_eq_sigmaPacketSupport]
      exact hzdel
  ·
    intro M hM T hT hMT
    refine Nat.coprime_of_dvd fun k hk hkM hkT => ?_
    have hmem : k ∈ sigmaPrimes M ∩ sigmaPrimes T :=
      ⟨mem_sigmaPrimes_of_dvd_natCard_sigmaCore hk hkM,
        mem_sigmaPrimes_of_dvd_natCard_sigmaCore hk hkT⟩
    rw [h₄ G hG09 M T (hcoatom M hM) (hcoatom T hT)
      (ne_conjSub_of_mem_transversal htrans hM hT (hcoatom M hM) hMT)] at hmem
    exact hmem
  ·
    intro M hM
    rw [sigDelta_eq_sigmaPacketSupport, Nat.card_coe_set_eq]
    exact (hpc M (hcoatom M hM)).1
  ·
    intro p hp
    obtain ⟨hpp, hpG, -⟩ := Nat.mem_primeFactors.1 hp
    obtain ⟨L, hL, hpL⟩ := exists_isCoatom_mem_sigmaPrimes hG.nonabelian hpp hpG
    have hHall : IsHallPiSubgroup (sigmaPrimes L) (sigmaCore L) := (h₁ G hG02 L hL).2.1
    obtain ⟨T, hT𝓣, -, hTcard⟩ := exists_mem_transversal_conj htrans hL
    refine ⟨T, hT𝓣, ?_⟩
    rw [hTcard]
    exact dvd_natCard_sigmaCore_of_mem_sigmaPrimes hHall hpp hpL hpG

end

end CFSG.FeitThompson.Proofs

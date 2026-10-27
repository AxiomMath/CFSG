module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Representations.TypeISupportingGroupConfiguration
import CFSG.FeitThompson.Representations.TypeISupportingCharacterConfig
import CFSG.FeitThompson.Local.DisjointDSetsNonconjugateMaximals
import CFSG.FeitThompson.Representations.TypeIINonfrobeniusCrossedColumnData
import CFSG.FeitThompson.Local.CommonPrimeFixedCoreFittingEnvelope
import CFSG.FeitThompson.OddOrder.FullExponentFreeRegularElement
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
import CFSG.FeitThompson.OddOrder.RegularPrimeActionLargeAbelianization
import CFSG.FeitThompson.OddOrder.LocalTypesConjugationInvariant
import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Foundations.LocalNormBoundsSmallIndex
import CFSG.FeitThompson.Representations.WitnessCongruenceLocalInverseNormBound
import CFSG.FeitThompson.Representations.TwoDisjointDadeSupportsStrictNorm
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.ProjectedRestrictionGenChars
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
import CFSG.FeitThompson.Foundations.CentralSeriesDerivedLength
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
import CFSG.FeitThompson.Representations.CyclicTIIsometryExistence
import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
import CFSG.FeitThompson.Representations.TypeVTwoFamilyCoherenceJoining

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep05
open scoped ComplexOrder

universe u

variable {G : Type u} [Group G] [Finite G]

theorem restrict_zpowers_mem_span_Irr {N : Subgroup G} {x : G} (hle : (zpowers x : Subgroup G) ≤ N)
    {ζ : ↥N → ℂ} (hζ : ζ ∈ Submodule.span ℤ (Irr ↥N)) :
    (fun t : ↥(zpowers x) => ζ ⟨(t : G), hle t.2⟩) ∈ Submodule.span ℤ (Irr ↥(zpowers x)) :=
  mem_span_Irr_of_mem_virtualChars (comp_mem_virtualChars (Subgroup.inclusion hle) hζ)

theorem sq_norm_lower_bound
    {M : Subgroup G} {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 1 ≤ e) (hep : 2 * e ≤ p + 1)
    {Ψ : G → ℂ} (hΨ : Ψ ∈ Submodule.span ℤ (Irr G))
    {c : ℤ} (hc : ∀ k ∈ (hallCoreOf M : Set G) \
      ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G), Ψ k = (c : ℂ))
    (hKK' : ((hallCoreOf M : Set G) \
      ((⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) : Set G)).Nonempty)
    (hval : ∀ k ∈ hallCoreOf M, k ≠ 1 → rhoHallCore M Ψ k = Ψ k)
    {N : Subgroup G} {ζ : ↥N → ℂ} (hζ1 : ζ 1 = (e : ℂ))
    (hζspan : ζ ∈ Submodule.span ℤ (Irr ↥N))
    {x g : G} (hxord : orderOf x = p) (hxN : x ∈ N)
    (hgK : g ∈ hallCoreOf M) (hgB : g ∉ (⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G))
    (hxg : Commute x g)
    (hmatch : ∀ a : ℕ, 1 ≤ a → a ≤ p - 1 → ∀ k ∈ hallCoreOf M, ∀ hxa : x ^ a ∈ N,
      Ψ (x ^ a * k) = ζ ⟨x ^ a, hxa⟩) :
    ((Nat.card ↥(hallCoreOf M) : ℝ) - Nat.card ↥(⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G))
        / Nat.card ↥M * ((e : ℝ) - 1) ^ 2
      ≤ (cfIP (fun m : ↥M => rhoHallCore M Ψ (m : G))
          (fun m : ↥M => rhoHallCore M Ψ (m : G))).re := by
  classical
  let _ : Fintype ↥M := Fintype.ofFinite _
  rw [cfIP_eq_cfInner]
  have hle : (zpowers x : Subgroup G) ≤ N := zpowers_le.2 hxN
  have hBK : (⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) < hallCoreOf M := by
    refine lt_of_le_of_ne (Subgroup.commutator_le_self _) ?_
    intro hcon
    obtain ⟨k, hk, hk'⟩ := hKK'
    exact hk' (by rw [hcon]; exact hk)
  refine card_sub_card_div_card_mul_sq_le_cfInner_self_re (B := ⁅hallCoreOf M, hallCoreOf M⁆)
    (K := hallCoreOf M) (M := M) hBK (hallCoreOf_le M) hΨ
    (c := (c : ℂ)) (fun k hk hkB => hc k ⟨hk, hkB⟩) ?_ hp
    (e := (e : ℤ)) (by exact_mod_cast he) (by exact_mod_cast hep) hxord hgK hgB hxg
    (Θ := fun t : ↥(zpowers x) => ζ ⟨(t : G), hle t.2⟩)
    (restrict_zpowers_mem_span_Irr hle hζspan) ?_ ?_
  · intro m hmK hmB
    exact hval (m : G) hmK (fun hcon => hmB (by rw [hcon]; exact one_mem _))
  · simp only [OneMemClass.coe_one]
    rw [show (⟨(1 : G), hle (Subgroup.one_mem _)⟩ : ↥N) = 1 from rfl]
    exact_mod_cast hζ1
  · intro a ha1 ha2
    have hxa : x ^ a ∈ N := pow_mem hxN a
    rw [hmatch a ha1 ha2 g hgK hxa]
    congr 1

omit [Finite G] in
theorem dadeSupport_congr {H H' : G → Subgroup G} {a : G} (h : H a = H' a) :
    dadeSupport H a = dadeSupport H' a := by
  ext z
  simp only [mem_dadeSupport_iff]
  constructor
  · rintro ⟨y, hy, hc⟩
    exact ⟨y, by rw [mem_dadeCoset_iff, ← h]; exact mem_dadeCoset_iff.1 hy, hc⟩
  · rintro ⟨y, hy, hc⟩
    exact ⟨y, by rw [mem_dadeCoset_iff, h]; exact mem_dadeCoset_iff.1 hy, hc⟩

omit [Finite G] in
theorem totalDadeSupport_congr {A : Set G} {H H' : G → Subgroup G} (h : ∀ a ∈ A, H a = H' a) :
    totalDadeSupport A H = totalDadeSupport A H' := by
  ext z
  simp only [mem_totalDadeSupport_iff]
  constructor
  · rintro ⟨a, ha, hz⟩; exact ⟨a, ha, (dadeSupport_congr (h a ha)) ▸ hz⟩
  · rintro ⟨a, ha, hz⟩; exact ⟨a, ha, (dadeSupport_congr (h a ha)).symm ▸ hz⟩

theorem sigSignalizer_eq_sigmaCoreSignalizer_of_mem (M : Subgroup G) {a : G}
    (ha : a ∈ (sigmaCore M : Set G) \ {1}) :
    sigSignalizer M a = Prep08.sigmaCoreSignalizer G a := by
  rw [sigSignalizer, signalizerOn_of_mem ha]
  rfl

theorem totalDadeSupport_sigmaCore_eq (M : Subgroup G) :
    totalDadeSupport ((sigmaCore M : Set G) \ {1}) (sigSignalizer M)
      = Prep08.sigmaPacketSupport G M := by
  rw [Prep08.sigmaPacketSupport_eq_totalDadeSupport]
  exact totalDadeSupport_congr fun a ha => sigSignalizer_eq_sigmaCoreSignalizer_of_mem M ha

omit [Finite G] in
theorem natCard_hallCoreOf_conjSubgroup (M : Subgroup G) (g : G) :
    Nat.card ↥(hallCoreOf (Prep08.conjSubgroup M g)) = Nat.card ↥(hallCoreOf M) := by
  rw [natCard_hallCoreOf, natCard_hallCoreOf, Prep08.conjSubgroup, conj_smul_eq_map_conj]
  exact natCard_hallCore_map (MulAut.conj g⁻¹) M

omit [Finite G] in
theorem ne_conjSubgroup_of_dvd_of_not_dvd {M N : Subgroup G} {p : ℕ}
    (hpJ : p ∣ Nat.card ↥(hallCoreOf N)) (hpK : ¬ p ∣ Nat.card ↥(hallCoreOf M)) (g : G) :
    N ≠ Prep08.conjSubgroup M g := by
  intro h
  rw [h, natCard_hallCoreOf_conjSubgroup] at hpJ
  exact hpK hpJ

theorem disjoint_totalDadeSupport_hallCoreOf
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M N : Subgroup G} (hM : IsCoatom M) (hN : IsCoatom N)
    (hIM : IsTypeI M) (hIN : IsTypeI N) {p : ℕ}
    (hpJ : p ∣ Nat.card ↥(hallCoreOf N)) (hpK : ¬ p ∣ Nat.card ↥(hallCoreOf M)) :
    Disjoint (totalDadeSupport ((hallCoreOf M : Set G) \ {1}) (sigSignalizer M))
      (totalDadeSupport ((hallCoreOf N : Set G) \ {1}) (sigSignalizer N)) := by
  have hG08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG09 : Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hSM, -⟩ := h₇ G hG09 M hM hIM
  obtain ⟨hSN, -⟩ := h₇ G hG09 N hN hIN
  rw [← hallCoreOf_eq_hallCoreIn] at hSM hSN
  have hdisj := FTS_nonconjugate_packets_disjoint h₂ h₄ G hG08 M N hM hN
    (ne_conjSubgroup_of_dvd_of_not_dvd hpJ hpK)
  rw [Set.disjoint_iff_inter_eq_empty, ← hSM, ← hSN, totalDadeSupport_sigmaCore_eq,
    totalDadeSupport_sigmaCore_eq]
  exact hdisj

theorem two_norms_lt_one
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u})
    (hG : IsMinimalSimpleOdd G) {M N : Subgroup G} (hM : IsCoatom M) (hN : IsCoatom N)
    (hIM : IsTypeI M) (hIN : IsTypeI N)
    (hdisj : Disjoint (totalDadeSupport ((hallCoreOf M : Set G) \ {1}) (sigSignalizer M))
      (totalDadeSupport ((hallCoreOf N : Set G) \ {1}) (sigSignalizer N)))
    {Ψ : G → ℂ} (hsi : IsSignedIrr Ψ) :
    (cfIP (fun m : ↥M => rhoHallCore M Ψ (m : G))
          (fun m : ↥M => rhoHallCore M Ψ (m : G))).re
        + (cfIP (fun n : ↥N => rhoHallCore N Ψ (n : G))
          (fun n : ↥N => rhoHallCore N Ψ (n : G))).re < 1 := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype ↥M := Fintype.ofFinite _
  let _ : Fintype ↥N := Fintype.ofFinite _
  rw [cfIP_eq_cfInner, cfIP_eq_cfInner]
  have hmem : Ψ ∈ signedIrr G := (isSignedIrr_iff_mem_signedIrr Ψ).1 hsi
  have hΨspan : Ψ ∈ Submodule.span ℤ (Irr G) := mem_span_Irr_of_mem_signedIrr hmem
  have hnorm1 : cfInner Ψ Ψ = 1 :=
    (mem_signedIrr_iff_mem_span_Irr_and_cfInner_self_eq_one.1 hmem).2
  have hΨ1 : Ψ 1 ≠ 0 := apply_one_ne_zero_of_mem_signedIrr hmem
  have hΨcf : Ψ ∈ classFun G := virtualChars_le_classFun (mem_virtualChars_of_mem_span_Irr hΨspan)
  have key := cfInner_self_dadeAverage_add_lt_one_of_disjoint
    (isDadeData_sdiff_hallCoreOf h₇ hG hM hIM) (isDadeData_sdiff_hallCoreOf h₇ hG hN hIN) hdisj
    (χ := (⟨Ψ, hΨcf⟩ : classFun G)) hnorm1 hΨ1
  have hFM : (fun y : ↥M => dadeAverage ((hallCoreOf M : Set G) \ {1}) (sigSignalizer M) Ψ (y : G))
      = fun m : ↥M => rhoHallCore M Ψ (m : G) := rfl
  have hFN : (fun y : ↥N => dadeAverage ((hallCoreOf N : Set G) \ {1}) (sigSignalizer N) Ψ (y : G))
      = fun n : ↥N => rhoHallCore N Ψ (n : G) := rfl
  rw [show ((⟨Ψ, hΨcf⟩ : classFun G) : G → ℂ) = Ψ from rfl, hFM, hFN] at key
  set FM : ↥M → ℂ := fun m : ↥M => rhoHallCore M Ψ (m : G) with hFMdef
  set FN : ↥N → ℂ := fun n : ↥N => rhoHallCore N Ψ (n : G) with hFNdef
  have hreM : cfInner FM FM = (((cfInner FM FM).re : ℝ) : ℂ) := by
    rw [cfInner_self_re, cfInner_self_eq_ofReal]
  have hreN : cfInner FN FN = (((cfInner FN FN).re : ℝ) : ℂ) := by
    rw [cfInner_self_re, cfInner_self_eq_ofReal]
  rw [hreM, hreN] at key
  have h1 : (((cfInner FM FM).re + (cfInner FN FN).re : ℝ) : ℂ) < ((1 : ℝ) : ℂ) := by
    push_cast
    simpa using key
  exact Complex.real_lt_real.1 h1

theorem one_sub_div_le_re_cfIP {N : Subgroup G} {Ψ : G → ℂ} {h e : ℕ}
    (hb : 1 - (e : ℂ) / (h : ℂ) ≤
      cfIP (fun n : ↥N => rhoHallCore N Ψ (n : G)) (fun n : ↥N => rhoHallCore N Ψ (n : G))) :
    1 - (e : ℝ) / (h : ℝ)
      ≤ (cfIP (fun n : ↥N => rhoHallCore N Ψ (n : G))
          (fun n : ↥N => rhoHallCore N Ψ (n : G))).re := by
  classical
  let _ : Fintype ↥N := Fintype.ofFinite _
  rw [cfIP_eq_cfInner] at hb ⊢
  set FN : ↥N → ℂ := fun n : ↥N => rhoHallCore N Ψ (n : G) with hFNdef
  have hre : cfInner FN FN = (((cfInner FN FN).re : ℝ) : ℂ) := by
    rw [cfInner_self_re, cfInner_self_eq_ofReal]
  rw [hre] at hb
  have hlhs : (1 : ℂ) - (e : ℂ) / (h : ℂ) = ((1 - (e : ℝ) / (h : ℝ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hlhs] at hb
  exact Complex.real_le_real.1 hb

theorem add_one_le_relIndex_commutator_hallCoreOf
    (hG : IsMinimalSimpleOdd G) {M N : Subgroup G} (hM : IsCoatom M)
    (hKbot : hallCoreOf M ≠ ⊥)
    (hMnormK : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G))
    (hMsd : FreeCore.IsInternalSemidirectProduct M (hallCoreOf M) (M ⊓ N))
    {D₀ : Subgroup G} (hD₀ : D₀ ≤ M ⊓ N)
    (hexp : Monoid.exponent ↥D₀ = Monoid.exponent ↥(M ⊓ N))
    (hD₀free : IsFixedPointFreeOn (hallCoreOf M) D₀)
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card ↥(hallCoreOf M))
    (hpM : p ∣ Nat.card ↥M) :
    p + 1 ≤ (⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G).relIndex (hallCoreOf M) := by
  classical
  have _ : Fact p.Prime := ⟨hp⟩
  have hKM : hallCoreOf M ≤ M := hallCoreOf_le M
  have hKnormal : ((hallCoreOf M).subgroupOf M).Normal := normal_subgroupOf_hallCoreOf M
  have hcompM : ((hallCoreOf M).subgroupOf M).IsComplement' ((M ⊓ N).subgroupOf M) :=
    isComplement'_subgroupOf_of_isInternalSemidirectProduct hMsd
  have hD₀M : D₀ ≤ M := hD₀.trans inf_le_left
  have hDM : M ⊓ N ≤ M := inf_le_left
  have hexpM : Monoid.exponent ↥(D₀.subgroupOf M) = Monoid.exponent ↥((M ⊓ N).subgroupOf M) := by
    rw [Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hD₀M),
      Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDM)]
    exact hexp
  have hCD0M : ∀ d ∈ D₀.subgroupOf M, d ≠ 1 →
      (hallCoreOf M).subgroupOf M ⊓ centralizer ({d} : Set ↥M) = ⊥ := by
    intro d hd hd1
    refine (inf_centralizer_singleton_subgroupOf_eq_bot_iff hKM d).2 ?_
    have h := hD₀free (d : G) (Subgroup.mem_subgroupOf.1 hd) (fun h => hd1 (Subtype.ext h))
    rwa [centralizerIn_eq, centralizer_coe_zpowers] at h
  have hpKM : ¬ p ∣ Nat.card ↥((hallCoreOf M).subgroupOf M) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
  obtain ⟨S⟩ : Nonempty (Sylow p ↥M) := inferInstance
  have hScard : Nat.card ↥(S : Subgroup ↥M) = p ^ (Nat.card ↥M).factorization p :=
    S.card_eq_multiplicity
  have hSbot : (S : Subgroup ↥M) ≠ ⊥ := by
    intro hb
    have hcard1 : Nat.card ↥(S : Subgroup ↥M) = 1 := by rw [hb]; simp
    have hpow : p ^ (Nat.card ↥M).factorization p = 1 := hScard.symm.trans hcard1
    have hpos : 0 < (Nat.card ↥M).factorization p :=
      hp.factorization_pos_of_dvd Nat.card_pos.ne' hpM
    rcases Nat.pow_eq_one.1 hpow with h | h
    · exact hp.one_lt.ne' h
    · omega
  obtain ⟨a, haS, haord, hCKa⟩ := exists_mem_sylow_orderOf_eq_and_inf_centralizer_eq_bot
    (K := (hallCoreOf M).subgroupOf M) (D := (M ⊓ N).subgroupOf M) (D0 := D₀.subgroupOf M)
    hcompM hexpM hCD0M hp hpKM S hSbot
  have hCKaG : hallCoreOf M ⊓ centralizer ({(a : G)} : Set G) = ⊥ :=
    (inf_centralizer_singleton_subgroupOf_eq_bot_iff hKM a).1 hCKa
  have hbord : orderOf ((a : G)) = p := by rw [Subgroup.orderOf_coe]; exact haord
  have hzp : (zpowers ((a : G)) : Subgroup G) ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
    zpowers_le.2 (hMnormK a.2)
  have hKtop : hallCoreOf M ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hKM))
  have hKsolv : Group.IsSolvable ↥(hallCoreOf M) := hG.isSolvable_of_ne_top _ hKtop
  have hKnt : Nontrivial ↥(hallCoreOf M) := (Subgroup.nontrivial_iff_ne_bot _).2 hKbot
  have htop : Subgroup.zpowers
      (⟨(a : G), Subgroup.mem_zpowers ((a : G))⟩ : ↥(zpowers ((a : G)))) = ⊤ := by
    ext y
    simp only [Subgroup.mem_top, iff_true, Subgroup.mem_zpowers_iff]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 y.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hcardA : Nat.card ↥(zpowers ((a : G))) = p := by rw [Nat.card_zpowers, hbord]
  have hfree : MonoidHom.FixedPointFree
      (conjOnNormalized (hallCoreOf M) hzp
        (⟨(a : G), Subgroup.mem_zpowers ((a : G))⟩ : ↥(zpowers ((a : G))))) := by
    intro v hv
    have hcoe : (a : G) * (v : G) * ((a : G))⁻¹ = (v : G) := by
      have h := congrArg Subtype.val hv
      rwa [conjOnNormalized_apply_coe] at h
    have hcomm : (a : G) * (v : G) = (v : G) * (a : G) := by
      have h2 := congrArg (fun z : G => z * (a : G)) hcoe
      simpa using h2
    have hmem : (v : G) ∈ hallCoreOf M ⊓ centralizer ({(a : G)} : Set G) := by
      refine ⟨v.2, mem_centralizer_iff.2 ?_⟩
      intro m hm
      rw [Set.mem_singleton_iff] at hm
      subst hm
      exact hcomm
    rw [hCKaG, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hkey : p + 1 ≤ Nat.card (↥(hallCoreOf M) ⧸ commutator ↥(hallCoreOf M)) :=
    add_one_le_card_quotient_commutator hp hcardA htop hfree
  have hsub : (⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G).subgroupOf (hallCoreOf M)
      = commutator ↥(hallCoreOf M) := by
    rw [Subgroup.subgroupOf, ← Subgroup.map_subtype_commutator (hallCoreOf M),
      Subgroup.comap_map_eq_self_of_injective (hallCoreOf M).subtype_injective]
  rwa [Subgroup.relIndex, hsub, Subgroup.index_eq_card]

theorem FPF_type_i_supporting_case_contradiction
    (h₁ : _root_.CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_positive_support_forces_cyclic_frobenius.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_sigma_prime_separation.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_complement_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_core_kappa_identity.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u}) :
    _root_.CFSG.FeitThompson.Statements.FPF_type_i_supporting_case_contradiction.{u} := by
  intro G _ _ hG p hp hsmall M N hM hN hIM hIN hpK P hPcomm hPsyl hrank hPsig x hxP hxord
    hCK hnorm hcent
  classical
  obtain ⟨hKbot, hJbot, hKnil, hJnil, hMnormK, hNnormJ, -, -, hMsolv, hPJ, hMsd, hDJ,
    ⟨D₀, D₁, hD₀, hD₁, hexp, hD₀free, hD₁comm, hD₁cent⟩,
    ⟨E, hEN, hEbot, hEcyc, hEsd, hEfree, hE3, -, hep⟩, hp3, hph, hnotFrob⟩ :=
    FPF_type_i_supporting_group_configuration h₇ G hG p hp hsmall M N hM hN hIM hIN hpK
      P hPcomm hPsyl hrank hPsig x hxP hxord hCK hnorm hcent
  have hx1 : x ≠ 1 := by
    intro h; rw [h, orderOf_one] at hxord; exact hp.one_lt.ne' hxord.symm
  have hxJ : x ∈ hallCoreOf N := hPJ hxP
  have hxM : x ∈ M := hPsyl.1 hxP
  have hxK : x ∉ hallCoreOf M := fun hx => hpK (hxord ▸ Subgroup.orderOf_dvd_natCard _ hx)
  have hpJ : p ∣ Nat.card ↥(hallCoreOf N) := hxord ▸ Subgroup.orderOf_dvd_natCard _ hxJ
  have hpM : p ∣ Nat.card ↥M := hxord ▸ Subgroup.orderOf_dvd_natCard M hxM
  obtain ⟨ζ, hζS, hζIrr, hζ1, hζ, ν, hν, hall⟩ :=
    FPF_type_i_supporting_character_configuration h₁ h₂ h₃ h₄ h₅ h₆ h₇ G hG M N hM hN hIM hIN
      E hEN hEbot hEsd hEfree hnotFrob p hp x hxJ hx1 hxM hxK hxord hnorm hcent
      (Nat.card ↥(hallCoreOf N)) (Nat.card ↥E) rfl rfl hph hep
  set Ψ : G → ℂ := (ν ⟨ζ, hζ⟩ : G → ℂ) with hΨdef
  obtain ⟨hsi, hmatch, -, -, hval, hKK', ⟨c, hc⟩, hvb⟩ := hall Ψ rfl
  have hΨspan : Ψ ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualChars (hν.mem_virtualChars _)
  have hζspan : ζ ∈ Submodule.span ℤ (Irr ↥N) := Submodule.subset_span hζIrr
  obtain ⟨g, hgC, hgB⟩ := Set.not_subset.1 hCK
  have hgK : g ∈ hallCoreOf M := hgC.1
  have hxg : Commute x g := (mem_centralizer_iff.1 hgC.2) x (Subgroup.mem_zpowers x)
  have hu := sq_norm_lower_bound (M := M) hp (e := Nat.card ↥E) (by omega) hep hΨspan
    (c := c) hc hKK' hval (N := N) (ζ := ζ) hζ1 hζspan (g := g) hxord (hallCoreOf_le N hxJ)
    hgK hgB hxg hmatch
  have hv := one_sub_div_le_re_cfIP (N := N) (Ψ := Ψ)
    (h := Nat.card ↥(hallCoreOf N)) (e := Nat.card ↥E) hvb
  have hdisj := disjoint_totalDadeSupport_hallCoreOf h₂ h₄ h₇ hG hM hN hIM hIN hpJ hpK
  have huv := two_norms_lt_one h₇ hG hM hN hIM hIN hdisj (Ψ := Ψ) hsi
  have hmkh : Nat.card ↥M ≤ Nat.card ↥(hallCoreOf M) * Nat.card ↥(hallCoreOf N) := by
    rw [hMsd.natCard_eq_mul]
    exact Nat.mul_le_mul_left _ (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hDJ))
  have hbk : Nat.card ↥(⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) ≤ Nat.card ↥(hallCoreOf M) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le (Subgroup.commutator_le_self _))
  have hlt := lt_four_mul_of_norm_bounds (k := Nat.card ↥(hallCoreOf M))
    (b := Nat.card ↥(⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G)) (m := Nat.card ↥M)
    (h := Nat.card ↥(hallCoreOf N)) (e := Nat.card ↥E)
    Nat.card_pos Nat.card_pos Nat.card_pos Nat.card_pos hbk hE3 hmkh hu hv huv
  have hrel : Nat.card ↥(⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G)
      * (⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G).relIndex (hallCoreOf M)
      = Nat.card ↥(hallCoreOf M) := natCard_mul_relIndex (Subgroup.commutator_le_self _)
  have hge := add_one_le_relIndex_commutator_hallCoreOf hG hM hKbot hMnormK hMsd hD₀ hexp
    hD₀free hp hpK hpM
  have hbpos : 0 < Nat.card ↥(⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) := Nat.card_pos
  have h4 : 4 ≤ (⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G).relIndex (hallCoreOf M) := by omega
  have hfin : 4 * Nat.card ↥(⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G)
      ≤ Nat.card ↥(hallCoreOf M) := by
    calc 4 * Nat.card ↥(⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G)
        ≤ (⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G).relIndex (hallCoreOf M)
            * Nat.card ↥(⁅hallCoreOf M, hallCoreOf M⁆ : Subgroup G) :=
          Nat.mul_le_mul_right _ h4
      _ = Nat.card ↥(hallCoreOf M) := by rw [mul_comm]; exact hrel
  omega

end CFSG.FeitThompson.Proofs

end

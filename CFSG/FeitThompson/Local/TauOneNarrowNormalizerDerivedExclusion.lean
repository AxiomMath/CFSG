module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerCommonFactor
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerOutsideNarrowPrimeFactor
import CFSG.FeitThompson.Local.PrimeFreeFactorDerivedOrder
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.ExceptionalInvariantSylowSeparation
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem natCard_commutator_subgroupOf {K T : Subgroup G} (h : K ≤ T) :
    Nat.card (_root_.commutator ↥(K.subgroupOf T)) = Nat.card (⁅K, K⁆ : Subgroup G) := by
  rw [natCard_commutator_subtype (K.subgroupOf T), ← Subgroup.card_subtype T,
    Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h]

theorem sup_eq_of_coe_eq_mul {D J T : Subgroup G} (hDT : D ≤ T) (hJT : J ≤ T)
    (h : (T : Set G) = (D : Set G) * (J : Set G)) : D ⊔ J = T := by
  refine le_antisymm (sup_le hDT hJT) fun x hx => ?_
  have hx' : x ∈ (D : Set G) * (J : Set G) := by rw [← h]; exact hx
  obtain ⟨d, hd, j, hj, rfl⟩ := hx'
  exact mul_mem (le_sup_left (α := Subgroup G) hd) (le_sup_right (α := Subgroup G) hj)

theorem not_dvd_natCard_commutator_of_sup_eq [Finite G] {p : ℕ} (hp : p.Prime)
    {T D J : Subgroup G} (hDT : D ≤ T) (hJT : J ≤ T) (hnorm : (D.subgroupOf T).Normal)
    (hsup : D ⊔ J = T) (hD : ¬ p ∣ Nat.card ↥D)
    (hJ : ¬ p ∣ Nat.card (⁅J, J⁆ : Subgroup G)) :
    ¬ p ∣ Nat.card (⁅T, T⁆ : Subgroup G) := by
  have := hnorm
  rw [← natCard_commutator_subtype T]
  refine not_dvd_natCard_commutator hp (D := D.subgroupOf T) (J := J.subgroupOf T) ?_ ?_ ?_
  · rw [← Subgroup.subgroupOf_sup hDT hJT, hsup, Subgroup.subgroupOf_self]
  · rwa [natCard_subgroupOf_of_le hDT]
  · rwa [natCard_commutator_subgroupOf hJT]

theorem exists_map_conj_le_of_isHallPiSubgroup [Finite G] {π : Set ℕ} {K : Subgroup G}
    (hK : IsHallPiSubgroup π K) {q : ℕ} (hq : q.Prime) (hqπ : q ∈ π) {Y : Subgroup G}
    (hYq : IsPGroup q ↥Y) : ∃ g : G, Y.map (MulAut.conj g : G →* G) ≤ K := by
  have := Fact.mk hq
  obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥K))
  have hQcard : Nat.card ↥((Q : Subgroup ↥K).map K.subtype)
      = q ^ (Nat.card G).factorization q := by
    rw [Subgroup.card_subtype, Q.card_eq_multiplicity,
      factorization_natCard_eq_of_isHallPiSubgroup hq hK hqπ]
  obtain ⟨g, hg⟩ := exists_forall_inv_mul_mul_mem hQcard hYq
  refine ⟨g⁻¹, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have hmem : g⁻¹ * y * g ∈ (Q : Subgroup ↥K).map K.subtype := hg y hy
  have heq : (MulAut.conj g⁻¹ : G →* G) y = g⁻¹ * y * g := by
    simp [MulAut.conj, mul_assoc]
  rw [heq]
  exact Subgroup.map_subtype_le _ hmem

theorem natCard_commutator_normalizer_map_conj [Finite G] (Y : Subgroup G) (g : G) :
    Nat.card (⁅normalizer ((Y.map (MulAut.conj g : G →* G) : Subgroup G) : Set G),
        normalizer ((Y.map (MulAut.conj g : G →* G) : Subgroup G) : Set G)⁆ : Subgroup G)
      = Nat.card (⁅normalizer (Y : Set G), normalizer (Y : Set G)⁆ : Subgroup G) := by
  rw [normalizer_map_conj, ← Subgroup.map_commutator]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem not_dvd_natCard_commutator_normalizer_of_le [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : Prep09.IsMinimalSimpleOddOrder G) {M E : Subgroup G} (hM : IsCoatom M)
    (hE : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E)
    {p : ℕ} (hpτ : p ∈ tau1Primes M) (hpβ : p ∉ betaPrimes G)
    {q : ℕ} (hqσ : q ∈ sigmaPrimes M) {Y : Subgroup G} (hYM : Y ≤ M) (hY : Y ≠ ⊥)
    (hYq : IsPGroup q ↥Y) :
    ¬ p ∣ Nat.card (⁅normalizer (Y : Set G), normalizer (Y : Set G)⁆ : Subgroup G) := by
  have hp : p.Prime := prime_of_mem_tau1Primes hpτ
  have hq : q.Prime := prime_of_mem_sigmaPrimes hqσ
  have hsimple := hG.isSimpleGroup
  have : Fintype G := Fintype.ofFinite G
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hpM' : ¬ p ∣ Nat.card (⁅M, M⁆ : Subgroup G) :=
    not_dvd_natCard_commutator_of_mem_tau1Primes hpτ
  have hpσM : p ∉ sigmaPrimes M := notMem_sigmaPrimes_of_mem_tau1Primes hpτ
  have hpS : ¬ p ∣ Nat.card ↥(sigmaCore M) := fun hd =>
    hpσM (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hd, Nat.card_pos.ne'⟩))
  have hpE : p ∣ Nat.card ↥E := by
    have hcard : Nat.card ↥M = Nat.card ↥(sigmaCore M) * Nat.card ↥E := hE.natCard_eq_mul
    have hdM := dvd_natCard_of_mem_tau1Primes hpτ
    rw [hcard] at hdM
    exact ((Nat.Prime.dvd_mul hp).1 hdM).resolve_left hpS
  by_cases hNM : normalizer (Y : Set G) ≤ M
  · exact fun hd => hpM' (hd.trans (Subgroup.card_dvd_of_le (Subgroup.commutator_mono hNM hNM)))
  ·
    have hNtop : normalizer (Y : Set G) ≠ ⊤ :=
      (normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hq hY hYq).ne
    obtain ⟨T, hT, hNT⟩ := exists_isCoatom_ge_of_ne_top hNtop
    have hMT : M ≠ T := fun h => hNM (h ▸ hNT)
    have hJ : ¬ p ∣ Nat.card (⁅M ⊓ T, M ⊓ T⁆ : Subgroup G) := fun hd =>
      hpM' (hd.trans (Subgroup.card_dvd_of_le
        (Subgroup.commutator_mono inf_le_left inf_le_left)))
    have hpT' : ¬ p ∣ Nat.card (⁅T, T⁆ : Subgroup G) := by
      by_cases hqT : q ∈ sigmaPrimes T
      ·
        obtain ⟨hDnorm, hpD, hTeq⟩ :=
          FBG_sigma_prime_normalizer_common_sigma_prime_factor h₁ h₇ h₈ G hG02 M T hM hT hMT
            q hq hqσ Y hYM hY hYq hNT E hE p hp hpE hpβ hqT _ rfl
        have hDT : pComplCoreIn p (⁅T, T⁆ : Subgroup G) ≤ T :=
          (pComplCoreIn_le p (⁅T, T⁆ : Subgroup G)).trans (Subgroup.commutator_le_self T)
        exact not_dvd_natCard_commutator_of_sup_eq hp hDT inf_le_right hDnorm
          (sup_eq_of_coe_eq_mul hDT inf_le_right hTeq) hpD hJ
      ·
        obtain ⟨-, hpST, hsdT⟩ :=
          FBG_sigma_prime_normalizer_outside_narrow_prime_factor h₁ h₂ h₃ h₄ h₅ h₆ h₇ G hG02
            M T hM hT hMT q hq hqσ Y hYM hY hYq hNT E hE p hp hpE hpβ hqT
        exact not_dvd_natCard_commutator_of_sup_eq hp (sigmaCore_le T) inf_le_right
          (sigmaCore_normal_subgroupOf T) hsdT.sup_eq hpST hJ
    exact fun hd => hpT' (hd.trans (Subgroup.card_dvd_of_le (Subgroup.commutator_mono hNT hNT)))

theorem FTS_tau_one_narrow_normalizer_derived_exclusion
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_beta_prime_centralizing_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_tau_one_narrow_normalizer_derived_exclusion.{u} := by
  intro G _ _ hG M hM E _ hE p hpτ hpβ q hqσ Y hY hYq
  have hq : q.Prime := prime_of_mem_sigmaPrimes hqσ
  have : Fintype G := Fintype.ofFinite G
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, hHallG, -⟩ := h₁ G hG02 M hM
  obtain ⟨g, hgle⟩ := exists_map_conj_le_of_isHallPiSubgroup hHallG hq hqσ hYq
  have hYbot : Y.map (MulAut.conj g : G →* G) ≠ ⊥ := fun h =>
    hY ((Subgroup.map_eq_bot_iff_of_injective Y (MulAut.conj g).injective).1 h)
  have hYq' : IsPGroup q ↥(Y.map (MulAut.conj g : G →* G)) := hYq.map _
  have hmain := not_dvd_natCard_commutator_normalizer_of_le h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hG hM hE
    hpτ hpβ hqσ (hgle.trans (sigmaCore_le M)) hYbot hYq'
  rwa [natCard_commutator_normalizer_map_conj] at hmain

end

end CFSG.FeitThompson.Proofs

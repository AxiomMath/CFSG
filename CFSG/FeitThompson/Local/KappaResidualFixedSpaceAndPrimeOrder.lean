module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OutsideSigmaKappaSylowCoreNilpotent
import CFSG.FeitThompson.Local.SigmaComplementExistsNontrivial
import CFSG.FeitThompson.Local.HallKappaSubgroupTI
import CFSG.FeitThompson.Local.KappaPositiveMultipleCoreTrivialResidual
import CFSG.FeitThompson.Local.CommonFixedFrobeniusComplementPrimeOrder
import CFSG.FeitThompson.Local.InvariantComplementFittingSelfCentralizing
public import CFSG.FeitThompson.Local.CentralRankThreeConstrainedTransitivity
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib
import CFSG.FeitThompson.Local.CoprimeSolvableCommutatorDecomposition

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup
open Pointwise

universe u

variable {G : Type u} [Group G]

theorem isComplement'_subgroupOf_of_isInternalSemidirectProduct {E A B : Subgroup G}
    (h : FreeCore.IsInternalSemidirectProduct E A B) :
    (A.subgroupOf E).IsComplement' (B.subgroupOf E) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ (Set.eq_univ_of_forall fun x => ?_)
  · refine Subgroup.disjoint_def.2 fun {x} hx1 hx2 => Subtype.ext ?_
    have hmem : (x : G) ∈ A ⊓ B := ⟨mem_subgroupOf.1 hx1, mem_subgroupOf.1 hx2⟩
    rw [h.inf_eq_bot] at hmem
    exact Subgroup.mem_bot.1 hmem
  · have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by rw [← h.coe_eq_mul]; exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact ⟨⟨a, h.left_le ha⟩, mem_subgroupOf.2 ha, ⟨b, h.right_le hb⟩, mem_subgroupOf.2 hb,
      Subtype.ext hab⟩

theorem inf_centralizer_subgroupOf_eq_bot {E V K : Subgroup G}
    (hfree : ∀ k ∈ K, k ≠ 1 → V ⊓ centralizer ({k} : Set G) = ⊥) :
    ∀ k ∈ K.subgroupOf E, k ≠ 1 → V.subgroupOf E ⊓ centralizer ({k} : Set ↥E) = ⊥ := by
  intro k hk hk1
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxV : (x : G) ∈ V := mem_subgroupOf.1 hx.1
  have hxc : (k : G) * (x : G) = (x : G) * (k : G) := by
    have := Subgroup.mem_centralizer_iff.1 hx.2 k rfl
    exact_mod_cast congrArg Subtype.val this
  have hmem : (x : G) ∈ V ⊓ centralizer ({(k : G)} : Set G) :=
    ⟨hxV, Subgroup.mem_centralizer_iff.2 (by simpa using hxc)⟩
  rw [hfree (k : G) (mem_subgroupOf.1 hk) (fun hc => hk1 (Subtype.ext hc))] at hmem
  exact Subtype.ext (Subgroup.mem_bot.1 hmem)

theorem inf_centralizer_eq_bot_of_forall {V K : Subgroup G}
    (hfree : ∀ k ∈ K, k ≠ 1 → V ⊓ centralizer ({k} : Set G) = ⊥) (hK : K ≠ ⊥) :
    V ⊓ centralizer (K : Set G) = ⊥ := by
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hK
  have hkK : (k : G) ∈ K := k.2
  refine le_bot_iff.1 ?_
  rw [← hfree (k : G) hkK (fun h => hk1 (Subtype.ext h))]
  exact inf_le_inf_left V (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hkK))

theorem subgroupOf_inf_centralizer_eq_bot {E V K : Subgroup G} (hKE : K ≤ E)
    (h : V ⊓ centralizer (K : Set G) = ⊥) :
    V.subgroupOf E ⊓ centralizer ((K.subgroupOf E : Subgroup ↥E) : Set ↥E) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxV : (x : G) ∈ V := mem_subgroupOf.1 hx.1
  have hxc : ∀ k ∈ K, k * (x : G) = (x : G) * k := by
    intro k hk
    have h2 := Subgroup.mem_centralizer_iff.1 hx.2 ⟨k, hKE hk⟩ (mem_subgroupOf.2 hk)
    simpa using congrArg (Subtype.val (p := fun z : G => z ∈ E)) h2
  have hmem : (x : G) ∈ V ⊓ centralizer (K : Set G) := ⟨hxV, Subgroup.mem_centralizer_iff.2 hxc⟩
  rw [h] at hmem
  exact Subtype.ext (Subgroup.mem_bot.1 hmem)

theorem map_subtype_commutator_subgroupOf {E A B : Subgroup G} (hAE : A ≤ E) (hBE : B ≤ E) :
    Subgroup.map E.subtype ⁅A.subgroupOf E, B.subgroupOf E⁆ = ⁅A, B⁆ := by
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hAE, inf_eq_left.2 hBE]

theorem map_fixedPoints_conjOnNormalized_subgroupOf {Q E B : Subgroup G}
    (hEN : E ≤ normalizer (Q : Set G)) (hBE : B ≤ E) :
    Subgroup.map Q.subtype (FixedPoints.subgroup
        ((conjOnNormalized Q hEN).comp (B.subgroupOf E).subtype).range ↥Q)
      = Q ⊓ centralizer (B : Set G) := by
  rw [map_subtype_fixedPoints_conjOnNormalized hEN (B.subgroupOf E),
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hBE]

theorem map_fixedPoints_conjOnNormalized_zpowers {Q E : Subgroup G}
    (hEN : E ≤ normalizer (Q : Set G)) (k : ↥E) :
    Subgroup.map Q.subtype (FixedPoints.subgroup
        ((conjOnNormalized Q hEN).comp (zpowers k).subtype).range ↥Q)
      = Q ⊓ centralizer ({(k : G)} : Set G) := by
  rw [map_subtype_fixedPoints_conjOnNormalized hEN (zpowers k), MonoidHom.map_zpowers]
  simp only [Subgroup.coe_subtype]
  rw [centralizer_coe_zpowers]

theorem factorization_natCard_eq_of_isHallPiOf [Finite G] {π : Set ℕ} {V M : Subgroup G} {r : ℕ}
    (hr : r.Prime) (h : Prep03.IsHallPiOf π V M) (hrπ : r ∈ π) :
    (Nat.card ↥M).factorization r = (Nat.card ↥V).factorization r := by
  have hmul : Nat.card ↥(V.subgroupOf M) * (V.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  rw [natCard_subgroupOf h.1] at hmul
  have hidx : ¬ r ∣ (V.subgroupOf M).index := fun hdvd =>
    h.2.2 r (Nat.mem_primeFactors.2 ⟨hr, hdvd, Subgroup.index_ne_zero_of_finite⟩) hrπ
  rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
  simp [Nat.factorization_eq_zero_of_not_dvd hidx]

theorem exists_isSylowSubgroupOf_le_of_isHallPiOf [Finite G] {π : Set ℕ} {V M : Subgroup G} {r : ℕ}
    (hr : r.Prime) (h : Prep03.IsHallPiOf π V M) (hrπ : r ∈ π) :
    ∃ P : Subgroup G, P ≤ V ∧ IsSylowIn r M P := by
  have := Fact.mk hr
  obtain ⟨P⟩ : Nonempty (Sylow r ↥V) := inferInstance
  refine ⟨(P : Subgroup ↥V).map V.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [isSylowIn_iff_natCard hr ((Subgroup.map_subtype_le _).trans h.1),
    Subgroup.card_subtype, P.card_eq_multiplicity,
    factorization_natCard_eq_of_isHallPiOf hr h hrπ]

theorem isHallPiSubgroup_subgroupOf_of_isHallPiOf_compl [Finite G] {π : Set ℕ} {V M : Subgroup G}
    (h : Prep03.IsHallPiOf πᶜ V M) :
    IsHallPiSubgroup {r : ℕ | r.Prime ∧ r ∉ π} (V.subgroupOf M) := by
  refine ⟨isPiSubgroup_iff.2 fun r hr => ?_, fun r hr hr' => ?_⟩
  · rw [natCard_subgroupOf h.1] at hr
    exact ⟨Nat.prime_of_mem_primeFactors hr, h.2.1 r hr⟩
  · exact h.2.2 r hr hr'.2

theorem coprime_natCard_of_isHallPiOf [Finite G] {π π' : Set ℕ} {V K M : Subgroup G}
    (hV : Prep03.IsHallPiOf π V M) (hK : Prep03.IsHallPiOf π' K M)
    (hdisj : ∀ r : ℕ, r ∈ π' → r ∉ π) : (Nat.card ↥K).Coprime (Nat.card ↥V) := by
  by_contra hc
  obtain ⟨r, hr, hrK, hrV⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  exact hdisj r (hK.2.1 r (Nat.mem_primeFactors.2 ⟨hr, hrK, Nat.card_pos.ne'⟩))
    (hV.2.1 r (Nat.mem_primeFactors.2 ⟨hr, hrV, Nat.card_pos.ne'⟩))

theorem prime_natCard_of_frobenius_on_normalized [Finite G] {Q E V K : Subgroup G}
    [Group.IsSolvable ↥E] [Group.IsSolvable ↥Q] [Nontrivial ↥Q]
    (hsd : FreeCore.IsInternalSemidirectProduct E V K)
    (hEN : E ≤ normalizer (Q : Set G)) (hcop : (Nat.card ↥E).Coprime (Nat.card ↥Q))
    (hKbot : K ≠ ⊥)
    (hfree : ∀ k ∈ K, k ≠ 1 → V ⊓ centralizer ({k} : Set G) = ⊥)
    (hCQV : Q ⊓ centralizer (V : Set G) = ⊥)
    (hCQk : ∀ k ∈ K, k ≠ 1 → Q ⊓ centralizer ({k} : Set G) = Q ⊓ centralizer (K : Set G)) :
    (Nat.card ↥K).Prime := by
  set ρ : ↥E →* MulAut ↥Q := conjOnNormalized Q hEN with hρ
  have hVE : V ≤ E := hsd.left_le
  have hKE : K ≤ E := hsd.right_le
  have hCD : FixedPoints.subgroup (ρ.comp (V.subgroupOf E).subtype).range ↥Q = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective, hρ,
      map_fixedPoints_conjOnNormalized_subgroupOf hEN hVE, hCQV]
  have hCK : ∀ k ∈ K.subgroupOf E, k ≠ 1 →
      FixedPoints.subgroup (ρ.comp (zpowers k).subtype).range ↥Q
        = FixedPoints.subgroup (ρ.comp (K.subgroupOf E).subtype).range ↥Q := by
    intro k hk hk1
    refine Subgroup.map_injective Q.subtype_injective ?_
    rw [hρ, map_fixedPoints_conjOnNormalized_zpowers hEN k,
      map_fixedPoints_conjOnNormalized_subgroupOf hEN hKE]
    exact hCQk (k : G) (mem_subgroupOf.1 hk) fun hc => hk1 (Subtype.ext hc)
  have hprime := prime_natCard_of_fixedPoints_eq (ρ := ρ) hcop hsd.normal_subgroupOf
    (isComplement'_subgroupOf_of_isInternalSemidirectProduct hsd)
    (subgroupOf_ne_bot hKE hKbot) (inf_centralizer_subgroupOf_eq_bot hfree) hCD hCK
  rwa [natCard_subgroupOf hKE] at hprime

theorem commutator_eq_of_free_coprime [Finite G] {E V K : Subgroup G}
    (hsd : FreeCore.IsInternalSemidirectProduct E V K) (hVab : IsMulCommutative ↥V)
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥V))
    (hCVK : V ⊓ centralizer (K : Set G) = ⊥) : ⁅V, K⁆ = V := by
  have hVE : V ≤ E := hsd.left_le
  have hKE : K ≤ E := hsd.right_le
  have := hsd.normal_subgroupOf
  have := hVab
  have hcop' : (Nat.card ↥(K.subgroupOf E)).Coprime (Nat.card ↥(V.subgroupOf E)) := by
    rwa [natCard_subgroupOf hKE, natCard_subgroupOf hVE]
  have hkey := sup_inf_centralizer_commutator_eq (V.subgroupOf E) (K.subgroupOf E)
    inferInstance hcop'
  rw [subgroupOf_inf_centralizer_eq_bot hKE hCVK, bot_sup_eq] at hkey
  have h2 := congrArg (Subgroup.map E.subtype) hkey
  rwa [map_subtype_commutator_subgroupOf hVE hKE, Subgroup.map_subgroupOf_eq_of_le hVE] at h2

theorem FBG_kappa_residual_fixed_space_and_prime_order
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : Statements.FTS_outside_sigma_plane_structure.{u}) :
    Statements.FBG_kappa_residual_fixed_space_and_prime_order.{u} := by
  intro G _ _ hG M K U hsetup
  have : Fintype G := Fintype.ofFinite G
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG03 : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG04 : IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨hHallS, -, -⟩ := h₁ G hG02 M hsetup.isCoatom
  have hKH : Prep03.IsHallPiOf (kappaPrimes M) K M :=
    isHallPiOf_of_isHallPiSubgroupOf ⟨hsetup.le_M_K, hsetup.hall_K⟩
  obtain ⟨hKbot, V, E₁, hVab, hVhall, hsemiM, hsemiVK, -, -, -, -, hCSX, hCSK, hCVk⟩ :=
    h₂ G hG03 M K hsetup.isCoatom hsetup.kappaPrimes_nonempty hKH
  have hsemiM' : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) (V ⊔ K) :=
    isInternalSemidirectProduct_of_isSemidirect hsemiM
  have hsemiVK' : FreeCore.IsInternalSemidirectProduct (V ⊔ K) V K :=
    isInternalSemidirectProduct_of_isSemidirect hsemiVK
  have hVM : V ≤ M := hVhall.1
  have hEM : (V ⊔ K : Subgroup G) ≤ M := hsemiM'.right_le
  have hEnetop : (V ⊔ K : Subgroup G) ≠ ⊤ := fun h => hsetup.isCoatom.1 (top_le_iff.1 (h ▸ hEM))
  have hSnetop : sigmaCore M ≠ ⊤ := fun h =>
    hsetup.isCoatom.1 (top_le_iff.1 (h ▸ sigmaCore_le M))
  have hEsolv : Group.IsSolvable ↥(V ⊔ K : Subgroup G) := hG.isSolvable _ hEnetop
  have hSsolv : Group.IsSolvable ↥(sigmaCore M) := hG.isSolvable _ hSnetop
  have hSbot : sigmaCore M ≠ ⊥ := by
    intro h
    refine hCSK ?_
    change sigmaCore M ⊓ centralizer (K : Set G) = ⊥
    rw [h, bot_inf_eq]
  have hSnt : Nontrivial ↥(sigmaCore M) := (Subgroup.nontrivial_iff_ne_bot _).2 hSbot
  have hEN : (V ⊔ K : Subgroup G) ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    hEM.trans hsemiM'.le_normalizer
  have hcopSE : (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥(V ⊔ K : Subgroup G)) :=
    (isHallOf_and_coprime_of_isInternalSemidirectProduct hHallS hEM hsemiM').2
  have hcard1 : Nat.card ↥M = Nat.card ↥(sigmaCore M) * (Nat.card ↥V * Nat.card ↥K) := by
    rw [hsemiM'.natCard_eq_mul, hsemiVK'.natCard_eq_mul]
  have hcard2 : Nat.card ↥M = Nat.card ↥(sigmaCore M) * (Nat.card ↥U * Nat.card ↥K) := by
    rw [hsetup.semidirect_M.natCard_eq_mul, hsetup.semidirect_UK.natCard_eq_mul]
  have hVU : Nat.card ↥V = Nat.card ↥U :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos
      (Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcard1.symm.trans hcard2))
  have hVbot : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hVU
    exact hsetup.ne_bot_U (Subgroup.card_eq_one.1 hVU.symm)
  obtain ⟨r, hrmem⟩ := Nat.nonempty_primeFactors.2 ((Subgroup.one_lt_card_iff_ne_bot V).2 hVbot)
  have hr : r.Prime := Nat.prime_of_mem_primeFactors hrmem
  have hrπ : r ∈ (sigmaPrimes M ∪ kappaPrimes M)ᶜ := hVhall.2.1 r hrmem
  obtain ⟨P, hPV, hPsyl⟩ := exists_isSylowSubgroupOf_le_of_isHallPiOf hr hVhall hrπ
  have hrM : r ∣ Nat.card ↥M :=
    (Nat.dvd_of_mem_primeFactors hrmem).trans (Subgroup.card_dvd_of_le hVM)
  obtain ⟨-, ⟨A, hAset, -, -, hCA⟩, hnil⟩ :=
    FNI_outside_sigma_kappa_sylow_core_nilpotent h₁ h₃ h₄ G hG04 r M P hsetup.isCoatom hr hrM
      hrπ hPsyl
  have hAV : A ≤ V := by
    intro x hx
    have hx' : x ∈ {x | x ∈ (P : Set G) ∧ x ^ r = 1} := hAset ▸ hx
    exact hPV hx'.1
  have hCSV : sigmaCore M ⊓ centralizer (V : Set G) = ⊥ :=
    le_bot_iff.1 (hCA ▸ inf_le_inf_left _ (Subgroup.centralizer_le hAV))
  have hCVK : V ⊓ centralizer (K : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_forall (fun k hk hk1 => hCVk k hk hk1) hKbot
  have hCSk : ∀ k ∈ K, k ≠ 1 →
      sigmaCore M ⊓ centralizer ({k} : Set G) = sigmaCore M ⊓ centralizer (K : Set G) := by
    intro k hk hk1
    have hzle : zpowers k ≤ K := zpowers_le.2 hk
    have hznb : zpowers k ≠ ⊥ := fun h => hk1 (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_zpowers k))
    have hX := hCSX (zpowers k) hzle hznb
    change sigmaCore M ⊓ centralizer ((zpowers k : Subgroup G) : Set G)
      = sigmaCore M ⊓ centralizer (K : Set G) at hX
    rwa [centralizer_coe_zpowers] at hX
  have hKprime : (Nat.card ↥K).Prime :=
    prime_natCard_of_frobenius_on_normalized hsemiVK' hEN hcopSE.symm hKbot
      (fun k hk hk1 => hCVk k hk hk1) hCSV hCSk
  have hcopKV : (Nat.card ↥K).Coprime (Nat.card ↥V) :=
    coprime_natCard_of_isHallPiOf hVhall hKH fun s hs hs' => hs' (Set.mem_union_right _ hs)
  have hcomm : ⁅V, K⁆ = V := commutator_eq_of_free_coprime hsemiVK' hVab hcopKV hCVK
  refine ⟨hKprime, hnil, V, hVbot, hVab, hVM,
    isHallPiSubgroup_subgroupOf_of_isHallPiOf_compl hVhall, hsemiM', hsemiVK', hCSV,
    fun k hk hk1 => hCVk k hk hk1, hcomm.symm, ?_⟩
  exact hcomm.ge.trans (Subgroup.commutator_mono (H₁ := V) (H₂ := K)
    (K₁ := V ⊔ K) (K₂ := V ⊔ K) le_sup_left le_sup_right)

end

end CFSG.FeitThompson.Proofs

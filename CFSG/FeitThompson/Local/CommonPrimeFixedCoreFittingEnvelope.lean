module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Local.CommonPrimeFixedComplementLayout
import CFSG.FeitThompson.Local.PrimeFixedKernelsEqualFitting
import CFSG.FeitThompson.Local.PrimeFixedSylowNotNarrow
import CFSG.FeitThompson.Local.CommonFixedActionNilpotentHallQuotient
import CFSG.FeitThompson.Local.CommonFixedOddActionFittingBound
import CFSG.FeitThompson.Local.FixedFreeComplementNilpotentSections
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.HallComponentsFixedPointFreeSubgroup
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
import CFSG.FeitThompson.Local.HallKappaSubgroupTI
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup QuotientGroup

variable {G : Type*} [Group G]

theorem subgroupOf_pCoreOf [Finite G] (q : ℕ) (L : Subgroup G) :
    (CFSG.FeitThompson.pCoreOf q L).subgroupOf L = pCore q ↥L := by
  rw [CFSG.FeitThompson.pCoreOf, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective]

theorem natCard_pCoreOf [Finite G] (q : ℕ) (L : Subgroup G) :
    Nat.card ↥(CFSG.FeitThompson.pCoreOf q L) = Nat.card ↥(pCore q ↥L) :=
  Subgroup.card_subtype _ _

theorem normal_subgroupOf_pCoreOf [Finite G] (q : ℕ) (L : Subgroup G) :
    ((CFSG.FeitThompson.pCoreOf q L).subgroupOf L).Normal := by
  rw [subgroupOf_pCoreOf]; exact pCore_normal q ↥L

theorem subgroupOf_inf_centralizer_coe_singleton {L S : Subgroup G} (k : ↥L) :
    (S ⊓ centralizer ({(k : G)} : Set G)).subgroupOf L
      = S.subgroupOf L ⊓ centralizer ({k} : Set ↥L) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subtype.ext_iff, Subgroup.coe_mul]

theorem le_map_subtype_of_subgroupOf_le {L A : Subgroup G} {B : Subgroup ↥L} (hAL : A ≤ L)
    (h : A.subgroupOf L ≤ B) : A ≤ B.map L.subtype := by
  have h2 := Subgroup.map_mono (f := L.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hAL] at h2

theorem isComplement'_subgroupOf_of_isInternalSemidirectProduct [Finite G] {L A B : Subgroup G}
    (h : FreeCore.IsInternalSemidirectProduct L A B) :
    (A.subgroupOf L).IsComplement' (B.subgroupOf L) := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [natCard_subgroupOf_of_le h.left_le, natCard_subgroupOf_of_le h.right_le]
    exact h.natCard_eq_mul.symm
  · rw [disjoint_iff]
    have he : A.subgroupOf L ⊓ B.subgroupOf L = (A ⊓ B).subgroupOf L :=
      (Subgroup.comap_inf _ _ _).symm
    rw [he, h.inf_eq_bot, Subgroup.bot_subgroupOf]

theorem pCore_eq_of_normal_of_isPGroup_of_natCard_eq {X : Type*} [Group X] [Finite X] {q : ℕ}
    (hq : q.Prime) {Q : Subgroup X} (hQn : Q.Normal) (hQp : IsPGroup q ↥Q)
    (hcard : Nat.card ↥Q = q ^ (Nat.card X).factorization q) : pCore q X = Q := by
  have : Fact q.Prime := ⟨hq⟩
  have := pCore_normal q X
  have hle : Q ≤ pCore q X := le_pCore hq hQn hQp
  obtain ⟨P⟩ : Nonempty (Sylow q X) := inferInstance
  have hP : pCore q X ≤ (P : Subgroup X) := (isPGroup_pCore hq X).le_sylow_of_normal P
  have hQP : Q = (P : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge (hle.trans hP) (by rw [hcard, P.card_eq_multiplicity])
  exact le_antisymm (hP.trans hQP.ge) hle

theorem map_mk'_le_centralizer_map_mk' {N A B : Subgroup G} [N.Normal]
    (h : A ≤ centralizer (B : Set G)) :
    A.map (mk' N) ≤ centralizer ((B.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  simp only [mk'_apply, ← QuotientGroup.mk_mul]
  rw [mem_centralizer_iff.1 (h ha) b hb]

variable [Finite G] {L J : Subgroup G} {q : ℕ}

theorem mem_sigmaPrimes_of_prime_dvd_natCard_sigmaCore (hq : q.Prime)
    (hdvd : q ∣ Nat.card ↥(sigmaCore L)) : q ∈ sigmaPrimes L :=
  isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore L) q
    (Nat.mem_primeFactors.2 ⟨hq, hdvd, Nat.card_pos.ne'⟩)

theorem sigmaCore_le_fittingOfNormal_of_isNilpotent (hnil : Group.IsNilpotent ↥(sigmaCore L)) :
    sigmaCore L ≤ fittingOfNormal L := by
  rw [← map_fittingRaw_subtype_eq_fittingOfNormal]
  exact le_map_fittingRaw_subtype (sigmaCore_le L) (sigmaCore_normal_subgroupOf L) hnil

theorem natCard_pCore_eq_of_isNilpotent_sigmaCore [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hL : IsCoatom L)
    (hq : q.Prime) (hqσ : q ∈ sigmaPrimes L) (hnil : Group.IsNilpotent ↥(sigmaCore L)) :
    Nat.card ↥(pCore q ↥L) = q ^ (Nat.card ↥L).factorization q := by
  have : Fact q.Prime := ⟨hq⟩
  set S : Subgroup ↥L := (sigmaCore L).subgroupOf L with hS
  have hSn : S.Normal := sigmaCore_normal_subgroupOf L
  have hSnil : Group.IsNilpotent ↥S :=
    Group.nilpotent_of_mulEquiv (_h := hnil) (Subgroup.subgroupOfEquivOfLe (sigmaCore_le L)).symm
  have hHall : IsHallSubgroup (sigmaPrimes L) S :=
    _root_.CFSG.FeitThompson.Proofs.isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hL
  have hqidx : ¬ q ∣ S.index := fun hd =>
    isPiNumber_iff.1 hHall.index q
      (Nat.mem_primeFactors.2 ⟨hq, hd, Subgroup.index_ne_zero_of_finite⟩) hqσ
  obtain ⟨P⟩ : Nonempty (Sylow q ↥S) := inferInstance
  have hPnormal : ((P : Subgroup ↥S)).Normal := sylow_normal_of_isNilpotent P
  have : ((P : Subgroup ↥S)).Characteristic := P.characteristic_of_normal hPnormal
  have hmapn : ((P : Subgroup ↥S).map S.subtype).Normal :=
    normal_map_subtype_of_characteristic S _
  have hmapp : IsPGroup q ↥((P : Subgroup ↥S).map S.subtype) := P.isPGroup'.map _
  have hmapc : Nat.card ↥((P : Subgroup ↥S).map S.subtype)
      = q ^ (Nat.card ↥L).factorization q := by
    rw [Subgroup.card_subtype, P.card_eq_multiplicity,
      factorization_natCard_eq_of_not_dvd_index hqidx]
  rw [pCore_eq_of_normal_of_isPGroup_of_natCard_eq hq hmapn hmapp hmapc, hmapc]

theorem isCommonPrimeFixedSetup_subgroupOf [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hL : IsCoatom L)
    (hq : q.Prime) (hZcard : Nat.card ↥(sigmaCore L ⊓ centralizer (J : Set G)) = q)
    (hnn : ¬ Group.IsNilpotent ↥(sigmaCore L))
    (hsd : FreeCore.IsInternalSemidirectProduct L (sigmaCore L) J) (hJ : J ≠ ⊥)
    (hfix : ∀ X : Subgroup G, X ≤ J → X ≠ ⊥ →
      sigmaCore L ⊓ centralizer (X : Set G) = sigmaCore L ⊓ centralizer (J : Set G)) :
    IsCommonPrimeFixedSetup ↥L q ((sigmaCore L).subgroupOf L) (J.subgroupOf L)
      ((sigmaCore L ⊓ centralizer (J : Set G)).subgroupOf L) := by
  have hLsolv : Group.IsSolvable ↥L := hsolv L hL.1
  have hcompl := isComplement'_subgroupOf_of_isInternalSemidirectProduct hsd
  have hSn : ((sigmaCore L).subgroupOf L).Normal := sigmaCore_normal_subgroupOf L
  have hHall : IsHallSubgroup (sigmaPrimes L) ((sigmaCore L).subgroupOf L) :=
    _root_.CFSG.FeitThompson.Proofs.isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hL
  have hZeq : (sigmaCore L ⊓ centralizer (J : Set G)).subgroupOf L
      = (sigmaCore L).subgroupOf L ⊓ centralizer ((J.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
    subgroupOf_inf_centralizer hsd.right_le
  refine
  { prime := hq
    odd_natCard := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
    isSolvable := hLsolv
    normal_S := hSn
    isComplement := hcompl
    coprime := ?_
    K_ne_bot := ?_
    not_isNilpotent_S := ?_
    commutator_eq := ?_
    Z_eq := hZeq
    natCard_Z := by rw [natCard_subgroupOf_of_le (le_trans inf_le_left (sigmaCore_le L)), hZcard]
    inf_centralizer_S := ?_ }
  · rw [← index_eq_natCard_of_isComplement' hcompl]
    exact hHall.coprime_natCard_index
  · intro hb
    exact hJ (le_bot_iff.1 (le_of_subgroupOf_le hsd.right_le (by rw [hb]; exact bot_le)))
  · intro hnil
    exact hnn (Group.nilpotent_of_mulEquiv (_h := hnil)
      (Subgroup.subgroupOfEquivOfLe (sigmaCore_le L)))
  · refine (eq_commutator_of_isSolvable_of_le_commutator _ _ hcompl.sup_eq_top
      (disjoint_iff.1 hcompl.disjoint) ?_).symm
    rw [commutator_eq_subgroupOf_commutator]
    exact Subgroup.comap_mono
      (_root_.CFSG.FeitThompson.Proofs.sigmaCore_le_commutator hna hodd hsolv hL)
  · intro k hk hk1
    have hkJ : (k : G) ∈ J := (Subgroup.mem_subgroupOf).1 hk
    have hk1' : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext (by simpa using h))
    have hne : zpowers (k : G) ≠ ⊥ := fun hb =>
      hk1' (Subgroup.mem_bot.1 (hb ▸ Subgroup.mem_zpowers (k : G)))
    have h1 := hfix (zpowers (k : G)) (zpowers_le.2 hkJ) hne
    rw [centralizer_coe_zpowers] at h1
    rw [← subgroupOf_inf_centralizer_coe_singleton, h1]

namespace IsCommonPrimeFixedSetup

variable {X : Type*} [Group X] [Finite X] {S K Z D : Subgroup X}
  (h : IsCommonPrimeFixedSetup X q S K Z) (hDS : D ≤ S)
  (hDhall : IsHallSubgroup ({q}ᶜ : Set ℕ) (D.subgroupOf S))
  (hDK : K ≤ normalizer (D : Set X))

include h hDS hDhall hDK

theorem inf_centralizer_Z_le_fittingRaw : S ⊓ centralizer (Z : Set X) ≤ fittingRaw X := by
  have hsetup := h.isPrimeFixedSectionSetup hDS hDhall hDK
  have hQ0 := h.inf_centralizer_lt_pCoreIn hDS hDhall
  have hD := h.isNilpotent_of_isHallSubgroup hDS hDhall
  have := hsetup.normal_Q
  have := IsPrimeFixedSectionSetup.normal_inf_centralizer hsetup hQ0
  rw [IsPrimeFixedSectionSetup.fittingRaw_eq_sectionFixKer_inf_centralizer_K hsetup hQ0 hD,
    le_sectionFixKer_iff, IsPrimeFixedSectionSetup.inf_centralizer_map_mk'_K_eq hsetup hQ0]
  refine ⟨?_, map_mk'_le_centralizer_map_mk' inf_le_right⟩
  rw [h.sup_pCoreIn_eq' hDS hDhall]
  exact inf_le_left

theorem not_isPNarrow_pCoreIn : ¬ IsPNarrow q ↥(pCoreIn q S) := by
  have hsetup := h.isPrimeFixedSectionSetup hDS hDhall hDK
  have : Group.IsSolvable X := h.isSolvable
  exact not_isPNarrow_of_centralizer_lt h.prime h.odd_natCard hsetup.normal_Q
    (h.isComplement'_pCoreIn_sup hDS hDhall hDK)
    hsetup.normal_D hsetup.inf_D_K hsetup.isPGroup_Q hsetup.coprime_Q hsetup.coprime_D_K
    hsetup.D_ne_bot hsetup.K_ne_bot hsetup.inf_centralizer_D hsetup.inf_centralizer_Q
    hsetup.Z_eq hsetup.natCard_Z rfl (h.inf_centralizer_lt_pCoreIn hDS hDhall)

theorem mem_betaPrimes : q ∈ betaPrimes X := by
  have := Fact.mk h.prime
  refine (mem_betaPrimes_iff_exists h.prime).2
    ⟨h.dvd_natCard_S.trans (Subgroup.card_subgroup_dvd_card S), h.sylow, ?_⟩
  rw [h.coe_sylow]
  exact h.not_isPNarrow_pCoreIn hDS hDhall hDK

end IsCommonPrimeFixedSetup

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

theorem FTS_common_prime_fixed_core_fitting_envelope
    (h₁ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u}) :
    Statements.FTS_common_prime_fixed_core_fitting_envelope.{u} := by
  intro G _ _ hG L hL hκ J hJ q hq hZcard
  have : Fintype G := Fintype.ofFinite G
  have := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable
  have hLc : IsCoatom L := hL
  have hFBG : IsFBGAmbient G := ⟨hodd, hG.isSimpleGroup, hna, hsolv⟩
  have hAmb : Prep03.IsAmbient G := ⟨hodd, hG.isSimpleGroup, hna, hsolv⟩
  set Z₀ : Subgroup G := sigmaCore L ⊓ centralizer (J : Set G) with hZ₀
  have hZL : Z₀ ≤ L := le_trans inf_le_left (sigmaCore_le L)
  have hqσ : q ∈ sigmaPrimes L :=
    mem_sigmaPrimes_of_prime_dvd_natCard_sigmaCore hq
      (hZcard ▸ Subgroup.card_dvd_of_le (inf_le_left : Z₀ ≤ sigmaCore L))
  obtain ⟨hJne, U, E₁, h₂'⟩ := h₂ G hAmb L J hLc hκ (isHallPiOf_of_isHallPiSubgroupOf hJ)
  have hfix : ∀ X : Subgroup G, X ≤ J → X ≠ ⊥ →
      sigmaCore L ⊓ centralizer (X : Set G) = sigmaCore L ⊓ centralizer (J : Set G) :=
    h₂'.2.2.2.2.2.2.2.2.1
  have hnncase : ¬ Group.IsNilpotent ↥(sigmaCore L) →
      Nat.card ↥(pCore q ↥L) = q ^ (Nat.card ↥L).factorization q ∧
        sigmaCore L ⊓ centralizer (Z₀ : Set G) ≤ fittingOfNormal L ∧
        q ∈ betaPrimes ↥L := by
    intro hnn
    obtain ⟨-, hstruct, -⟩ := h₁ G hFBG L hLc hnn
    obtain ⟨hsd, -, -⟩ := hstruct J hJ.le hJ.2
    have hsetup := isCommonPrimeFixedSetup_subgroupOf hna hodd hsolv hLc hq hZcard hnn hsd
      hJne hfix
    obtain ⟨D, hDS, hDhall, hDK⟩ := exists_hall_qCompl_normalized_by hsetup
    refine ⟨?_, ?_, hsetup.mem_betaPrimes hDS hDhall hDK⟩
    · exact pCore_eq_of_normal_of_isPGroup_of_natCard_eq hq hsetup.normal_pCoreIn
        hsetup.isPGroup_pCoreIn hsetup.natCard_pCoreIn ▸ hsetup.natCard_pCoreIn
    · have hle := hsetup.inf_centralizer_Z_le_fittingRaw hDS hDhall hDK
      rw [← map_fittingRaw_subtype_eq_fittingOfNormal]
      refine le_map_subtype_of_subgroupOf_le (le_trans inf_le_left (sigmaCore_le L)) ?_
      rw [subgroupOf_inf_centralizer hZL]
      exact hle
  refine ⟨normal_subgroupOf_pCoreOf q L, ⟨CFSG.FeitThompson.pCoreOf_le q L, ?_⟩, ?_, ?_⟩
  · rw [natCard_pCoreOf]
    by_cases hnil : Group.IsNilpotent ↥(sigmaCore L)
    · exact natCard_pCore_eq_of_isNilpotent_sigmaCore hna hodd hsolv hLc hq hqσ hnil
    · exact (hnncase hnil).1
  · by_cases hnil : Group.IsNilpotent ↥(sigmaCore L)
    · exact le_trans inf_le_left (sigmaCore_le_fittingOfNormal_of_isNilpotent hnil)
    · exact (hnncase hnil).2.1
  · intro hnn
    exact (hnncase hnn).2.2

end

end CFSG.FeitThompson.Proofs

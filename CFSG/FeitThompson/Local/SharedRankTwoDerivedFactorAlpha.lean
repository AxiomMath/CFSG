module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.PLengthOneNarrowSylowNormalComplement
import CFSG.FeitThompson.Local.MinimalSimpleProperSubgroupPLengthOne
import CFSG.FeitThompson.Local.InvariantControlUniqueMaximalOvergroup
import CFSG.FeitThompson.Local.LowRankFittingDerivedNilpotent
import CFSG.FeitThompson.Local.NormalComplementSylowDerivedIntersection
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
public import CFSG.FeitThompson.Local.BetaPrimeDerivedComplement
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.Local.PElementNormalSubgroupPLength
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise

universe u

variable {G : Type u} [Group G]

theorem le_normalizer_commutator (M : Subgroup G) :
    M ≤ normalizer ((⁅M, M⁆ : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (commutator_le_self M)).1
    (by rw [← commutator_eq_subgroupOf_commutator]; infer_instance)

theorem map_pComplCore_commutatorEquiv [Finite G] (p : ℕ) (M : Subgroup G) :
    (pComplCore p ↥(_root_.commutator ↥M)).map (commutatorEquiv M : _ →* _)
      = pComplCore p ↥(⁅M, M⁆ : Subgroup G) := by
  rw [pComplCore_eq_piCore, pComplCore_eq_piCore, map_piCore_of_mulEquiv]

theorem pComplCoreIn_commutator_le [Finite G] (p : ℕ) (M : Subgroup G) :
    _root_.CFSG.FeitThompson.pComplCoreIn p (⁅M, M⁆ : Subgroup G) ≤ M :=
  (_root_.CFSG.FeitThompson.pComplCoreIn_le p _).trans (commutator_le_self M)

theorem le_normalizer_pComplCoreIn_commutator [Finite G] (p : ℕ) (M : Subgroup G) :
    M ≤ normalizer
      ((_root_.CFSG.FeitThompson.pComplCoreIn p (⁅M, M⁆ : Subgroup G) : Subgroup G) : Set G) := by
  rw [_root_.CFSG.FeitThompson.pComplCoreIn_eq]
  exact le_normalizer_map_subtype_of_characteristic _ (le_normalizer_commutator M)

theorem not_dvd_natCard_pComplCoreIn_commutator [Finite G] {p : ℕ} (hp : p.Prime)
    (M : Subgroup G) :
    ¬ p ∣ Nat.card ↥(_root_.CFSG.FeitThompson.pComplCoreIn p (⁅M, M⁆ : Subgroup G)) := by
  rw [_root_.CFSG.FeitThompson.pComplCoreIn_eq, Subgroup.card_subtype]
  exact not_dvd_natCard_pComplCore hp _

theorem mem_sigmaPrimes_of_not_isMulCommutative
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    [Finite G] (hG : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G)
    {p : ℕ} {M R : Subgroup G} (hM : IsCoatom M) (hp : p.Prime) (hRM : R ≤ M)
    (hRcard : Nat.card ↥R = p ^ (Nat.card G).factorization p)
    (hrank : elementaryAbelianPRank p ↥R = 2) (hRab : ¬ IsMulCommutative ↥R) :
    p ∈ sigmaPrimes M := by
  by_contra hpσ
  obtain ⟨A₀, ⟨e⟩⟩ := mem_elementaryAbelianRanks.1
    (show 2 ∈ elementaryAbelianRanks p ↥R by
      rw [← hrank]; exact elementaryAbelianPRank_mem_elementaryAbelianRanks hp.one_lt)
  have hplane : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane p (A₀.map R.subtype) :=
    ⟨(A₀.equivMapOfInjective R.subtype R.subtype_injective).symm.trans e⟩
  obtain ⟨-, -, hsyl, -⟩ := h₂ G hG p M (A₀.map R.subtype)
    ⟨hM, hp, hpσ, (Subgroup.map_subtype_le _).trans hRM, hplane⟩
  exact hRab (hsyl R ((_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp hRM).2
    (natCard_eq_pow_factorization_of_le hp hRM hRcard))).1

theorem commutator_le_pComplCoreIn_sup [Finite G] [IsSimpleGroup G] {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hodd : Odd (Nat.card G))
    (hna : ¬ IsMulCommutative G) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    {M R : Subgroup G} (hM : IsCoatom M) (hRM' : R ≤ (⁅M, M⁆ : Subgroup G))
    (hRcard : Nat.card ↥R = p ^ (Nat.card G).factorization p)
    (hrank : elementaryAbelianPRank p ↥R = 2) :
    (⁅M, M⁆ : Subgroup G) ≤ _root_.CFSG.FeitThompson.pComplCoreIn p (⁅M, M⁆ : Subgroup G) ⊔ R := by
  have := Fact.mk hp
  have hsolvM : Group.IsSolvable ↥M := hsolv M hM.1
  have hRM : R ≤ M := hRM'.trans (commutator_le_self M)
  have hoddM : Odd (Nat.card ↥M) := hodd.of_dvd_nat M.card_subgroup_dvd_card
  have hPcard : Nat.card ↥(R.subgroupOf M) = p ^ (Nat.card ↥M).factorization p :=
    natCard_subgroupOf_eq_pow_factorization hRcard hRM
  have hnarrow : IsPNarrow p ↥(R.subgroupOf M) :=
    isPNarrow_of_elementaryAbelianPRank_le_two (by
      rw [elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt (subgroupOfEquivOfLe hRM), hrank])
  have hlen : HasPLengthLeOne p ↥M := hasPLengthLeOne_of_ne_top hna hodd hsolv hM.1 hp
  have h := isNormalPComplement_pComplCore_commutator_of_card (X := ↥M) hp hpodd hoddM
    hPcard hnarrow hlen
  have h' : IsNormalPComplement p (pComplCore p ↥(⁅M, M⁆ : Subgroup G)) := by
    have := h.map_mulEquiv (commutatorEquiv M)
    rwa [map_pComplCore_commutatorEquiv] at this
  obtain ⟨n, hn⟩ := h'.exists_index_eq_pow
  have hKcard : Nat.card ↥(R.subgroupOf (⁅M, M⁆ : Subgroup G))
      = p ^ (Nat.card ↥(⁅M, M⁆ : Subgroup G)).factorization p :=
    natCard_subgroupOf_eq_pow_factorization hRcard hRM'
  have hsup := sup_sylow_eq_top hp h'.not_dvd_natCard hn (Sylow.ofCard _ hKcard)
  have hmap := congrArg (Subgroup.map (⁅M, M⁆ : Subgroup G).subtype) hsup
  rw [Subgroup.map_sup, Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hRM',
    map_top_subtype] at hmap
  rw [_root_.CFSG.FeitThompson.pComplCoreIn_eq]
  exact hmap.ge

theorem alphaCoreIn_ne_bot_of_ne [Finite G] [IsSimpleGroup G] {p : ℕ}
    (hp : p.Prime) (hodd : Odd (Nat.card G)) (hna : ¬ IsMulCommutative G)
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    {M T R : Subgroup G} (hM : IsCoatom M) (hT : IsCoatom T) (hMT : M ≠ T)
    (hRM' : R ≤ (⁅M, M⁆ : Subgroup G))
    (hRcard : Nat.card ↥R = p ^ (Nat.card G).factorization p)
    (hNR : normalizer (R : Set G) ≤ M ⊓ T) : _root_.CFSG.FeitThompson.alphaCoreIn M ≠ ⊥ := by
  have := Fact.mk hp
  have hsolvM : Group.IsSolvable ↥M := hsolv M hM.1
  intro hB
  rw [_root_.CFSG.FeitThompson.alphaCoreIn_eq, Subgroup.map_eq_bot_iff_of_injective _
    M.subtype_injective] at hB
  have hhall := isHallSubgroup_alphaCore hna hodd hsolv hM
  rw [hB] at hhall
  have hindex := isPiNumber_iff.1 hhall.index
  rw [Subgroup.index_bot] at hindex
  have hα : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥M ≤ 2 := by
    intro q hq
    by_contra hcon
    have hmem : q ∈ alphaPrimes ↥M := mem_alphaPrimes.2 ⟨hq, by omega⟩
    have hqdvd : q ∣ Nat.card ↥M := (one_le_elementaryAbelianPRank_iff hq).1 (by omega)
    exact hindex q (Nat.mem_primeFactors.2 ⟨hq, hqdvd, Nat.card_pos.ne'⟩) hmem
  have hoddM : Odd (Nat.card ↥M) := hodd.of_dvd_nat M.card_subgroup_dvd_card
  have hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥(fittingRaw ↥M) ≤ 2 := fun q hq =>
    le_trans (elementaryAbelianPRank_le_of_injective hq.one_lt
      (fittingRaw ↥M).subtype_injective) (hα q hq)
  have hnil : Group.IsNilpotent ↥(_root_.commutator ↥M) := isNilpotent_commutator hoddM hrank
  have hnil' : Group.IsNilpotent ↥(⁅M, M⁆ : Subgroup G) :=
    Group.nilpotent_of_mulEquiv (_h := hnil) (commutatorEquiv M)
  have hKcard : Nat.card ↥(R.subgroupOf (⁅M, M⁆ : Subgroup G))
      = p ^ (Nat.card ↥(⁅M, M⁆ : Subgroup G)).factorization p :=
    natCard_subgroupOf_eq_pow_factorization hRcard hRM'
  have hchar : (R.subgroupOf (⁅M, M⁆ : Subgroup G)).Characteristic :=
    characteristic_of_natCard_eq_pow_factorization hKcard
  have hMnormR : M ≤ normalizer (R : Set G) := by
    have h1 := normalizer_le_normalizer_map_subtype (⁅M, M⁆ : Subgroup G)
      (R.subgroupOf (⁅M, M⁆ : Subgroup G))
    rw [Subgroup.map_subgroupOf_eq_of_le hRM'] at h1
    exact le_trans (le_normalizer_commutator M) h1
  have hMTle : M ≤ T := (hMnormR.trans hNR).trans inf_le_right
  rcases lt_or_eq_of_le hMTle with h | h
  · exact hT.1 (hM.2 T h)
  · exact hMT h

theorem FNI_shared_rank_two_derived_factor_and_alpha
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_shared_rank_two_derived_factor_and_alpha.{u} := by
  intro G _ _ hG p M T R hM hT hMT hp hpodd hRMT hRab hRsyl hrank hNR
  have hsimple := hG.isSimpleGroup
  have := Fact.mk hp
  have hRM : R ≤ M := hRMT.trans inf_le_left
  have hRcard : Nat.card ↥R = p ^ (Nat.card G).factorization p :=
    (_root_.CFSG.FeitThompson.isSylowSubgroup_iff_natCard hp).1 hRsyl
  have hpσ : p ∈ sigmaPrimes M :=
    mem_sigmaPrimes_of_not_isMulCommutative h₂ hG hM hp hRM hRcard hrank hRab
  obtain ⟨hHallOf, -, hSle⟩ :=
    haveI : Fintype G := Fintype.ofFinite G
    h₁ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩ M hM
  have hRS : R ≤ sigmaCore M :=
    le_sigmaCore_of_isPiSubgroup_of_isHallPiSubgroup hHallOf.2 hRM
      (isPiSubgroup_of_natCard_eq_pow hp hRcard hpσ)
  have hRM' : R ≤ (⁅M, M⁆ : Subgroup G) := hRS.trans hSle
  refine ⟨pComplCoreIn_commutator_le p M, le_normalizer_pComplCoreIn_commutator p M,
    not_dvd_natCard_pComplCoreIn_commutator hp M, ?_,
    alphaCoreIn_ne_bot_of_ne hp hG.odd_natCard hG.not_isMulCommutative hG.isSolvable_of_ne_top
      hM hT hMT hRM' hRcard hNR⟩
  set D : Subgroup G := _root_.CFSG.FeitThompson.pComplCoreIn p (⁅M, M⁆ : Subgroup G) with hDdef
  have hDR : (⁅M, M⁆ : Subgroup G) ≤ D ⊔ R :=
    commutator_le_pComplCoreIn_sup hp hpodd hG.odd_natCard hG.not_isMulCommutative
      hG.isSolvable_of_ne_top hM hRM' hRcard hrank
  have hfrat : M ≤ (⁅M, M⁆ : Subgroup G) ⊔ normalizer (R : Set G) :=
    le_sup_normalizer_of_le_normalizer hp (commutator_le_self M) (le_normalizer_commutator M)
      hRM' (natCard_eq_pow_factorization_of_le hp hRM hRcard)
  have hMle : M ≤ D ⊔ (M ⊓ T) := by
    refine hfrat.trans (sup_le (hDR.trans (sup_le le_sup_left ?_)) (le_trans hNR le_sup_right))
    exact le_trans (le_trans Subgroup.le_normalizer hNR) le_sup_right
  have hMeq : D ⊔ (M ⊓ T) = M :=
    le_antisymm (sup_le (hDdef ▸ pComplCoreIn_commutator_le p M) inf_le_left) hMle
  have hcoe : ((D ⊔ (M ⊓ T) : Subgroup G) : Set G)
      = (D : Set G) * ((M ⊓ T : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left D (M ⊓ T)
      (inf_le_left.trans (hDdef ▸ le_normalizer_pComplCoreIn_commutator p M))
  rwa [hMeq] at hcoe

end

end CFSG.FeitThompson.Proofs

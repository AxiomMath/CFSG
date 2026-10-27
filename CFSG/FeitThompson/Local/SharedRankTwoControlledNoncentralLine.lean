module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SharedRankTwoDerivedFactorAlpha
import CFSG.FeitThompson.Local.PrimeCubeCentralizerCompetingMaximum
import CFSG.FeitThompson.Local.NonuniqueLinesAlphaCoreTrivial
import CFSG.FeitThompson.Local.KappaResidualLocalNormalizer
import CFSG.FeitThompson.Local.NormalProductCoprimeNormalizerFactorization
import CFSG.FeitThompson.Local.PrimeCubeNonabelianCommutatorCentre
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson.Prep08
  Subgroup Pointwise

universe u

variable {G : Type u} [Group G]

theorem normalizer_inf_le_of_normal_product [Finite G] {M T D Z : Subgroup G}
    (hsolv : Group.IsSolvable ↥M) (hDM : D ≤ M) (hMD : M ≤ normalizer (D : Set G))
    (hprod : (M : Set G) = (D : Set G) * ((M ⊓ T : Subgroup G) : Set G))
    (hZMT : Z ≤ M ⊓ T) (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Z))
    (hCDZ : D ⊓ centralizer (Z : Set G) ≤ T) :
    normalizer (Z : Set G) ⊓ M ≤ T := by
  have := hsolv
  have hZM : Z ≤ M := hZMT.trans inf_le_left
  have hDnormal : (D.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).2 hMD
  have hMsup : M ≤ D ⊔ (M ⊓ T) := by
    intro x hx
    have hx' : x ∈ (D : Set G) * ((M ⊓ T : Subgroup G) : Set G) := by rw [← hprod]; exact hx
    obtain ⟨d, hd, y, hy, rfl⟩ := hx'
    exact Subgroup.mul_mem_sup hd hy
  have hDJ : D.subgroupOf M ⊔ (M ⊓ T).subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hDM inf_le_left, Subgroup.subgroupOf_eq_top]
    exact hMsup
  have hcop' : Nat.Coprime (Nat.card ↥(D.subgroupOf M)) (Nat.card ↥(Z.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv]
    exact hcop
  have hform := CFSG.FeitThompson.normalizer_eq_inf_centralizer_sup_inf_normalizer
    (D := D.subgroupOf M) (J := (M ⊓ T).subgroupOf M) (U := Z.subgroupOf M) hDJ
    (Subgroup.comap_mono hZMT) hcop'
  intro x hx
  obtain ⟨hxN, hxM⟩ := Subgroup.mem_inf.1 hx
  have h1 : (⟨x, hxM⟩ : ↥M) ∈ normalizer ((Z.subgroupOf M : Subgroup ↥M) : Set ↥M) :=
    (mem_normalizer_subgroupOf_iff hZM ⟨x, hxM⟩).2 hxN
  rw [hform] at h1
  have hle : (D.subgroupOf M ⊓ centralizer ((Z.subgroupOf M : Subgroup ↥M) : Set ↥M))
      ⊔ ((M ⊓ T).subgroupOf M ⊓ normalizer ((Z.subgroupOf M : Subgroup ↥M) : Set ↥M))
      ≤ T.subgroupOf M := by
    refine sup_le (fun y hy => ?_) (le_trans inf_le_left (Subgroup.comap_mono inf_le_right))
    obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.1 hy
    exact Subgroup.mem_subgroupOf.2 (hCDZ (Subgroup.mem_inf.2
      ⟨Subgroup.mem_subgroupOf.1 hyD, (mem_centralizer_subgroupOf_iff hZM y).1 hyC⟩))
  exact Subgroup.mem_subgroupOf.1 (hle h1)

theorem isUniqueMaximalOvergroup_of_forall_eq [Finite G] {p : ℕ} (hp : p.Prime)
    (hsimple : IsSimpleGroup G) (hnab : ¬ IsMulCommutative G) {M A₀ : Subgroup G}
    (hM : IsCoatom M) (hcard : Nat.card ↥A₀ = p)
    (hno : ∀ K : Subgroup G, IsCoatom K → normalizer (A₀ : Set G) ≤ K → K = M) :
    IsUniqueMaximalOvergroup (normalizer (A₀ : Set G)) M := by
  have := hsimple
  have hA₀ : A₀ ≠ ⊥ := fun h => by
    rw [h] at hcard; simp at hcard; exact hp.one_lt.ne' hcard.symm
  have hpg : IsPGroup p ↥A₀ := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  have hlt : normalizer (A₀ : Set G) < ⊤ := normalizer_lt_top_of_isPGroup hnab hp hA₀ hpg
  obtain ⟨N, hN, hNle⟩ := exists_isCoatom_ge_of_ne_top hlt.ne
  exact ⟨hM, (hno N hN hNle) ▸ hNle, fun K hK hKle => hno K hK hKle⟩

theorem alphaCoreOf_eq_alphaCoreIn [Finite G] (M : Subgroup G) :
    alphaCoreOf M = _root_.CFSG.FeitThompson.alphaCoreIn M := by
  rw [alphaCoreOf, _root_.CFSG.FeitThompson.alphaCoreIn_eq]

theorem exists_line_forall_isCoatom_eq [Finite G]
    (h₄ : Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (hG : IsMinimalSimpleOddOrder G) {p : ℕ} (hp : p.Prime) {M A : Subgroup G} (hM : IsCoatom M)
    (hAM : A ≤ M) (hA : IsPlaneAt p A) (hB : alphaCoreOf M ≠ ⊥) :
    ∃ A₀ ≤ A, Nat.card ↥A₀ = p ∧
      ∀ K : Subgroup G, IsCoatom K → normalizer (A₀ : Set G) ≤ K → K = M := by
  have key : ¬ ∀ Y ≤ A, Nat.card ↥Y = p →
      ∃ T : Subgroup G, IsCoatom T ∧ T ≠ M ∧ normalizer ((Y : Subgroup G) : Set G) ≤ T := by
    intro hall
    exact hB (FTS_nonunique_lines_alpha_core_trivial h₄ G hG M A p ⟨hM, hp, hAM, hA, hall⟩).1
  by_contra hcon
  refine key fun Y hY hYcard => ?_
  by_contra hno
  refine hcon ⟨Y, hY, hYcard, fun K hK hKle => ?_⟩
  by_contra hKM
  exact hno ⟨K, hK, hKM, hKle⟩

theorem FNI_shared_rank_two_controlled_noncentral_line
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₄ : Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₅ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FNI_shared_rank_two_controlled_noncentral_line.{u} := by
  intro G _ _ hG p M T R Q A hM hT hMT hp hpodd hRMT hRnab hRsyl hrank hNR hQR hQnab hQcard
    hQexp hAQ hAplane
  have hfact := Fact.mk hp
  have hGmin : IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  obtain ⟨hDM, hMD, hpD, hprod, hBne⟩ :=
    FNI_shared_rank_two_derived_factor_and_alpha h₁ h₂ G hG p M T R hM hT hMT hp hpodd hRMT
      hRnab hRsyl hrank hNR
  set D : Subgroup G := _root_.CFSG.FeitThompson.pComplCoreIn p (⁅M, M⁆ : Subgroup G) with hDdef
  set Z : Subgroup G := Q ⊓ centralizer (Q : Set G) with hZdef
  have hQMT : Q ≤ M ⊓ T := hQR.trans hRMT
  have hcopD : Nat.Coprime (Nat.card ↥D) p := (hp.coprime_iff_not_dvd.2 hpD).symm
  have hZcard : Nat.card ↥Z = p := by
    rw [hZdef, ← map_center_subtype, Subgroup.card_subtype]
    exact card_center_of_card_eq_prime_cube hp hQcard hQnab
  have hZMT : Z ≤ M ⊓ T := (hZdef ▸ inf_le_left : Z ≤ Q).trans hQMT
  have hCDZ : D ⊓ centralizer (Z : Set G) ≤ T :=
    FNI_prime_cube_centralizer_in_competing_maximum h₁ h₃ h₄ h₅ G hG p M T Q D hM hT hp hpodd
      hQMT hQnab hQcard hQexp hDM hMD hcopD
  have hNMZ : normalizer (Z : Set G) ⊓ M ≤ T :=
    normalizer_inf_le_of_normal_product (hG.isSolvable_of_ne_top M hM.1) hDM hMD hprod hZMT
      (by rw [hZcard]; exact hcopD) hCDZ
  have hZnot : ¬ IsUniqueMaximalOvergroup (normalizer (Z : Set G)) M := fun hu =>
    hMT (hu.eq_of_isCoatom hT (le_trans (le_inf le_rfl hu.le) hNMZ)).symm
  have hAM : A ≤ M := (hAQ.trans hQMT).trans inf_le_left
  have hAplane : IsPlaneAt p A := by
    refine ⟨?_, hAplane.natCard'⟩
    rw [isElementaryAbelian_iff_isElementaryAbelianSubgroup]
    exact hAplane.isElementaryAbelianSubgroup
  obtain ⟨A₀, hA₀A, hA₀card, hA₀no⟩ :=
    exists_line_forall_isCoatom_eq h₄ hGmin hp hM hAM hAplane
      (by rw [alphaCoreOf_eq_alphaCoreIn]; exact hBne)
  have hA₀ := isUniqueMaximalOvergroup_of_forall_eq hp hG.isSimpleGroup
    hG.not_isMulCommutative hM hA₀card hA₀no
  exact ⟨A₀, hA₀A, hA₀card, fun hEq => hZnot (hEq ▸ hA₀), hA₀⟩

end

end CFSG.FeitThompson.Proofs

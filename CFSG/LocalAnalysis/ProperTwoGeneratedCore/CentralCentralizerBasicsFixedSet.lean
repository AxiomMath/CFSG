module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBasics
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorCentralizerAction

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G}

theorem coreSetting_mem_fixedSet_iff (hset : CoreSetting G S H) {u : G} (huH : u ∈ H)
    (hu : orderOf u = 2) (β : pointRightCosetSpace H) :
    β ∈ elementFixedSet H u ↔ ∃ m ∈ Subgroup.centralizer ({u} : Set G),
      pointRightCosetMul H (Quotient.mk (QuotientGroup.rightRel H) 1) m = β := by
  constructor
  · exact coreSetting_exists_centralizer_mul_eq hset hu ((base_mem_elementFixedSet_iff u).mpr huH)
  · rintro ⟨m, hm, rfl⟩
    exact original_centralizer_preserves_full_fixedSet H u m hm _
      ((base_mem_elementFixedSet_iff u).mpr huH)

theorem coreSetting_existsUnique_common_fixed_point (hset : CoreSetting G S H) {t u : G}
    (ht : orderOf t = 2) (hu : orderOf u = 2) (hne : t ≠ u) (htu : Commute t u) :
    ∃! β : pointRightCosetSpace H, β ∈ elementFixedSet H u ∧ β ∈ elementFixedSet H t := by
  set V := Subgroup.zpowers t ⊔ Subgroup.zpowers u with hV
  have hVe : IsElemAbelian 2 V := commuting_elementary_sup _ _ (involution_zpowers_elementary t ht)
    (involution_zpowers_elementary u hu) (zpowers_le_centralizer_zpowers htu)
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have huV : u ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hVrank : 2 ≤ Open.pRank 2 V := two_le_pRank_of_commuting_involutions htV huV ht hu hne htu
  have hfix : ∀ β : pointRightCosetSpace H, V ≤ rightCosetStabilizer H β ↔
      β ∈ elementFixedSet H u ∧ β ∈ elementFixedSet H t := by
    intro β
    rw [mem_elementFixedSet_iff_mem_stabilizer, mem_elementFixedSet_iff_mem_stabilizer]
    exact ⟨fun h => ⟨h huV, h htV⟩, fun h =>
      sup_le (Subgroup.zpowers_le.mpr h.2) (Subgroup.zpowers_le.mpr h.1)⟩
  obtain ⟨β, hβ⟩ := coreSetting_twoGroup_fixes_point hset (isPGroup_of_isElemAbelian hVe)
  exact ⟨β, (hfix β).mp hβ, fun γ hγ =>
    coreSetting_eq_of_le_stabilizer hset hVrank ((hfix γ).mpr hγ) hβ⟩

theorem coreSetting_involution_eq_of_fixes_two_points (hset : CoreSetting G S H) {t u : G}
    (ht : orderOf t = 2) (hu : orderOf u = 2) (htu : Commute t u)
    {β γ : pointRightCosetSpace H} (hβ : β ∈ elementFixedSet H u) (hβt : β ∈ elementFixedSet H t)
    (hγ : γ ∈ elementFixedSet H u) (hγt : γ ∈ elementFixedSet H t) (hne : β ≠ γ) : t = u := by
  by_contra htne
  exact hne ((coreSetting_existsUnique_common_fixed_point hset ht hu htne htu).unique
    ⟨hβ, hβt⟩ ⟨hγ, hγt⟩)

omit [Finite G] in
@[expose] def fixedSetKernel (H : Subgroup G) (u : G) : Subgroup G :=
  Subgroup.centralizer ({u} : Set G) ⊓ pointwiseRightStabilizer H (elementFixedSet H u)

omit [Finite G] in
theorem mem_fixedSetKernel_iff {u k : G} :
    k ∈ fixedSetKernel H u ↔ k ∈ Subgroup.centralizer ({u} : Set G) ∧
      ∀ β ∈ elementFixedSet H u, pointRightCosetMul H β k = β := by
  rw [fixedSetKernel, Subgroup.mem_inf, mem_pointwiseRightStabilizer]

omit [Finite G] in
theorem self_mem_fixedSetKernel (u : G) : u ∈ fixedSetKernel H u :=
  mem_fixedSetKernel_iff.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, fun _ hβ => hβ⟩

omit [Finite G] in
theorem centralizer_le_normalizer_fixedSetKernel (u : G) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (fixedSetKernel H u : Set G) := by
  have hconj : ∀ m ∈ Subgroup.centralizer ({u} : Set G), ∀ k ∈ fixedSetKernel H u,
      m * k * m⁻¹ ∈ fixedSetKernel H u := by
    intro m hm k hk
    rw [mem_fixedSetKernel_iff] at hk ⊢
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hk.1) (Subgroup.inv_mem _ hm),
      fun β hβ => ?_⟩
    rw [← pointRightCosetMul_mul, ← pointRightCosetMul_mul,
      hk.2 _ (original_centralizer_preserves_full_fixedSet H u m hm β hβ),
      pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one]
  intro m hm
  refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨hconj m hm k, fun hk => ?_⟩
  have h := hconj m⁻¹ (Subgroup.inv_mem _ hm) _ hk
  have hk' : m⁻¹ * (m * k * m⁻¹) * m⁻¹⁻¹ = k := by group
  rwa [hk'] at h

theorem coreSetting_le_pointwiseRightStabilizer_of_normalized (hset : CoreSetting G S H) {u : G}
    (huH : u ∈ H) (hu : orderOf u = 2) {N : Subgroup G} (hNH : N ≤ H)
    (hMN : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (N : Set G)) :
    N ≤ pointwiseRightStabilizer H (elementFixedSet H u) := by
  intro n hn
  rw [mem_pointwiseRightStabilizer]
  intro β hβ
  obtain ⟨m, hm, rfl⟩ := (coreSetting_mem_fixedSet_iff hset huH hu β).mp hβ
  have hmn : m * n * m⁻¹ ∈ H := hNH ((Subgroup.mem_normalizer_iff.mp (hMN hm) n).mp hn)
  have hprod : m * n = m * n * m⁻¹ * m := by group
  have hfix : pointRightCosetMul H (Quotient.mk (QuotientGroup.rightRel H) 1) (m * n * m⁻¹) =
      Quotient.mk (QuotientGroup.rightRel H) 1 := (point_right_base_fixed_iff H _).mpr hmn
  rw [pointRightCosetMul_mul, hprod, ← pointRightCosetMul_mul, hfix]

theorem coreSetting_le_fixedSetKernel_of_normalized (hset : CoreSetting G S H) {u : G}
    (huH : u ∈ H) (hu : orderOf u = 2) {N : Subgroup G} (hNH : N ≤ H)
    (hNM : N ≤ Subgroup.centralizer ({u} : Set G))
    (hMN : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (N : Set G)) :
    N ≤ fixedSetKernel H u :=
  le_inf hNM (coreSetting_le_pointwiseRightStabilizer_of_normalized hset huH hu hNH hMN)

theorem coreSetting_fixedSetKernel_involution_eq (hset : CoreSetting G S H) {u : G} (huH : u ∈ H)
    (hu : orderOf u = 2) (hesc : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) {t : G}
    (htK : t ∈ fixedSetKernel H u) (ht : orderOf t = 2) : t = u := by
  obtain ⟨m, hm, hmH⟩ := Set.not_subset.mp hesc
  rw [mem_fixedSetKernel_iff] at htK
  have hα := (base_mem_elementFixedSet_iff (H := H) u).mpr huH
  have hαm := original_centralizer_preserves_full_fixedSet H u m hm _ hα
  have hne : Quotient.mk (QuotientGroup.rightRel H) 1 ≠
      pointRightCosetMul H (Quotient.mk (QuotientGroup.rightRel H) 1) m := by
    rw [pointRightCosetMul_mk, one_mul, Ne, quotient_mk_eq_iff, inv_one, mul_one]
    exact hmH
  exact coreSetting_involution_eq_of_fixes_two_points hset ht hu
    (Subgroup.mem_centralizer_singleton_iff.mp htK.1) hα (htK.2 _ hα) hαm (htK.2 _ hαm) hne

theorem pRank_two_le_one_of_forall_involution_eq {K : Subgroup G} {u : G} (hu : orderOf u = 2)
    (h : ∀ t ∈ K, orderOf t = 2 → t = u) : Open.pRank 2 K ≤ 1 := by
  apply CFSG.SectionRank.pRank_le (by decide)
  intro E hEK hE
  have hEu : E ≤ Subgroup.zpowers u := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · rw [h x (hEK hx) (orderOf_eq_prime (hE.2 x hx) hx1)]
      exact Subgroup.mem_zpowers u
  calc Nat.card E ≤ Nat.card (Subgroup.zpowers u) := Subgroup.card_le_of_le hEu
    _ = 2 ^ 1 := by rw [Nat.card_zpowers, hu, pow_one]

end CFSG.ProperTwoGeneratedCore.Assembly

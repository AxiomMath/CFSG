module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClassSurvive
public import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClassPoint

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

namespace RankOneClass

theorem mem_coreActionKernel_of_pRank_le_one' {R : Subgroup G}
    (hRq : IsQuasisimple (↥R ⧸ pPrimeCore 2 ↥R)) (hrank : CFSG.pRank 2 ↥R ≤ 1) {a : G}
    (haR : a ∈ R) (ha : orderOf a = 2) : a ∈ coreActionKernel R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq' : IsQuasisimple (↥R ⧸ CFSG.oddCore ↥R) := LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore_two ↥R)).symm hRq
  obtain ⟨-, z₀, -, huniq, hcen, -⟩ :=
    UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrank hq'
  have ha'2 : orderOf (⟨a, haR⟩ : R) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hmk2 : orderOf (QuotientGroup.mk ⟨a, haR⟩ : ↥R ⧸ CFSG.oddCore ↥R) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, ← ha'2, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h
      have hO : (⟨a, haR⟩ : R) ∈ CFSG.oddCore ↥R := (QuotientGroup.eq_one_iff _).mp h
      rw [oddCore_eq_pPrimeCore_two] at hO
      exact not_mem_pPrimeCore_two_of_orderOf ha'2 hO
  have hcentral : (QuotientGroup.mk ⟨a, haR⟩ : ↥R ⧸ CFSG.oddCore ↥R) ∈
      center (↥R ⧸ CFSG.oddCore ↥R) := by
    rw [huniq _ hmk2, hcen]
    exact mem_zpowers _
  refine ⟨le_normalizer haR, fun j hj => ?_⟩
  rw [FooteLit.mk_mem_center_iff] at hcentral
  have h1 := hcentral (⟨j, hj⟩ : R)⁻¹
  rw [oddCore_eq_pPrimeCore_two, mem_pPrimeCore_iff_mem_oddCoreIn] at h1
  have e : (((((⟨j, hj⟩ : R)⁻¹ * ⟨a, haR⟩)⁻¹ * (⟨a, haR⟩ * (⟨j, hj⟩ : R)⁻¹) : R)) : G) =
      a⁻¹ * j * a * j⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e] at h1
  have h3 := (mem_normalizer_iff.mp (mem_normalizer_oddCoreIn (le_normalizer (inv_mem hj))) _).mp
    h1
  rw [inv_inv] at h3
  rw [show j⁻¹ * a⁻¹ * j * a = j⁻¹ * (a⁻¹ * j * a * j⁻¹) * j by group]
  exact h3

end RankOneClass

theorem exists_twoComponent_centralizer_center_ne_bot {K : Subgroup G}
    (hK : IsSolomonMaximal K) (hrank : CFSG.pRank 2 ↥K ≤ 1) :
    ∃ t : G, orderOf t = 2 ∧ ∃ X : Subgroup G,
      IsTwoComponentIn X (centralizer ({t} : Set G)) ∧ SolomonEquiv K X ∧
        center (↥X ⧸ pPrimeCore 2 ↥X) ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T, hT, hT2, hTQ, hKT⟩ := hK.1
  have hKq := isQuasisimple_coreQuot_of_isSolomonMember hK.1
  obtain ⟨t, htT, ht, htc⟩ := RankOneClass.exists_central_involution hT hT2
  set Ct := centralizer ({t} : Set G) with hCt
  have hCTt : centralizer (T : Set G) ≤ Ct := centralizer_le (Set.singleton_subset_iff.mpr htT)
  have hTt : T ≤ Ct := fun s hs => mem_centralizer_singleton_iff.mpr (htc s hs)
  have hzt : centralizer ((zpowers t : Subgroup G) : Set G) = Ct := by
    rw [zpowers_eq_closure, centralizer_closure]
  obtain ⟨hRY, hLY, -, ⟨eR⟩⟩ :=
    cover_facts hKq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hT2 hTQ)
  set R := oddResidualIn (K ⊓ centralizer (T : Set G)) with hRdef
  have hRL : R ≤ twoLayerIn Ct := by
    have h1 := twoLayer_inf_centralizer_le_of_witness hKq hT2 hTQ hKT
    rw [hLY] at h1
    have h2 := GrSLit.pLayer_inf_centralizer_le_of_normalizes (Q := Ct) hT2
      (hTt.trans le_normalizer)
    rw [inf_eq_right.mpr hCTt] at h2
    exact h1.trans h2
  have hRq : IsQuasisimple (↥R ⧸ pPrimeCore 2 ↥R) :=
    isQuasisimple_quotient_of_isPComponent hRY.1 hRY.2
  have hRrank : CFSG.pRank 2 ↥R ≤ 1 := by
    rw [← pRank_quotient_pPrimeCore ↥R, pRank_eq_of_mulEquiv one_lt_two eR,
      pRank_quotient_pPrimeCore ↥K]
    exact hrank
  obtain ⟨z, hzR, hz⟩ := RankOneClass.exists_involution hRY
  have hzQ : z ∈ coreActionKernel R :=
    RankOneClass.mem_coreActionKernel_of_pRank_le_one' hRq hRrank hzR hz
  have hz2 : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hzQ' : zpowers z ≤ coreActionKernel R := (zpowers_le).mpr hzQ
  obtain ⟨hR₂Y, -, -, ⟨eR₂⟩⟩ :=
    cover_facts hRq inf_le_left (inf_centralizer_sup_oddCoreIn_eq hz2 hzQ')
  set R₂ := oddResidualIn (R ⊓ centralizer ((zpowers z : Subgroup G) : Set G)) with hR₂def
  have hR₂R : R₂ ≤ R := (Sol76.oddResidualIn_le _).trans inf_le_left
  have hR₂L : R₂ ≤ twoLayerIn Ct := hR₂R.trans hRL
  have hR₂perf : ⁅R₂, R₂⁆ = R₂ := UnbalancedCorr.commutator_eq_of_isPComponent hR₂Y.1 hR₂Y.2
  have hR₂res : oddResidualIn R₂ = R₂ := oddResidualIn_eq_self_of_isPComponent hR₂Y.1 hR₂Y.2
  have hR₂q : IsQuasisimple (↥R₂ ⧸ pPrimeCore 2 ↥R₂) :=
    isQuasisimple_quotient_of_isPComponent hR₂Y.1 hR₂Y.2
  have hzR₂ : z ∈ R₂ := mem_oddResidualIn
    (mem_inf.mpr ⟨hzR, mem_centralizer_iff.mpr fun g hg => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
      exact (Commute.zpow_left (Commute.refl z) n).eq⟩) ⟨1, by rw [hz, pow_one]⟩
  have hzc : ∀ j ∈ R₂, j * z = z * j := fun j hj => by
    have h1 := (mem_inf.mp (Sol76.oddResidualIn_le _ hj)).2
    exact (mem_centralizer_iff.mp h1 z (mem_zpowers z)).symm
  have ht2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hTzt : T ≤ normalizer ((zpowers t : Subgroup G) : Set G) := fun s hs =>
    centralizer_le_normalizer _ (by rw [hzt]; exact hTt hs)
  have hstart : twoLayerIn (K ⊓ Ct) ≤ twoLayerIn Ct := by
    have h1 := twoLayer_inf_centralizer_le_of_normalizes hKq ht2 hT2 ((zpowers_le).mpr htT)
      hTzt hTQ (twoLayer_inf_centralizer_le_of_witness hKq hT2 hTQ hKT)
    rwa [hzt] at h1
  have hTKt : T ≤ normalizer ((K ⊓ Ct : Subgroup G) : Set G) := by
    intro s hs
    have hsK : s ∈ normalizer (K : Set G) := (hTQ hs).1
    have hsC : s ∈ normalizer (Ct : Set G) := le_normalizer (hTt hs)
    rw [mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨hgK, hgC⟩ := mem_inf.mp hg
      exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hsK g).mp hgK, (mem_normalizer_iff.mp hsC g).mp hgC⟩
    · intro hg
      obtain ⟨hgK, hgC⟩ := mem_inf.mp hg
      exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hsK g).mpr hgK,
        (mem_normalizer_iff.mp hsC g).mpr hgC⟩
  have hRKt : R ≤ twoLayerIn (K ⊓ Ct) := by
    have h1 := GrSLit.pLayer_inf_centralizer_le_of_normalizes (Q := K ⊓ Ct) hT2 hTKt
    rw [inf_assoc, inf_eq_right.mpr hCTt] at h1
    rw [← hLY]
    exact h1
  have hmoved : ∀ X : Subgroup G, IsTwoComponentIn X Ct → ¬ R₂ ≤ coreActionKernel X →
      SolomonEquiv K X := by
    intro X hX hR₂X
    have hJX : ¬ twoLayerIn (K ⊓ Ct) ≤ coreActionKernel X := fun h =>
      hR₂X ((hR₂R.trans hRKt).trans h)
    have hlt : SolomonLt K X := by
      refine ⟨hK.1, isSolomonMember_of_isTwoComponentIn_centralizer ht hX, zpowers t, ht2,
        (zpowers_le).mpr (hTQ htT), ?_⟩
      rw [hzt]
      exact isTwoComponentIn_conjClosure_of_not_le hX hstart hJX
    exact hK.2 K X ⟨hK.1, Relation.ReflTransGen.refl⟩ hlt
  have hcard : ∀ X : Subgroup G, IsTwoComponentIn X Ct → ¬ R₂ ≤ coreActionKernel X →
      Nat.card (↥X ⧸ Open.fusionZStar ↥X) ≤ Nat.card (↥R₂ ⧸ Open.fusionZStar ↥R₂) := by
    intro X hX hR₂X
    obtain ⟨e1⟩ := nonempty_fusionZStar_equiv_of_reflTransGen (hmoved X hX hR₂X).2
    obtain ⟨e2⟩ := nonempty_fusionZStar_equiv_of_quotient_equiv (eR₂.trans eR)
    exact (Nat.card_congr (e1.symm.trans e2.symm).toEquiv).le
  obtain ⟨X, hX, hR₂X, hZX⟩ := RankOneClass.exists_center_ne_bot_of_moves hR₂L hR₂perf hR₂res
    hR₂q hzR₂ hz hzc hcard
  exact ⟨t, ht, X, hX, hmoved X hX hR₂X, hZX⟩

end CFSG.ComponentClassification.Sol76

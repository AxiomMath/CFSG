module

public import CFSG.LocalAnalysis.ComponentClassification.UGSChainTargetProduction

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Pointwise

theorem kProper_orbit_target_production_of_schreier {G : Type} [Group G] [Finite G]
    (hS : SchreierFor Blueprint.Catalog) (hK : Assembly.KProper Blueprint.Catalog G)
    {a : G} (ha : orderOf a = 2) {J : Subgroup G} (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {b : G} (hb : orderOf b = 2) (hbZ : b ∉ center G) (hab : a * b = b * a)
    (hbJ : b ∈ normalizer (J : Set G))
    (hJb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) :
    ∃ M : Subgroup G, M ≤ centralizer ({b} : Set G) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))) ∧
      gsFixedLayer J b ≤ M ⊔ conjugate M a ∧
      IsPComponent 2 ((gsFixedLayer J b).subgroupOf
        ((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G))) ∧
      (pPrimeCore 2 J).index ≤ (pPrimeCore 2 M).index ∧
      (M ≠ conjugate M a ∨ (pPrimeCore 2 J).index = (pPrimeCore 2 M).index →
        GSCorr a J b M) ∧
      (M = conjugate M a → (pPrimeCore 2 J).index = (pPrimeCore 2 M).index →
        GSIsoCorr a J b M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G) with hCa
  set Hb := centralizer ({b} : Set G) with hHb
  have hJaJ : conjugate J a = J := UnbalancedCorr.conjugate_eq_self_of_le_centralizer hJa
  have hKe : ∀ k ∈ J ⊔ conjugate J a, k⁻¹ * b⁻¹ * k * b ∈ (pPrimeCore 2 Ca).map Ca.subtype := by
    intro k hk
    rw [hJaJ, sup_idem] at hk
    exact UGSChain.map_pPrimeCore_le_of_isPComponent hJa hJ (hJb k hk)
  obtain ⟨-, -, -, -, hTab, hTpc, hTV, hVE, -, -, φ, -⟩ :=
    UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK (a := a)
      (b := a) (e := b) ha hb rfl hab hbZ hJa hJ hKe
  have hTE : gsFixedLayer J b ≤ (pLayer Hb 2).map Hb.subtype := hTV.trans hVE
  have hTHb : gsFixedLayer J b ≤ Hb := hTab.trans inf_le_right
  have haHb : a ∈ Hb := mem_centralizer_singleton_iff.mpr hab
  have ha' : orderOf (⟨a, haHb⟩ : Hb) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena : centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb) = (Ca ⊓ Hb).subgroupOf Hb := by
    ext y
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨congrArg Subtype.val h, y.2⟩, fun h => Subtype.ext h.1⟩
  have hT'C : (gsFixedLayer J b).subgroupOf Hb ≤ centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb) := by
    rw [hcena]
    intro y hy
    exact mem_subgroupOf.mpr (hTab (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 (((gsFixedLayer J b).subgroupOf Hb).subgroupOf
      (centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb))) := by
    rw [hcena, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact hTpc
  have hT'E : (gsFixedLayer J b).subgroupOf Hb ≤ pLayer Hb 2 := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := mem_map.mp (hTE (mem_subgroupOf.mp hy))
    rwa [← Subtype.ext hzy]
  obtain ⟨M', hM', hT'K, hT'Kpc⟩ := two_layer_fixed_component_orbit_location ha' hT'C hT'pc hT'E
  obtain ⟨M, hMHb, rfl⟩ : ∃ M : Subgroup G, M ≤ Hb ∧ M.subgroupOf Hb = M' :=
    ⟨M'.map Hb.subtype, map_subtype_le _, comap_map_eq_self_of_injective Hb.subtype_injective _⟩
  obtain ⟨hMaHb, -⟩ := UGSChain.conjugate_isPComponent_centralizer hab hMHb hM'
  have hconj : conjugate (M.subgroupOf Hb) ⟨a, haHb⟩ = (conjugate M a).subgroupOf Hb :=
    conjugate_subgroupOf_eq M Hb ⟨a, haHb⟩
  have hK'eq : M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩ =
      (M ⊔ conjugate M a).subgroupOf Hb := by
    rw [hconj, subgroupOf_sup hMHb hMaHb]
  have hKHb : M ⊔ conjugate M a ≤ Hb := sup_le hMHb hMaHb
  have hCeq : (M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩) ⊓
      centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb) = ((M ⊔ conjugate M a) ⊓ Ca).subgroupOf Hb := by
    rw [hK'eq, hcena]
    ext y
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, y.2⟩⟩
  have hTK : gsFixedLayer J b ≤ M ⊔ conjugate M a := by
    intro t ht
    have h1 := hT'K (show (⟨t, hTHb ht⟩ : Hb) ∈ (gsFixedLayer J b).subgroupOf Hb from ht)
    rw [hK'eq] at h1
    exact h1
  have hTKpc : IsPComponent 2 ((gsFixedLayer J b).subgroupOf
      ((M ⊔ conjugate M a) ⊓ Ca)) := by
    rw [hCeq, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left.trans hKHb) 2 Nat.prime_two] at hT'Kpc
    exact hT'Kpc
  obtain ⟨hle, hswap, heqc⟩ := involution_orbit_fixed_component_quotient_comparison ha'
    (M.subgroupOf Hb) hM' _ rfl _ rfl _ (le_inf hT'K hT'C) hT'Kpc
  have hidxT : (pPrimeCore 2 ((gsFixedLayer J b).subgroupOf Hb)).index =
      (pPrimeCore 2 J).index := by
    rw [index_eq_card, index_eq_card,
      UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr (subgroupOfEquivOfLe hTHb)]
    exact Nat.card_congr φ.toEquiv
  have hidxM : (pPrimeCore 2 (M.subgroupOf Hb)).index = (pPrimeCore 2 M).index := by
    rw [index_eq_card, index_eq_card,
      UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr (subgroupOfEquivOfLe hMHb)]
  rw [hidxT, hidxM] at hle heqc
  have hfix : (pLayer ↥((M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩) ⊓
        centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb)) 2).map
        ((M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩) ⊓
          centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb)).subtype =
        (gsFixedLayer J b).subgroupOf Hb →
      gsFixedLayer J b = gsFixedLayer (M ⊔ conjugate M a) a := by
    intro h
    have h1 := UnbalancingLocal.Correspondence.gsFixedLayer_subgroupOf hKHb haHb
    rw [← hK'eq] at h1
    apply UGSChain.eq_of_subgroupOf_eq hTHb
      ((gsFixedLayer_le_inf _ a).trans (inf_le_left.trans hKHb))
    rw [h1]
    exact h.symm
  have hcorr : gsFixedLayer J b = gsFixedLayer (M ⊔ conjugate M a) a → GSCorr a J b M :=
    fun h => ⟨ha, hb, hab, hJa, hJ, hMHb, hM', hbJ, hJb, h⟩
  have hstable : M = conjugate M a → M.subgroupOf Hb = conjugate (M.subgroupOf Hb) ⟨a, haHb⟩ :=
    fun h => by rw [hconj, ← h]
  refine ⟨M, hMHb, hM', hTK, hTKpc, hle, fun hcase => hcorr (hfix ?_), fun hMa hidx => ?_⟩
  · rcases hcase with hne | hidx
    · refine hswap fun h => hne ?_
      exact UGSChain.eq_of_subgroupOf_eq hMHb hMaHb (h.trans hconj)
    · exact (heqc hidx).1
  · obtain ⟨hlay, hcov⟩ := heqc hidx
    have hcov' := congrArg (map Hb.subtype) (hcov (hstable hMa))
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hTHb, pPrimeCore_map_subgroupOf 2 M Hb hMHb,
      map_subgroupOf_eq_of_le hMHb] at hcov'
    have hTM : gsFixedLayer J b ≤ M := le_sup_left.trans hcov'.le
    refine ⟨hcorr (hfix hlay), by rw [← hMa, sup_idem], ?_⟩
    rw [← coe_sup_primeCore_eq_mul hTM, hcov']

end CFSG.ComponentClassification.FooteLit

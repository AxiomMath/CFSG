module

public import CFSG.LocalAnalysis.ComponentClassification.UGSChainTargetProduction

public section

namespace CFSG.ComponentClassification.UGSChain

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedGS

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_mk_eq_subgroupOf {a : G} {X : Subgroup G} (haX : a ∈ X) :
    centralizer ({(⟨a, haX⟩ : X)} : Set X) = (centralizer ({a} : Set G) ⊓ X).subgroupOf X := by
  ext y
  rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨congrArg Subtype.val h, y.2⟩, fun h => Subtype.ext h.1⟩

theorem map_pLayer_le_normalizer {X A : Subgroup G} (hAX : A ≤ X)
    (hA : IsPComponent 2 (A.subgroupOf X)) :
    (pLayer X 2).map X.subtype ≤ normalizer (A : Set G) := by
  have hEN : pLayer X 2 ≤ normalizer ((A.subgroupOf X : Subgroup X) : Set X) := by
    apply sSup_le
    intro B hB
    by_cases hAB : A.subgroupOf X = B
    · rw [← hAB]
      exact le_normalizer
    · exact ((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ B hA
        hB).2 hAB).1
  rintro y ⟨y', hy', rfl⟩
  exact mem_normalizer_of_subgroupOf hAX (hEN hy')

theorem map_mk_eq_of_sup_pPrimeCore {b : G} {X T : Subgroup G}
    (hXb : X ≤ centralizer ({b} : Set G))
    (hX : IsPComponent 2 (X.subgroupOf (centralizer ({b} : Set G))))
    (hsup : T ⊔ (pPrimeCore 2 X).map X.subtype = X) :
    (X.subgroupOf (centralizer ({b} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({b} : Set G)))) =
      (T.subgroupOf (centralizer ({b} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({b} : Set G)))) := by
  set Hb := centralizer ({b} : Set G) with hHb
  have hTX : T ≤ X := le_sup_left.trans hsup.le
  have hOX : (pPrimeCore 2 X).map X.subtype ≤ X := map_subtype_le _
  have hcore := map_pPrimeCore_le_of_isPComponent hXb hX
  have hbot : (((pPrimeCore 2 X).map X.subtype).subgroupOf Hb).map
      (QuotientGroup.mk' (pPrimeCore 2 Hb)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro y hy
    obtain ⟨z, hz, hzy⟩ := mem_map.mp (hcore (mem_subgroupOf.mp hy))
    rwa [← Subtype.ext hzy]
  conv_lhs => rw [← hsup]
  rw [subgroupOf_sup (hTX.trans hXb) (hOX.trans hXb), Subgroup.map_sup, hbot, sup_bot_eq]

theorem exists_orbit_component_of_le_pLayer {a b : G} (ha : orderOf a = 2)
    (hab : a * b = b * a) {T : Subgroup G}
    (hT : T ≤ centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G))
    (hTpc : IsPComponent 2
      (T.subgroupOf (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G))))
    (hTE : T ≤ (pLayer (centralizer ({b} : Set G)) 2).map (centralizer ({b} : Set G)).subtype) :
    ∃ M : Subgroup G, M ≤ centralizer ({b} : Set G) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))) ∧ T ≤ M ⊔ conjugate M a ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G) with hCa
  set Hb := centralizer ({b} : Set G) with hHb
  have hTHb : T ≤ Hb := hT.trans inf_le_right
  have haHb : a ∈ Hb := mem_centralizer_singleton_iff.mpr hab
  have ha' : orderOf (⟨a, haHb⟩ : Hb) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena := centralizer_mk_eq_subgroupOf haHb
  have hT'C : T.subgroupOf Hb ≤ centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb) := by
    rw [hcena]
    intro y hy
    exact mem_subgroupOf.mpr (hT (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 ((T.subgroupOf Hb).subgroupOf
      (centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb))) := by
    rw [hcena, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact hTpc
  have hT'E : T.subgroupOf Hb ≤ pLayer Hb 2 := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := mem_map.mp (hTE (mem_subgroupOf.mp hy))
    rwa [← Subtype.ext hzy]
  obtain ⟨M', hM', hT'K, hT'Kpc⟩ := two_layer_fixed_component_orbit_location ha' hT'C hT'pc hT'E
  obtain ⟨M, hMHb, rfl⟩ : ∃ M : Subgroup G, M ≤ Hb ∧ M.subgroupOf Hb = M' :=
    ⟨M'.map Hb.subtype, map_subtype_le _, comap_map_eq_self_of_injective Hb.subtype_injective _⟩
  obtain ⟨hMaHb, -⟩ := conjugate_isPComponent_centralizer hab hMHb hM'
  have hK'eq : M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩ =
      (M ⊔ conjugate M a).subgroupOf Hb := by
    rw [conjugate_subgroupOf_eq M Hb ⟨a, haHb⟩, subgroupOf_sup hMHb hMaHb]
  have hKHb : M ⊔ conjugate M a ≤ Hb := sup_le hMHb hMaHb
  have hCeq : (M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩) ⊓
      centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb) = ((M ⊔ conjugate M a) ⊓ Ca).subgroupOf Hb := by
    rw [hK'eq, hcena]
    ext y
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, y.2⟩⟩
  refine ⟨M, hMHb, hM', fun t ht => ?_, ?_⟩
  · have h1 := hT'K (show (⟨t, hTHb ht⟩ : Hb) ∈ T.subgroupOf Hb from ht)
    rw [hK'eq] at h1
    exact h1
  · rw [hCeq, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left.trans hKHb) 2 Nat.prime_two] at hT'Kpc
    exact hT'Kpc

theorem orbit_fixed_component_comparison {a b : G} (ha : orderOf a = 2) (hab : a * b = b * a)
    {M : Subgroup G} (hMHb : M ≤ centralizer ({b} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G)))) {T : Subgroup G}
    (hTK : T ≤ (M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G))
    (hTpc : IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G)))) :
    (pPrimeCore 2 T).index ≤ (pPrimeCore 2 M).index ∧
      (M ≠ conjugate M a → gsFixedLayer (M ⊔ conjugate M a) a = T) ∧
      ((pPrimeCore 2 T).index = (pPrimeCore 2 M).index →
        gsFixedLayer (M ⊔ conjugate M a) a = T ∧
          (M = conjugate M a → T ⊔ (pPrimeCore 2 M).map M.subtype = M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G) with hCa
  set Hb := centralizer ({b} : Set G) with hHb
  have haHb : a ∈ Hb := mem_centralizer_singleton_iff.mpr hab
  have ha' : orderOf (⟨a, haHb⟩ : Hb) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena := centralizer_mk_eq_subgroupOf haHb
  obtain ⟨hMaHb, -⟩ := conjugate_isPComponent_centralizer hab hMHb hM
  have hKHb : M ⊔ conjugate M a ≤ Hb := sup_le hMHb hMaHb
  have hTHb : T ≤ Hb := hTK.trans (inf_le_left.trans hKHb)
  have hconj : conjugate (M.subgroupOf Hb) ⟨a, haHb⟩ = (conjugate M a).subgroupOf Hb :=
    conjugate_subgroupOf_eq M Hb ⟨a, haHb⟩
  have hK'eq : M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩ =
      (M ⊔ conjugate M a).subgroupOf Hb := by
    rw [hconj, subgroupOf_sup hMHb hMaHb]
  have hCeq : (M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩) ⊓
      centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb) = ((M ⊔ conjugate M a) ⊓ Ca).subgroupOf Hb := by
    rw [hK'eq, hcena]
    ext y
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, y.2⟩⟩
  have hT'C : T.subgroupOf Hb ≤ (M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩) ⊓
      centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb) := by
    rw [hCeq]
    intro y hy
    exact mem_subgroupOf.mpr (hTK (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 ((T.subgroupOf Hb).subgroupOf
      ((M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩) ⊓
        centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb))) := by
    rw [hCeq, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left.trans hKHb) 2 Nat.prime_two]
    exact hTpc
  obtain ⟨hle, hswap, heqc⟩ := involution_orbit_fixed_component_quotient_comparison ha'
    (M.subgroupOf Hb) hM _ rfl _ rfl _ hT'C hT'pc
  have hidxT : (pPrimeCore 2 (T.subgroupOf Hb)).index = (pPrimeCore 2 T).index := by
    rw [index_eq_card, index_eq_card,
      UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr (subgroupOfEquivOfLe hTHb)]
  have hidxM : (pPrimeCore 2 (M.subgroupOf Hb)).index = (pPrimeCore 2 M).index := by
    rw [index_eq_card, index_eq_card,
      UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr (subgroupOfEquivOfLe hMHb)]
  rw [hidxT, hidxM] at hle heqc
  have hfix : (pLayer ↥((M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩) ⊓
        centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb)) 2).map
        ((M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩) ⊓
          centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb)).subtype = T.subgroupOf Hb →
      gsFixedLayer (M ⊔ conjugate M a) a = T := by
    intro h
    have h1 := UnbalancingLocal.Correspondence.gsFixedLayer_subgroupOf hKHb haHb
    rw [← hK'eq] at h1
    apply eq_of_subgroupOf_eq ((gsFixedLayer_le_inf _ a).trans (inf_le_left.trans hKHb)) hTHb
    rw [h1]
    exact h
  refine ⟨hle, fun hne => hfix (hswap fun h => hne ?_), fun hidx => ?_⟩
  · exact eq_of_subgroupOf_eq hMHb hMaHb (h.trans hconj)
  · obtain ⟨hlay, hcov⟩ := heqc hidx
    refine ⟨hfix hlay, fun hMa => ?_⟩
    have hcov' := congrArg (map Hb.subtype) (hcov (by rw [hconj, ← hMa]))
    rwa [Subgroup.map_sup, map_subgroupOf_eq_of_le hTHb, pPrimeCore_map_subgroupOf 2 M Hb hMHb,
      map_subgroupOf_eq_of_le hMHb] at hcov'

end CFSG.ComponentClassification.UGSChain

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKFixed

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedGS CFSG.ComponentClassification.UGSChain
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace HeK

variable {G : Type} [Group G] [Finite G]

theorem exists_pump (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {a b : G} (ha : orderOf a = 2)
    (hab : a * b = b * a) (hbtop : centralizer ({b} : Set G) ≠ ⊤) {T : Subgroup G}
    (hTab : T ≤ centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G))
    (hTpc : IsPComponent 2 (T.subgroupOf
      (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)))) :
    ∃ M : Subgroup G, M ≤ centralizer ({b} : Set G) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))) ∧
      T ≤ (M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G) ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G))) ∧
      (pPrimeCore 2 T).index ≤ (pPrimeCore 2 M).index ∧
      (M ≠ conjugate M a → gsFixedLayer (M ⊔ conjugate M a) a = T) ∧
      ((pPrimeCore 2 T).index = (pPrimeCore 2 M).index → M = conjugate M a →
        T ⊔ (pPrimeCore 2 M).map M.subtype = M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G) with hCa
  set Hb := centralizer ({b} : Set G) with hHb
  have haHb : a ∈ Hb := mem_centralizer_singleton_iff.mpr hab
  have ha' : orderOf (⟨a, haHb⟩ : Hb) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena : centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb) = (Ca ⊓ Hb).subgroupOf Hb := by
    ext y
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨congrArg Subtype.val h, y.2⟩, fun h => Subtype.ext h.1⟩
  have hTHb : T ≤ Hb := hTab.trans inf_le_right
  have hT'C : T.subgroupOf Hb ≤ centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb) := by
    rw [hcena]
    intro y hy
    exact mem_subgroupOf.mpr (hTab (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 ((T.subgroupOf Hb).subgroupOf
      (centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb))) := by
    rw [hcena, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact hTpc
  have hKHb : SectionRank.IsKGroupCat ↥Hb :=
    UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
      (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hK Hb hbtop
  have hT'E : T.subgroupOf Hb ≤ pLayer Hb 2 :=
    (kGroup_involution_fixed_two_layer_containment_of_schreier hS hKHb ha').1 _ hT'C hT'pc
  obtain ⟨M', hM', hT'K, hT'Kpc⟩ := two_layer_fixed_component_orbit_location ha' hT'C hT'pc hT'E
  obtain ⟨M, hMHb, rfl⟩ : ∃ M : Subgroup G, M ≤ Hb ∧ M.subgroupOf Hb = M' :=
    ⟨M'.map Hb.subtype, map_subtype_le _, comap_map_eq_self_of_injective Hb.subtype_injective _⟩
  obtain ⟨hMaHb, -⟩ := conjugate_isPComponent_centralizer hab hMHb hM'
  have hconj : conjugate (M.subgroupOf Hb) ⟨a, haHb⟩ = (conjugate M a).subgroupOf Hb :=
    conjugate_subgroupOf_eq M Hb ⟨a, haHb⟩
  have hK'eq : M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩ =
      (M ⊔ conjugate M a).subgroupOf Hb := by
    rw [hconj, subgroupOf_sup hMHb hMaHb]
  have hKHb' : M ⊔ conjugate M a ≤ Hb := sup_le hMHb hMaHb
  have hCeq : (M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩) ⊓
      centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb) = ((M ⊔ conjugate M a) ⊓ Ca).subgroupOf Hb := by
    rw [hK'eq, hcena]
    ext y
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, y.2⟩⟩
  have hTK : T ≤ M ⊔ conjugate M a := by
    intro t ht
    have h1 := hT'K (show (⟨t, hTHb ht⟩ : Hb) ∈ T.subgroupOf Hb from ht)
    rw [hK'eq] at h1
    exact h1
  have hTKpc : IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M a) ⊓ Ca)) := by
    rw [hCeq, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left.trans hKHb') 2 Nat.prime_two] at hT'Kpc
    exact hT'Kpc
  have hTKC : T ≤ (M ⊔ conjugate M a) ⊓ Ca := le_inf hTK (hTab.trans inf_le_left)
  obtain ⟨hle, hswap, heq⟩ := orbit_fixed_component_comparison ha hab hMHb hM' hTKC hTKpc
  exact ⟨M, hMHb, hM', hTKC, hTKpc, hle, hswap, fun h hMa => (heq h).2 hMa⟩

theorem index_eq_of_mem (hD : L34RankTwoCentralFixedInput)
    (hK : Assembly.KProper Blueprint.Catalog G) {a b : G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hbtop : centralizer ({b} : Set G) ≠ ⊤) {M T : Subgroup G}
    (hMb : M ≤ centralizer ({b} : Set G))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (hMa : conjugate M a = M) (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hle : (pPrimeCore 2 T).index ≤ (pPrimeCore 2 M).index) (hbT : b ∈ T)
    (htype : IsL34Type (T ⧸ Open.fusionZStar T)) {z₁ z₂ : G}
    (hz₁ : z₁ ∈ (Open.fusionZStar T).map T.subtype)
    (hz₂ : z₂ ∈ (Open.fusionZStar T).map T.subtype) (hs₁ : z₁ * z₁ = 1) (hs₂ : z₂ * z₂ = 1)
    (hn₁ : z₁ ≠ 1) (hn₂ : z₂ ≠ 1) (hne : z₁ ≠ z₂) (hc : z₁ * z₂ = z₂ * z₁) :
    (pPrimeCore 2 T).index = (pPrimeCore 2 M).index := by
  by_contra hne'
  exact false_of_proper_fixed_l34 hD hK ha hbtop hMb hMp hMa hTM hTp (lt_of_le_of_ne hle hne')
    htype hz₁ hz₂ hs₁ hs₂ hn₁ hn₂ hne hc hbT hb

end HeK

end CFSG.ComponentClassification.GrSLit

module

public import CFSG.Foundations.GilmanSolomonGrammar

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def gsFixedLayer (N : Subgroup G) (t : G) : Subgroup G :=
  (pLayer ↥(N ⊓ centralizer ({t} : Set G)) 2).map (N ⊓ centralizer ({t} : Set G)).subtype

@[expose] def GSCorr (a : G) (J : Subgroup G) (b : G) (L : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.Corr (fun J K => IsPComponent 2 (J.subgroupOf K))
    (fun X => (pPrimeCore 2 X).map X.subtype) gsFixedLayer a J b L

@[expose] def GSIsoCorr (a : G) (J : Subgroup G) (b : G) (L : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.IsoCorr GSCorr (fun X => (pPrimeCore 2 X).map X.subtype) gsFixedLayer
    a J b L

theorem gsCorr_iff_grammar {a b : G} {J L : Subgroup G} :
    GSCorr a J b L ↔ GSGrammar.Corr (fun J K => IsPComponent 2 (J.subgroupOf K))
      (fun X => (pPrimeCore 2 X).map X.subtype) gsFixedLayer a J b L :=
  Iff.rfl

theorem gsIsoCorr_iff_grammar {a b : G} {J L : Subgroup G} :
    GSIsoCorr a J b L ↔ GSGrammar.IsoCorr GSCorr (fun X => (pPrimeCore 2 X).map X.subtype)
      gsFixedLayer a J b L :=
  Iff.rfl

theorem gsFixedLayer_le_inf (N : Subgroup G) (t : G) :
    gsFixedLayer N t ≤ N ⊓ centralizer ({t} : Set G) :=
  map_subtype_le _

theorem GSCorr.gsFixedLayer_le {a b : G} {J L : Subgroup G} (h : GSCorr a J b L)
    (hK : L ⊔ conjugate L a = L) : gsFixedLayer J b ≤ L :=
  GSGrammar.Corr.layer_le (fun N t => (gsFixedLayer_le_inf N t).trans inf_le_left)
    (gsCorr_iff_grammar.1 h) hK

theorem coe_sup_primeCore_eq_mul {A L : Subgroup G} (hA : A ≤ L) :
    ((A ⊔ (pPrimeCore 2 L).map L.subtype : Subgroup G) : Set G) =
      (A : Set G) * ((pPrimeCore 2 L).map L.subtype : Set G) :=
  GSGrammar.coe_sup_eq_mul hA <| by
    have hnormal : (((pPrimeCore 2 L).map L.subtype).subgroupOf L).Normal := by
      rw [← comap_subtype, comap_map_eq_self_of_injective L.subtype_injective]
      infer_instance
    exact le_normalizer_of_normal_subgroupOf (map_subtype_le _)

theorem gsIsoCorr_iff_sup {a b : G} {J L : Subgroup G} :
    GSIsoCorr a J b L ↔ GSCorr a J b L ∧ L ⊔ conjugate L a = L ∧
      gsFixedLayer J b ⊔ (pPrimeCore 2 L).map L.subtype = L :=
  gsIsoCorr_iff_grammar.trans <| GSGrammar.isoCorr_iff_sup (fun h hK => h.gsFixedLayer_le hK) <| by
    have hnormal : (((pPrimeCore 2 L).map L.subtype).subgroupOf L).Normal := by
      rw [← comap_subtype, comap_map_eq_self_of_injective L.subtype_injective]
      infer_instance
    exact le_normalizer_of_normal_subgroupOf (map_subtype_le _)

theorem sup_primeCore_eq_iff_map_eq_top {A L : Subgroup G} (hA : A ≤ L) :
    A ⊔ (pPrimeCore 2 L).map L.subtype = L ↔
      (A.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 L)) = ⊤ := by
  rw [← (comap_injective (QuotientGroup.mk'_surjective (pPrimeCore 2 L))).eq_iff, comap_map_eq,
    comap_top, QuotientGroup.ker_mk', ← (map_injective L.subtype_injective).eq_iff,
    Subgroup.map_sup, map_subgroupOf_eq_of_le hA, ← MonoidHom.range_eq_map, range_subtype]

theorem gsIsoCorr_iff_map_eq_top {a b : G} {J L : Subgroup G} :
    GSIsoCorr a J b L ↔ GSCorr a J b L ∧ L ⊔ conjugate L a = L ∧ gsFixedLayer J b ≤ L ∧
      ((gsFixedLayer J b).subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 L)) = ⊤ := by
  rw [gsIsoCorr_iff_sup]
  constructor
  · rintro ⟨h, hK, hsup⟩
    exact ⟨h, hK, h.gsFixedLayer_le hK,
      (sup_primeCore_eq_iff_map_eq_top (h.gsFixedLayer_le hK)).mp hsup⟩
  · rintro ⟨h, hK, hle, htop⟩
    exact ⟨h, hK, (sup_primeCore_eq_iff_map_eq_top hle).mpr htop⟩

end CFSG.ComponentClassification.UnbalancedGS

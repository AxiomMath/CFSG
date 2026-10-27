module

public import CFSG.Dihedral.CyclingNormalizerBridge
public import CFSG.Dihedral.OriginalCyclingOddCore
public import CFSG.Dihedral.OriginalOvergroupQuotients
import all CFSG.Dihedral.BlueprintDefs
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hasNormalIndexTwo_iff_exists (H : Subgroup G) :
    HasNormalIndexTwo H ↔ ∃ L : Subgroup H, L.Normal ∧ L.index = 2 := by
  constructor
  · rintro ⟨K, _, hn, hi⟩
    exact ⟨K.subgroupOf H, hn, hi⟩
  · rintro ⟨L, hn, hi⟩
    have hLH : L.map H.subtype ≤ H := Subgroup.map_subtype_le _
    have heq : (L.map H.subtype).subgroupOf H = L := by
      exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective L
    refine ⟨L.map H.subtype, hLH, ?_, ?_⟩
    · rw [heq]
      exact hn
    · rw [heq]
      exact hi

namespace OriginalData

variable (d : OriginalData G)

theorem sylow_isSylowIn_overgroup (H : Subgroup G)
    (hSH : (d.S : Subgroup G) ≤ H) : IsSylowIn 2 (d.S : Subgroup G) H := by
  exact ⟨hSH, d.S.isPGroup', fun _ _ hQ hSQ => d.S.is_maximal' hQ hSQ⟩

theorem has_dihedral_sylow_overgroup (H : Subgroup G)
    (hSH : (d.S : Subgroup G) ≤ H) : HasDihedralSylowTwo H := by
  obtain ⟨T, hT⟩ := (isSylowIn_iff_exists_sylow 2 (d.S : Subgroup G) H).mp
    (d.sylow_isSylowIn_overgroup H hSH)
  have eT : (T : Subgroup H) ≃* (d.S : Subgroup G) :=
    (Subgroup.equivMapOfInjective (T : Subgroup H) H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hT)
  obtain ⟨eS⟩ := d.sylow_mulEquiv_dihedral
  intro U
  exact ⟨d.n - 1, by have := d.three_le; omega,
    ⟨(Sylow.equiv U T).trans (eT.trans eS)⟩⟩

theorem cycles_of_no_indexTwo (H V : Subgroup G)
    (hSH : (d.S : Subgroup G) ≤ H) (hV : IsKleinFour V)
    (hVS : V ≤ (d.S : Subgroup G)) (hno : ¬ HasNormalIndexTwo H) : Cycles H V := by
  obtain ⟨T, hT⟩ := (isSylowIn_iff_exists_sylow 2 (d.S : Subgroup G) H).mp
    (d.sylow_isSylowIn_overgroup H hSH)
  have hVT : V.subgroupOf H ≤ (T : Subgroup H) := by
    intro v hv
    have hm : (v : G) ∈ (d.S : Subgroup G) := hVS hv
    rw [← hT] at hm
    obtain ⟨w, hw, hweq⟩ := Subgroup.mem_map.mp hm
    exact (Subtype.ext hweq : w = v) ▸ hw
  have hno' : ¬ ∃ L : Subgroup H, L.Normal ∧ L.index = 2 :=
    fun h => hno ((hasNormalIndexTwo_iff_exists H).mpr h)
  have hc := (case1_no_index_two_fusion_and_normalizer
    (d.has_dihedral_sylow_overgroup H hSH) hno').2 T (V.subgroupOf H) hVT
      (isKleinFour_subgroupOf (hVS.trans hSH) hV)
  exact (cycles_iff_normalizerContainsCPrime H V (hVS.trans hSH) hV).mpr hc

theorem indexTwo_of_not_cycles (H : Subgroup G)
    (hSH : (d.S : Subgroup G) ≤ H) (j : Fin 2) (hj : ¬ Cycles H (d.V j)) :
    HasNormalIndexTwo H := by
  by_contra hno
  exact hj (d.cycles_of_no_indexTwo H (d.V j) hSH
    (d.V_isKleinFour_general j) (d.V_le_sylow j) hno)

theorem cycling_quotient_alternatives (d : OriginalData G)
    (H V : Subgroup G) (hH : H ≠ ⊤)
    (hVH : V ≤ H) (hV : IsKleinFour V) (hc : Cycles H V) :
    HasCoordinates H ∨ HasAlternatingQuotient H := by
  rcases d.proper_quotients H hH with hcoord | halt | htwo
  · exact Or.inl hcoord
  · exact Or.inr halt
  · exact (not_sylowTwoQuotient_of_cycles H V hVH hV hc htwo).elim

theorem one_cycle_coordinates_and_indexTwo (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (d.S : Subgroup G) ≤ H) (i j : Fin 2)
    (hi : Cycles H (d.V i)) (hj : ¬ Cycles H (d.V j)) :
    HasCoordinates H ∧ HasNormalIndexTwo H := by
  have hindex := d.indexTwo_of_not_cycles H hSH j hj
  refine ⟨?_, hindex⟩
  rcases d.cycling_quotient_alternatives H (d.V i) hH
      ((d.V_le_sylow i).trans hSH) (d.V_isKleinFour_general i) hi with hcoord | halt
  · exact hcoord
  · exact (not_alternatingQuotient_of_normalIndexTwo H hindex halt).elim

theorem both_cycles_quotient_and_indexTwo [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (d.S : Subgroup G) ≤ H)
    (h0 : Cycles H (d.V 0)) (h1 : Cycles H (d.V 1)) :
    oddCoreOf H ≤ Subgroup.centralizer (d.S : Set G) ∧
      (HasCoordinates H ∨ HasAlternatingQuotient H) ∧ ¬ HasNormalIndexTwo H := by
  exact ⟨d.both_cycles_oddCore_centralizes_sylow hnonab H hSH h0 h1,
    d.cycling_quotient_alternatives H (d.V 0) hH
      ((d.V_le_sylow 0).trans hSH) (d.V_isKleinFour_general 0) h0,
    d.no_indexTwo_of_both_cycles H hSH h0 h1⟩

end OriginalData

end CFSG.DihedralBlueprint

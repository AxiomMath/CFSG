module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.TightEmbedding
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.ComponentStepData
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.ComponentConj

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup

theorem Case3Core.exists_component_ge (hI31 : CFSG.ASVolI.I_3_1) {G : Type} [Group G] [Finite G]
    {z : G} {K : Subgroup G} (h : Case3Core G z K)
    (hX : CFSG.SectionRank.IsKGroupCat ↥(centralizer ({z} : Set G)))
    (hO : CFSG.oddCore ↥(centralizer ({z} : Set G)) = ⊥) :
    ∃ E : Subgroup G, K ≤ E ∧ E ≤ centralizer ({z} : Set G) ∧ CFSG.IsQuasisimple ↥E ∧
      (E.subgroupOf (centralizer ({z} : Set G))).IsSubnormal := by
  let X : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let L : Subgroup ↥X := K.subgroupOf X
  obtain ⟨u, hu, hu4, _hu2, hu_comm⟩ := h.exists_generator
  have huK : u ∈ K := by
    have hmem := hu
    rw [CFSG.Open.pCoreOf] at hmem
    obtain ⟨x, _hx, hx⟩ := Subgroup.mem_map.mp hmem
    rw [← hx]
    exact x.2
  have huX : u ∈ X := h.le_centralizer huK
  let u' : ↥X := ⟨u, huX⟩
  have hcomm : ∀ k ∈ K, k * (u' : G) = (u' : G) * k := by
    intro k hk
    simpa [u'] using hu_comm k hk
  have htight : Subgroup.centralizer ({(u' : G)} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    simpa [u'] using h.tight u hu hu4
  obtain ⟨hP, hL⟩ := h.isTwoComponentIn_centralizer u' huK hu4 hcomm htight
  obtain ⟨K₁, hK₁_1, hK₁_2, _hK₁_3⟩ :=
    hI31 ↥X (show CFSG.SectionRank.IsKGroupCat ↥X from hX) (Subgroup.zpowers u') hP L hL
  have hO' : CFSG.oddCore ↥X = ⊥ := hO
  have hLodd : L ≤ Subgroup.centralizer (CFSG.oddCore ↥X : Set ↥X) := by
    rw [hO']
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := by simpa using hy
    rw [hy1]
    simp
  have hK₁ : CFSG.ASVolI.ChIJK.IsComponentIn K₁ ⊤ := (hK₁_2 hLodd).2
  have hLle : L ≤ CFSG.ASVolI.ChIJK.conjClosure L (CFSG.ASVolI.ChIJK.oddCoreE ↥X) := by
    unfold CFSG.ASVolI.ChIJK.conjClosure
    refine le_iSup₂_of_le (1 : ↥X) (Subgroup.one_mem (CFSG.ASVolI.ChIJK.oddCoreE ↥X)) ?_
    have hconj : CFSG.conjugate L (1 : ↥X) = L := by
      unfold CFSG.conjugate
      rw [inv_one]
      have hf : (MulAut.conj (1 : ↥X)).toMonoidHom = MonoidHom.id ↥X := by
        ext x
        simp
      rw [hf, Subgroup.map_id]
    exact hconj.ge
  have hLle' : L ≤ CFSG.ASVolI.ChIJK.conjClosure K₁ (Subgroup.zpowers u') :=
    hLle.trans (le_of_eq hK₁_1.2)
  have hu'L : u' ∈ L := by
    rw [Subgroup.mem_subgroupOf]
    exact huK
  have hLK₁ : L ≤ K₁ := le_of_le_conjClosure_zpowers hK₁ hu'L hLle'
  refine ⟨K₁.map X.subtype, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [Subgroup.mem_map]
    exact ⟨⟨k, h.le_centralizer hk⟩, hLK₁ (by rw [Subgroup.mem_subgroupOf]; exact hk), rfl⟩
  · exact Subgroup.map_subtype_le K₁
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (K₁.equivMapOfInjective X.subtype X.subtype_injective) hK₁.2.1
  · have hEsub : (K₁.map X.subtype).subgroupOf X = K₁ :=
      Subgroup.map_injective X.subtype_injective
        (Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le K₁))
    rw [hEsub]
    have hsur : Function.Surjective (⊤ : Subgroup ↥X).subtype :=
      fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
    have hsn := (hK₁.2.2).map (f := (⊤ : Subgroup ↥X).subtype) hsur
    rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : K₁ ≤ ⊤)] at hsn

end CFSG.OddStandard.HigherRank.G2Three

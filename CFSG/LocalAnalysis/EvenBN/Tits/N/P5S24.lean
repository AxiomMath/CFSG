module

public import CFSG.Open.FusionDefs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Gen
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N

theorem exists_mem_normalizer_not_mem_of_isPGroup_two {G : Type*} [Group G] [Finite G] {S P : Subgroup G}
    (hP : IsPGroup 2 P) (hSP : S ≤ P) (hne : S ≠ P) :
    ∃ n ∈ P, n ∈ normalizer (S : Set G) ∧ n ∉ S := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : S.subgroupOf P < ⊤ :=
    lt_top_iff_ne_top.2 fun h => hne (le_antisymm hSP (subgroupOf_eq_top.1 h))
  have hlt' := Group.normalizerCondition_of_isNilpotent _ hlt
  rw [← subgroupOf_normalizer_eq hSP] at hlt'
  obtain ⟨x, hx, hxS⟩ := IsConcreteLE.exists_of_lt hlt'
  exact ⟨x, x.2, mem_subgroupOf.1 hx, fun h => hxS (mem_subgroupOf.2 h)⟩

theorem actFun_mem_normalizer_of_maxElemAbelian2_eq_singleton {G : Type*} [Group G]
    (V : Subgroup G) {W : Subgroup (MulAut ↥V)} (hWab : IsElemAbelian 2 W) {S : Subgroup G}
    (hmax : maxElemAbelian2 (imgIn V S) = {W}) {n : G} (hnV : n ∈ normalizer (V : Set G))
    (hnS : n ∈ normalizer (S : Set G)) : actFun V n ∈ normalizer (W : Set (MulAut ↥V)) := by
  have hW : W ∈ maxElemAbelian2 (imgIn V S) := by
    rw [hmax]
    exact Set.mem_singleton W
  obtain ⟨hWS, -, hWcard⟩ := hW
  have hnSs := actFun_mem_normalizer_imgIn V S hnV hnS
  have hinj : Function.Injective (MulAut.conj (actFun V n)).toMonoidHom :=
    (MulAut.conj (actFun V n)).injective
  have hW' : W.map (MulAut.conj (actFun V n)).toMonoidHom ∈ maxElemAbelian2 (imgIn V S) := by
    refine ⟨?_, hWab.map _, fun D hD hDab => ?_⟩
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
      exact (Subgroup.mem_normalizer_iff.1 hnSs w).1 (hWS hw)
    · rw [card_map_of_injective hinj]
      exact hWcard D hD hDab
  rw [hmax] at hW'
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 hW'

theorem fusionIsSylowIn_normalizer_of_maxElemAbelian2 {G : Type*} [Group G] [Finite G]
    (V : Subgroup G) {W : Subgroup (MulAut ↥V)} (hWab : IsElemAbelian 2 W) {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S
      (preIn V (normalizer (W : Set (MulAut ↥V)) ⊓ imgIn V (normalizer (V : Set G)))))
    (hmax : maxElemAbelian2 (imgIn V S) = {W}) :
    fusionIsSylowIn 2 S (normalizer (V : Set G)) := by
  obtain ⟨hSI, hS2, hSmax⟩ := hS
  refine ⟨hSI.trans (preIn_le_normalizer V _), hS2, fun P hPH hP2 hSP => ?_⟩
  by_contra hne
  obtain ⟨n, hnP, hnS, hn⟩ := exists_mem_normalizer_not_mem_of_isPGroup_two hP2 hSP (Ne.symm hne)
  have hnV : n ∈ normalizer (V : Set G) := hPH hnP
  have hnI : n ∈ preIn V (normalizer (W : Set (MulAut ↥V)) ⊓ imgIn V (normalizer (V : Set G))) :=
    (mem_preIn_iff V _).2 ⟨hnV, Subgroup.mem_inf.2
      ⟨actFun_mem_normalizer_of_maxElemAbelian2_eq_singleton V hWab hmax hnV hnS,
        actFun_mem_imgIn hnV hnV⟩⟩
  have hQ := hSmax (S ⊔ zpowers n) (sup_le hSI (zpowers_le.2 hnI))
    (hP2.to_le (sup_le hSP (zpowers_le.2 hnP))) le_sup_left
  have hnQ : n ∈ S ⊔ zpowers n := (le_sup_right : zpowers n ≤ S ⊔ zpowers n) (mem_zpowers n)
  rw [hQ] at hnQ
  exact hn hnQ

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5

module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbReduceNormal

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

namespace GOrbReduce

theorem gOrbConcl_of_simple (h : KFactChevGraphOrbitSimple) {Y : Type} [Group Y] [Finite Y]
    {L R P : Subgroup Y} (hS : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L))
    (hC : IsChevTwo (↥L ⧸ Subgroup.center ↥L)) (hRN : R ≤ Subgroup.normalizer (L : Set Y))
    (hR2 : IsPGroup 2 R) (hSyl : IsSylowTwoOf (R ⊓ L) L) (hMin : IsMinOverBorel L (R ⊓ L) P)
    (hnP : ¬ R ≤ Subgroup.normalizer (P : Set Y)) : GOrbConcl R P := by
  obtain ⟨N, hN⟩ : ∃ N : Subgroup Y, N = Subgroup.normalizer (L : Set Y) := ⟨_, rfl⟩
  have hNle : N ≤ Subgroup.normalizer (L : Set Y) := hN.le
  have hLN : L ≤ N := hN ▸ Subgroup.le_normalizer
  have hRN' : R ≤ N := hN ▸ hRN
  have hPN : P ≤ N := hMin.1.trans hLN
  haveI : (L.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNle
  have hι : Function.Injective N.subtype := N.subtype_injective
  have hL₁ : (L.subgroupOf N).map N.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLN
  have hR₁ : (R.subgroupOf N).map N.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRN'
  have hP₁ : (P.subgroupOf N).map N.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPN
  have e : ↥(L.subgroupOf N) ≃* ↥L :=
    (Subgroup.equivMapOfInjective (L.subgroupOf N) N.subtype hι).trans
      (MulEquiv.subgroupCongr hL₁)
  have e' : ↥(L.subgroupOf N) ⧸ Subgroup.center ↥(L.subgroupOf N) ≃*
      ↥L ⧸ Subgroup.center ↥L :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hS₁ : IsSimpleGroup (↥(L.subgroupOf N) ⧸ Subgroup.center ↥(L.subgroupOf N)) := by
    haveI := hS
    exact e'.isSimpleGroup
  have hC₁ : IsChevTwo (↥(L.subgroupOf N) ⧸ Subgroup.center ↥(L.subgroupOf N)) :=
    isChevTwo_congr e'.symm hC
  have hR₂ : IsPGroup 2 (R.subgroupOf N) := hR2.comap_of_injective N.subtype hι
  have hSyl₁ : IsSylowTwoOf (R.subgroupOf N ⊓ L.subgroupOf N) (L.subgroupOf N) := by
    rw [← isSylowTwoOf_map_iff hι, Subgroup.map_inf _ _ _ hι, hR₁, hL₁]
    exact hSyl
  have hMin₁ : IsMinOverBorel (L.subgroupOf N) (R.subgroupOf N ⊓ L.subgroupOf N)
      (P.subgroupOf N) := by
    rw [← isMinOverBorel_map_iff hι, Subgroup.map_inf _ _ _ hι, hR₁, hL₁, hP₁]
    exact hMin
  have hnP₁ : ¬ R.subgroupOf N ≤ Subgroup.normalizer ((P.subgroupOf N : Subgroup N) : Set N) := by
    intro hle
    apply hnP
    have h1 : (R.subgroupOf N).map N.subtype ≤
        Subgroup.normalizer (((P.subgroupOf N).map N.subtype : Subgroup Y) : Set Y) :=
      (Subgroup.map_mono hle).trans (Subgroup.le_normalizer_map N.subtype)
    rwa [hR₁, hP₁] at h1
  have key := gOrbConcl_of_normal h hS₁ hC₁ hR₂ hSyl₁ hMin₁ hnP₁
  have hmap := gOrbConcl_map hι key
  rwa [hR₁, hP₁] at hmap

end GOrbReduce

theorem kFactChevGraphOrbit_of_simple (h : KFactChevGraphOrbitSimple) : KFactChevGraphOrbit := by
  unfold KFactChevGraphOrbit
  intro Y _ _ L R P hL hChev hRN hR2 hSyl hMin hnP
  exact GOrbReduce.gOrbConcl_of_simple h hL.2 hChev hRN hR2 hSyl hMin hnP

end CFSG.AGLEmbeddingD2.Tits.GN516

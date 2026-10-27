module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadicalSmall
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchGlue

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits ToralCensus

section Catalog


theorem ToralCensus.radicalSelfNormOver_of_isClassicalTwoOrG2 {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (h : IsClassicalTwoOrG2 X) : RadicalSelfNormOver X := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | h | h
  · exact radicalSelfNormOver_of_index d hd e
  · exact radicalSelfNormOver_small (Or.inl h)
  · exact radicalSelfNormOver_small (Or.inr h)

theorem parabRadicalSelfNorm : ParabRadicalSelfNorm := by
  intro Y _ _ L J hCP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set φ : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective Z
  have hZr : Nat.Coprime (Nat.card Z) 2 := Nat.coprime_two_right.2 hCP.odd
  have hsimp : IsSimpleGroup (↥L ⧸ Z) := hCP.comp.2.2.2
  have hJL : J ≤ L := hCP.parab.1
  obtain ⟨T, hT, hTJ⟩ := hCP.parab.2
  set J' : Subgroup ↥L := J.subgroupOf L with hJ'
  set T' : Subgroup ↥L := T.subgroupOf L with hT'
  set Q' : Subgroup ↥L := (pCoreOf 2 J).subgroupOf L with hQ'
  have hTr : T ≤ L.subtype.range := by rw [Subgroup.range_subtype]; exact hT.1
  have hT'2 : IsPGroup 2 T' := hT.2.1.comap_of_injective L.subtype L.subtype_injective
  have hNJ' : Subgroup.normalizer (T' : Set ↥L) ≤ J' := by
    rw [hT', Subgroup.subgroupOf, ← Subgroup.comap_normalizer_eq_of_le_range hTr]
    intro x hx
    exact hTJ ⟨x.2, hx⟩
  have hZJ : Z ≤ J' := (Subgroup.center_le_normalizer _).trans hNJ'
  have hJcomap : (J'.map φ).comap φ = J' := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.2 hZJ
  have hidx : ¬ 2 ∣ (T'.map φ).index := fun hd =>
    hT.2.2 (by simpa [Subgroup.relIndex] using hd.trans (Subgroup.index_map_dvd _ hφs))
  set T₀ : Sylow 2 (↥L ⧸ Z) := (hT'2.map φ).toSylow hidx
  have hNT : Subgroup.normalizer (((T₀ : Subgroup (↥L ⧸ Z))) : Set (↥L ⧸ Z)) ≤ J'.map φ := by
    have h := normalizer_eq_comap_normalizer_map Z le_rfl hZr hT'2
    have h' := congrArg (Subgroup.map φ) h
    rw [Subgroup.map_comap_eq_self_of_surjective hφs] at h'
    change Subgroup.normalizer ((T'.map φ : Subgroup (↥L ⧸ Z)) : Set (↥L ⧸ Z)) ≤ _
    rw [← h']
    exact Subgroup.map_mono hNJ'
  have hQ'2 : IsPGroup 2 Q' :=
    (pCoreOf_isPGroup 2 J).comap_of_injective L.subtype L.subtype_injective
  have hQ'J : Q' ≤ J' := Subgroup.comap_mono (pCoreOf_le 2 J)
  have hJQ' : J' ≤ Subgroup.normalizer (Q' : Set ↥L) :=
    (Subgroup.comap_mono (le_normalizer_pCoreOf 2 J)).trans (Subgroup.le_normalizer_comap _)
  have hpJ : pCoreOf 2 J' = Q' := by
    refine le_antisymm ?_ (le_pCoreOf_of_le_normalizer 2 hQ'J hJQ' hQ'2)
    intro x hx
    show (x : Y) ∈ pCoreOf 2 J
    have hle : (pCoreOf 2 J').map L.subtype ≤ pCoreOf 2 J := by
      refine le_pCoreOf_of_le_normalizer 2 ?_ ?_ ((pCoreOf_isPGroup 2 J').map _)
      · rintro _ ⟨y, hy, rfl⟩
        exact pCoreOf_le 2 J' hy
      · intro j hj
        have hj' : (⟨j, hJL hj⟩ : ↥L) ∈ Subgroup.normalizer (pCoreOf 2 J' : Set ↥L) :=
          le_normalizer_pCoreOf 2 J' hj
        have := Subgroup.le_normalizer_map L.subtype ⟨_, hj', rfl⟩
        exact this
    exact hle ⟨x, hx, rfl⟩
  have hO : pCoreOf 2 (J'.map φ) = Q'.map φ := by
    refine le_antisymm ?_ (hpJ ▸ map_pCoreOf_le φ J')
    have h := pCoreOf_le_map_pCoreOf_comap Z le_rfl hZr (J'.map φ)
    rwa [hJcomap, hpJ] at h
  rintro l ⟨hlL, hlN⟩
  have hl' : (⟨l, hlL⟩ : ↥L) ∈ Subgroup.normalizer (Q' : Set ↥L) :=
    Subgroup.le_normalizer_comap L.subtype hlN
  have hφl : φ ⟨l, hlL⟩ ∈ Subgroup.normalizer (pCoreOf 2 (J'.map φ) : Set (↥L ⧸ Z)) := by
    rw [hO]
    exact Subgroup.le_normalizer_map φ ⟨_, hl', rfl⟩
  have hmem := radicalSelfNormOver_of_isClassicalTwoOrG2 hCP.type T₀ (J'.map φ) hNT hφl
  have : (⟨l, hlL⟩ : ↥L) ∈ J' := by
    rw [← hJcomap]
    exact hmem
  exact this

theorem glueVhyp_of_schreier (hSch : KFactCatalogSchreier) : GlueVhyp :=
  glueVhyp_of hSch parabRadicalSelfNorm

end Catalog

end CFSG.AGLEmbedding

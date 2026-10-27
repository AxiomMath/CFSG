module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableDatum
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableW

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519

section Types

variable {G : Type} [Group G]

theorem IsListedComponentW.k32ListedType_or {M S L : Subgroup G} {z : G}
    (h : IsListedComponentW M S L z) :
    K32ListedType ↥L ∨ IsThreeFoldCoverAlt L 6 ∨ IsThreeFoldCoverAlt L 7 := by
  rcases h with h | h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, -, -⟩
  · exact Or.inl (.bender h)
  · rcases h with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h | h | h
    · exact Or.inl (.psl3 n hn h)
    · exact Or.inl (.psp4 n hn h)
    · exact Or.inl (.alt6 h)
    · exact Or.inl (.psl3four h)
    · exact Or.inr (Or.inl h)
  · rcases h with h | h
    · exact Or.inl (.alt7 h)
    · exact Or.inr (Or.inr h)
  · rcases h with h | h
    · exact Or.inl (.psl33 h)
    · exact Or.inl (.m11 h)
  · obtain ⟨p, hp, h⟩ := h
    exact Or.inl (.psl2p p hp h)
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl (.m22 h)
    · exact Or.inl (.m22cover h)
    · exact Or.inl (.m23 h)
  · exact Or.inl (.psl42 h)

end Types

section ThreeFold

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem k32_false_of_threeFoldCover (ctx : K32Ctx T M H S L s x z₁ z₂ K)
    (hKnorm : centralizerElem z₂ ≤ Subgroup.normalizer (K : Set G)) {m : ℕ}
    (h : IsThreeFoldCoverAlt K m) : False := by
  classical
  have hKG₂ : K ≤ centralizerElem z₂ := ctx.comp.1
  set Z : Subgroup G := (Subgroup.center ↥K).map K.subtype with hZ
  have hZcard : Nat.card Z = 3 := by
    rw [hZ, Subgroup.card_map_of_injective K.subtype_injective]
    exact h.2.1
  have hZK : Z ≤ K := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hZG₂ : Z ≤ centralizerElem z₂ := hZK.trans hKG₂
  have hZc : ∀ g ∈ Z, ∀ k ∈ K, k * g = g * k := by
    rintro _ ⟨c, hc, rfl⟩ k hk
    have := Subgroup.mem_center_iff.mp hc ⟨k, hk⟩
    exact congrArg Subtype.val this
  have hZnorm : (Z.subgroupOf (centralizerElem z₂)).Normal := by
    constructor
    intro n hn g
    have hn' : (n : G) ∈ Z := Subgroup.mem_subgroupOf.mp hn
    rw [Subgroup.mem_subgroupOf]
    have hg : (g : G) ∈ Subgroup.normalizer (K : Set G) := hKnorm g.2
    have hgn : (g : G) * (n : G) * (g : G)⁻¹ ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp hg (n : G)).mp (hZK hn')
      exact this
    have hz : ∃ c ∈ Subgroup.center ↥K, (c : G) = (g : G) * (n : G) * (g : G)⁻¹ := by
      refine ⟨⟨(g : G) * (n : G) * (g : G)⁻¹, hgn⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have hk' : (g : G)⁻¹ * (k : G) * (g : G) ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) (k : G)).mp k.2
        simpa using this
      have hc := hZc _ hn' _ hk'
      show (k : G) * ((g : G) * (n : G) * (g : G)⁻¹) = ((g : G) * (n : G) * (g : G)⁻¹) * (k : G)
      calc (k : G) * ((g : G) * (n : G) * (g : G)⁻¹)
          = (g : G) * (((g : G)⁻¹ * (k : G) * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
        _ = (g : G) * ((n : G) * ((g : G)⁻¹ * (k : G) * (g : G))) * (g : G)⁻¹ := by rw [hc]
        _ = ((g : G) * (n : G) * (g : G)⁻¹) * (k : G) := by group
    obtain ⟨c, hc, hcg⟩ := hz
    exact ⟨c, hc, hcg⟩
  have hodd : Odd (Nat.card ↥(Z.subgroupOf (centralizerElem z₂))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZG₂).toEquiv, hZcard]
    decide
  have hle : Z.subgroupOf (centralizerElem z₂) ≤ fusionOddCore ↥(centralizerElem z₂) :=
    le_sSup ⟨hZnorm, hodd⟩
  have hZodd : Z ≤ oddCoreIn (centralizerElem z₂) := by
    intro g hg
    exact ⟨⟨g, hZG₂ hg⟩, hle (Subgroup.mem_subgroupOf.mpr hg), rfl⟩
  rw [ctx.oddCore] at hZodd
  have hZbot : Z = ⊥ := le_bot_iff.mp hZodd
  rw [hZbot, Subgroup.card_bot] at hZcard
  omega

end ThreeFold

section Main

variable {G : Type} [Group G] [Finite G]

theorem k32TableW_of_inputs (hP : Prop121Three) (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hTab : K32AutExcl) (hAlt : K32AltOut) : K32TableW := by
  intro G _ _ T M H S L s x z₁ z₂ K ctx hlist
  by_cases hS : sOne S x ≤ Subgroup.normalizer (K : Set G)
  · have hKnorm : centralizerElem z₂ ≤ Subgroup.normalizer (K : Set G) := by
      have hs := ctx.a3.cs.setting
      have hpc : pCoreOf 2 (centralizerElem z₂) ≠ ⊥ :=
        pCoreOf_centralizerElem_ne_bot ctx.a3.z₂_ne ctx.a3.sq₂
      have hJc : K ∈ cComp (centralizerElem z₂) := mem_cComp_of_isComponentIn ctx.comp
      rcases hP G hs.simple hs.nonabelian hs.qtke _ hpc K hJc with hnorm | ⟨hcard, -⟩
      · exact hnorm
      · exact (false_of_card_conj_eq_two ctx.sylow hS hcard).elim
    rcases IsListedComponentW.k32ListedType_or hlist with hty | h6 | h7
    · by_contra h8
      obtain ⟨X, P, R, A, V, hdat⟩ := k32_datum_of_normal hD h27_1 ctx hKnorm
      exact hTab ↥K (BenderBranch.isQuasisimple_of_isComponentIn ctx.comp) hty h8 X P R A V hdat
    · exact (k32_false_of_threeFoldCover ctx hKnorm h6).elim
    · exact (k32_false_of_threeFoldCover ctx hKnorm h7).elim
  · exact (k32_false_of_swapped hP hD h27_1 hAlt ctx hS).elim

end Main

end CFSG.QuasithinUnique.DoubleA3

module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

theorem lemma33One_of_asc76Theorem2 (hT2 : Asc76Theorem2) : Lemma33One := by
  intro G _ _ A hA R hR g hg T hT hT1 hTR
  rcases hT2 G A hA.oddCore hA.standard (asc76HypII_of_hypII hA.standard.1 hA.hypII) hA.rank R
      hR g hg T hT hT1 with ⟨h4, -, -⟩ | ⟨-, hTs, hc⟩
  · exact Or.inl h4
  · refine Or.inr ⟨hTs, ?_⟩
    rwa [inf_eq_left.mpr hTR] at hc

variable {G : Type*} [Group G] [Finite G]

theorem inf_centralizer_mulEquiv_of_tightlyEmbedded {K R T : Subgroup G} (hK : TightlyEmbedded K)
    {g : G} (hg : g ∉ normalizer (K : Set G))
    (hT : IsSylowOf 2 T (rightConjugate K g ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥)
    (hR : IsSylowOf 2 R K) (hTR : T ≤ normalizer (R : Set G)) :
    Nonempty (↥(R ⊓ centralizer (T : Set G)) ≃* T) := by
  obtain ⟨T', hT'⟩ := id hT
  have hRT : IsPGroup 2 (R ⊔ T : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hR.isPGroup hT.isPGroup hTR
  have hRTle : R ⊔ T ≤ K ⊔ sylowImage _ T' := by
    rw [sylowImage, hT']
    exact sup_le_sup_right hR.le T
  have hRTp : IsPGroup 2 ((R ⊔ T).subgroupOf (K ⊔ sylowImage _ T')) := hRT.comap_subtype
  obtain ⟨S, hS⟩ := hRTp.exists_le_sylow
  have hTS : sylowImage _ T' ≤ sylowImage _ S := by
    intro x hx
    have hxRT : x ∈ R ⊔ T := by
      rw [sylowImage, hT'] at hx
      exact mem_sup_right hx
    exact ⟨⟨x, hRTle hxRT⟩, hS hxRT, rfl⟩
  have hne : sylowImage _ T' ≠ ⊥ := by rwa [sylowImage, hT']
  obtain ⟨hN, hTK1, -, -, factor, -, -, -⟩ := theorem_2_part_one K hK g hg T' S hTS hne
  set X := sylowImage (K ⊔ sylowImage _ T') S with hX
  have hTeq : sylowImage _ T' = T := hT'
  rw [hTeq] at hTK1
  have hRX : R ≤ X := fun x hx => ⟨⟨x, hRTle (mem_sup_left hx)⟩, hS (mem_sup_left hx), rfl⟩
  have hXK : X ⊓ K = R := by
    refine hR.eq_of_le (le_inf hRX hR.le) inf_le_right ?_
    exact (S.isPGroup'.map (K ⊔ sylowImage _ T').subtype).to_le inf_le_left
  have hkey : relativeNormalizer (sylowImage _ T') X ⊓ K = R ⊓ centralizer (T : Set G) := by
    rw [relativeNormalizer, hTeq, inf_assoc, inf_comm X, ← inf_assoc, inf_assoc, inf_comm K,
      hXK, inf_comm]
    refine le_antisymm (fun r hr => ⟨hr.1, ?_⟩) (inf_le_inf_left R (centralizer_le_normalizer _))
    refine mem_centralizer_iff.mpr fun t ht => ?_
    have h1 : r * t * r⁻¹ * t⁻¹ ∈ T := by
      have := (mem_normalizer_iff.mp hr.2 t).mp ht
      exact T.mul_mem this (T.inv_mem ht)
    have h2 : r * t * r⁻¹ * t⁻¹ ∈ R := by
      have h3 := (mem_normalizer_iff.mp (hTR ht) r⁻¹).mp (R.inv_mem hr.1)
      have h4 := R.mul_mem hr.1 h3
      simpa [mul_assoc] using h4
    have h4 : r * t * r⁻¹ * t⁻¹ ∈ T ⊓ K := ⟨h1, hR.le h2⟩
    rw [hTK1, mem_bot] at h4
    have : r * t * r⁻¹ = t := mul_inv_eq_one.mp h4
    calc t * r = r * t * r⁻¹ * r := by rw [this]
      _ = r * t := by group
  exact ⟨((MulEquiv.subgroupCongr hkey).symm.trans factor.symm).trans
    (MulEquiv.subgroupCongr hTeq)⟩

theorem lemma33Four :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Hyp31 A →
      ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
      ∀ g : G, g ∉ normalizer (A : Set G) → ∀ T : Subgroup G,
        IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)) →
        T ≠ ⊥ → T ≤ normalizer (R : Set G) →
          Nonempty (↥(R ⊓ centralizer (T : Set G)) ≃* T) := by
  intro G _ _ A hA R hR g hg T hT hT1 hTR
  have hNK := normalizer_centralizer_eq hA.standard
  rw [← hNK] at hg hT
  exact inf_centralizer_mulEquiv_of_tightlyEmbedded (tightlyEmbedded_centralizer hA.standard) hg
    hT hT1 hR hTR

end CFSG.ComponentClassification.AS76b

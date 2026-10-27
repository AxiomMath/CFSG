module

public import CFSG.LocalAnalysis.SectionRank.Induction
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def CatalogClassicalOddHyp : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsStronglyQuasithin L →
    Odd (Nat.card (Subgroup.center L)) → ∀ {t : StatedLieTag} {n p f : ℕ}, p.Prime → p ≠ 2 →
    StatedClassicalModel (L ⧸ Subgroup.center L) t n p f → CatalogStepConclusion L

@[expose] def CatalogClassicalEvenHyp : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsStronglyQuasithin L →
    Odd (Nat.card (Subgroup.center L)) → ∀ {t : StatedLieTag} {n f : ℕ},
    StatedClassicalModel (L ⧸ Subgroup.center L) t n 2 f → CatalogStepConclusion L

@[expose] def CatalogExceptionalEvenHyp : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsStronglyQuasithin L →
    Odd (Nat.card (Subgroup.center L)) → ∀ f : ℕ,
    ((∃ t ∈ chevalleyExceptionalTags, ChevalleyExceptionalModel (L ⧸ Subgroup.center L) t 2 f) ∨
      ReeTitsModel (L ⧸ Subgroup.center L) .twistedF4 2 f ∨
      ReeTitsModel (L ⧸ Subgroup.center L) .Tits 2 f ∨
      SuzukiModel (L ⧸ Subgroup.center L) 2 f) → CatalogStepConclusion L

@[expose] def CatalogSporadicHyp : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsStronglyQuasithin L →
    Odd (Nat.card (Subgroup.center L)) → NativeSporadic.SporadicRep (L ⧸ Subgroup.center L) →
    CatalogStepConclusion L

theorem catalog_center_quotient {L : Type} [Group L] (hL : IsQuasisimple L)
    (hK : IsKGroupCat L) : Catalog (L ⧸ Subgroup.center L) := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.1
  let φ : (⊤ : Subgroup L) →* L ⧸ Subgroup.center L :=
    (QuotientGroup.mk' (Subgroup.center L)).comp (⊤ : Subgroup L).subtype
  exact catalog_of_isKGroupCat_of_surjective hK ⊤ φ fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩

theorem catalogStepHyp_of
    (hodd : CatalogClassicalOddHyp) (heven : CatalogClassicalEvenHyp)
    (hexc : CatalogExceptionalEvenHyp) (hspor : CatalogSporadicHyp) : CatalogStepHyp := by
  intro L _ _ hL hLK hZ
  have hSQT := hLK.1
  rcases catalog_center_quotient hL hLK.2 with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ |
      ⟨t, n, p, f, hm⟩ | (⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩) | hs
  · exfalso
    obtain ⟨a, b, hab⟩ := hL.2.2
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact catalog_alternating hL hSQT hZ hn e
  · have hp : p.Prime := hm.1.1
    by_cases hp2 : p = 2
    · subst hp2
      exact heven L hL hSQT hZ hm
    · exact hodd L hL hSQT hZ hp hp2 hm
  · have hp : p.Prime := hm.1.1
    by_cases hp2 : p = 2
    · subst hp2
      exact hexc L hL hSQT hZ f (Or.inl ⟨t, ht, hm⟩)
    · exact catalog_exceptional_odd hL hSQT hZ ⟨p, f, hp, hp2, Or.inl ⟨t, ht, hm⟩⟩
  · have hp : p.Prime := hm.1.1
    simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    ·
      have hp3 : p ≠ 2 := by
        rw [(smallReeModel_rank hm).1]
        norm_num
      exact catalog_exceptional_odd hL hSQT hZ ⟨p, f, hp, hp3, Or.inr hm⟩
    · obtain ⟨-, -, -, hp2, -⟩ := hm.1
      subst hp2
      exact hexc L hL hSQT hZ f (Or.inr (Or.inl hm))
    · obtain ⟨-, -, -, hp2, -⟩ := hm.1
      subst hp2
      exact hexc L hL hSQT hZ f (Or.inr (Or.inr (Or.inl hm)))
  · have hp2 : p = 2 := hm.1
    subst hp2
    exact hexc L hL hSQT hZ f (Or.inr (Or.inr (Or.inr hm)))
  · exact hspor L hL hSQT hZ hs

end CFSG.SectionRank

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SD5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82E16InnerT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L F : Subgroup G), IsOm6M L →
    F ≤ normalizer (L : Set G) → IsElemAb2 F 4 → F ⊓ centralizer (L : Set G) = ⊥ →
      (∀ f ∈ F, orderOf f = 2 → InnerOn L f ∨ ∃ α : ℤˣ, InducesTypeSome L f 6 (-1) 3 α) →
        ∀ f ∈ F, InnerOn L f

theorem asc82E16Inner_of (hT6 : Asc82Tab6M) (hT : Asc82E16InnerT) : Asc82E16Inner := by
  intro G _ _ L F hL hFN hF hFC hlay f hf
  refine hT G L F hL hFN hF hFC (fun g hg hg2 => ?_) f hf
  have hgN : g ∈ normalizer (L : Set G) := hFN hg
  rcases (hT6.layer_trivial G L hL g hg2 hgN).mp (hlay g hg hg2) with h4 | h3
  · exact Or.inl ((hT6.inner_iff G L hL g hg2 hgN).mpr h4).1
  · exact Or.inr h3

theorem asc82Lemma91_of_inputs (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h66 : Asc82Lemma66)
    (h82 : Asc82Lemma82) (hT6 : Asc82Tab6M) (hB8 : Asc82Sec8B) (hT : Asc82E16InnerT) :
    Asc82Lemma91 :=
  asc82Lemma91_of h36 h37 h66 h82 hT6 hB8 (asc82E16Inner_of hT6 hT) (asc82RankOm6M_of hT6)

end CFSG.OddStandard.SmallF3.Omega

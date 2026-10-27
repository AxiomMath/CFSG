module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem pRank_add_le_pRank_centralizer_of_fixedBlock {M S L₁ L₂ : Subgroup G}
    (h₁ : IsWeakSBlock M S L₁) (h₂ : IsWeakSBlock M S L₂) (hne : barM M L₁ ≠ barM M L₂)
    (hZ₁ : ¬ 3 ∣ Nat.card (barM M L₁ ⊓
      Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    {x : G} (hxL₂ : L₂ ≤ Subgroup.centralizer ({x} : Set G)) :
    Open.pRank 3 (L₁ ⊓ Subgroup.centralizer ({x} : Set G)) + Open.pRank 3 L₂ ≤
      Open.pRank 3 (Subgroup.centralizer ({x} : Set G) ⊓ M) := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  set L₁b := barM M L₁
  set L₂b := barM M L₂
  set D₁ := barM M (L₁ ⊓ Subgroup.centralizer ({x} : Set G))
  have hcomp : ⁅L₁b, L₂b⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁.component h₂.component hne
  have hL₂C₁ : L₂b ≤ Subgroup.centralizer (L₁b : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer).mp ?_
    rw [Subgroup.commutator_comm]
    exact hcomp
  have hD₁L : D₁ ≤ L₁b := barM_mono inf_le_left
  have hc : ∀ a ∈ D₁, ∀ b ∈ L₂b, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hL₂C₁ hb) a (hD₁L ha))
  have hi : Nat.Coprime 3 (Nat.card (D₁ ⊓ L₂b : Subgroup _)) := by
    rw [Nat.Prime.coprime_iff_not_dvd h3]
    intro hdvd
    apply hZ₁
    exact hdvd.trans (Subgroup.card_dvd_of_le fun u hu => ⟨hD₁L hu.1, hL₂C₁ hu.2⟩)
  have hs := pRank_add_le_pRank_sup_of_coprime h3 hc hi
  have hsup : D₁ ⊔ L₂b ≤ barM M (Subgroup.centralizer ({x} : Set G) ⊓ M) :=
    sup_le (barM_mono fun l hl => ⟨hl.2, h₁.le hl.1⟩) (barM_mono fun l hl => ⟨hxL₂ hl, h₂.le hl⟩)
  have hCx : Open.pRank 3 (barM M (Subgroup.centralizer ({x} : Set G) ⊓ M)) =
      Open.pRank 3 (Subgroup.centralizer ({x} : Set G) ⊓ M) :=
    pRank_barM_eq h3 (by decide) M _ inf_le_right
  have hD₁ : Open.pRank 3 D₁ = Open.pRank 3 (L₁ ⊓ Subgroup.centralizer ({x} : Set G)) :=
    pRank_barM_eq h3 (by decide) M _ (inf_le_left.trans h₁.le)
  have hL₂b : Open.pRank 3 L₂b = Open.pRank 3 L₂ := pRank_barM_eq h3 (by decide) M L₂ h₂.le
  have hsup' := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hsup
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3A9Rank
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem false_of_three_le_pRank_barM (hrank : evenRank G = 3) (h3 : 3 ∈ rankThreeSigmaA G)
    {M L : Subgroup G} (hM : IsTwoLocal M) (hLM : L ≤ M) (h : 3 ≤ Open.pRank 7 (barM M L)) :
    False := by
  have h8 := pRank_barM_le (q := 7) (by norm_num) (by norm_num) M L hLM
  have h9 := local_pRank_le_localRank 7 (by norm_num) M hM
  have h10 := rankThreeLocalRank_lt_three_of_sigmaA_three hrank h3 (q := 7) (by norm_num)
    (by norm_num)
  have h11 := pRank_mono 7 (by norm_num) hLM
  omega

theorem false_of_two_blocks (hrank : evenRank G = 3) (h3 : 3 ∈ rankThreeSigmaA G)
    {M L₁ L₂ : Subgroup G} (hM : IsTwoLocal M) (h₁ : IsTwoPrimeComponent M L₁)
    (h₂ : IsTwoPrimeComponent M L₂) (hne : L₁ ≠ L₂)
    {E₁ E₂ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hE₁ : E₁ ≤ barM M L₁) (hE₂ : E₂ ≤ barM M L₂)
    (he₁ : IsElemAbelian 7 E₁) (he₂ : IsElemAbelian 7 E₂) (hc₁ : Nat.card E₁ = 7 ^ 2)
    (hc₂ : Nat.card E₂ = 7 ^ 2)
    (hz : E₁ ⊓ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥) : False := by
  have hbar : barM M L₁ ≠ barM M L₂ := fun he => hne (h₁.eq_of_barM_eq h₂ he)
  have hcom := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁.component
    h₂.component hbar
  have hcomm : ∀ h ∈ barM M L₁, ∀ y ∈ barM M L₂, h * y = y * h := by
    intro h hh y hy
    have h' := Subgroup.commutator_mem_commutator hh hy
    rw [hcom, Subgroup.mem_bot] at h'
    exact commutatorElement_eq_one_iff_mul_comm.mp h'
  have hxy : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy => hcomm x (hE₁ hx) y (hE₂ hy)
  have hN : E₂ ≤ Subgroup.normalizer (E₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hxy x hx y hy)
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right E₁ E₂
    (fun x hx => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      fun y hy => (hxy x hx y hy).symm))
  have hel : IsElemAbelian 7 (E₁ ⊔ E₂) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · have ha : (a : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
          ((E₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) * (E₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
        rw [← hmul]; exact a.2
      have hb : (b : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
          ((E₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) * (E₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
        rw [← hmul]; exact b.2
      obtain ⟨x, hx, y, hy, hxy'⟩ := ha
      obtain ⟨x', hx', y', hy', hxy''⟩ := hb
      change (a : ↥M ⧸ CFSG.pCore 2 ↥M) * b = b * a
      rw [← hxy', ← hxy'']
      have c1 : x * x' = x' * x := congrArg Subtype.val (he₁.1.1.comm ⟨x, hx⟩ ⟨x', hx'⟩)
      have c2 : y * y' = y' * y := congrArg Subtype.val (he₂.1.1.comm ⟨y, hy⟩ ⟨y', hy'⟩)
      calc x * y * (x' * y') = x * (y * x') * y' := by group
        _ = x * (x' * y) * y' := by rw [← hxy x' hx' y hy]
        _ = (x * x') * (y * y') := by group
        _ = (x' * x) * (y' * y) := by rw [c1, c2]
        _ = x' * (x * y') * y := by group
        _ = x' * (y' * x) * y := by rw [hxy x hx y' hy']
        _ = x' * y' * (x * y) := by group
    · intro a ha
      have ha' : a ∈ ((E₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) *
          (E₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
        rw [← hmul]; exact ha
      obtain ⟨x, hx, y, hy, rfl⟩ := ha'
      have hc : Commute x y := hxy x hx y hy
      rw [hc.mul_pow, he₁.2 x hx, he₂.2 y hy, one_mul]
  have hinf : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff, ← hz]
    refine le_inf inf_le_left fun y hy => ?_
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => hcomm h hh y (hE₂ hy.2)
  have hcard : Nat.card (E₁ ⊔ E₂ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) = 7 ^ 4 := by
    have h := card_sup_mul_card_inf_eq_of_le_normalizer hN
    rw [hinf, Subgroup.card_bot, hc₁, hc₂, mul_one] at h
    rw [h]
    norm_num
  have h4 : 4 ≤ Open.pRank 7 (E₁ ⊔ E₂) :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 7 (by norm_num) _)
      ⟨E₁ ⊔ E₂, le_rfl, hel, hcard⟩
  have hLsup : L₁ ⊔ L₂ ≤ M := sup_le h₁.le h₂.le
  have hE : E₁ ⊔ E₂ ≤ barM M (L₁ ⊔ L₂) :=
    sup_le (hE₁.trans (barM_mono le_sup_left)) (hE₂.trans (barM_mono le_sup_right))
  have h5 := pRank_mono 7 (by norm_num) hE
  exact false_of_three_le_pRank_barM hrank h3 hM hLsup (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC

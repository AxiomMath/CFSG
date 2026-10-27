module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporData
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.RankThree.PartOne.F106.ConvItems
public import CFSG.LocalAnalysis.SectionRank.Sporadic.B
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co1
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi22
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi23
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi24prime
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HN
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Ly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.McL
public import CFSG.LocalAnalysis.SectionRank.Sporadic.ON
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Suz
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Th
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MonsterD2PRank
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCarrierSimple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Blueprint TauCeti CFSG.RankThree.PartOne.F106 CFSG.RankThree.PartOne.Census3

theorem not_pow_four_dvd_of_carrier (s : SporadicName)
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* s.Group))
    (hord : ¬ 3 ^ 4 ∣ Nat.card (NativeSporadic.Carrier s)) :
    ¬ 3 ^ 4 ∣ Nat.card (CFSGIndex.sporadic s).Group := by
  obtain ⟨b⟩ := hbr
  intro h4
  exact hord (by rw [Nat.card_congr b.toEquiv]; exact h4)

theorem four_le_pRank_of_elem (s : SporadicName)
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* s.Group))
    (hE : ∃ E : Subgroup (NativeSporadic.Carrier s),
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4)
    [Finite (CFSGIndex.sporadic s).Group] :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (CFSGIndex.sporadic s).Group) := by
  obtain ⟨b⟩ := hbr
  obtain ⟨E, hE, hc⟩ := hE
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (le_top : E.map b.toMonoidHom ≤ ⊤)
    (CFSG.SectionRank.isElemAbelian_map hE b.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective b.injective, hc])

theorem four_le_pRank_of_iso (s : SporadicName)
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* s.Group)) {R : Type} [Group R]
    (hR : ∀ [Finite R], 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup R))
    (hiso : Nonempty (R ≃* NativeSporadic.Carrier s))
    [Finite (CFSGIndex.sporadic s).Group] :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (CFSGIndex.sporadic s).Group) := by
  obtain ⟨b⟩ := hbr
  obtain ⟨i⟩ := hiso
  let f : R ≃* (CFSGIndex.sporadic s).Group := i.trans b
  haveI : Finite R := Finite.of_equiv _ f.symm.toEquiv
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) f]
  exact hR

section Monster

open CFSG.Monster CFSG.Monster.Visible CFSG.Monster.Generated

theorem four_le_pRank_Gmat
    [Finite Gmat] : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Gmat) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Finite Gvis :=
    Finite.of_injective (Subgroup.inclusion Hmat_le_Gmat) (Subgroup.inclusion_injective _)
  have e : Gvis ⧸ rhoQvis ≃* NativeSporadic.Carrier .Co1 :=
    CFSG.Monster.Existence.Co1Bridge.visQuotEquivCo1
  have : Finite (NativeSporadic.Carrier .Co1) := Finite.of_equiv _ e.toEquiv
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Co1_elementary_three_rank_four
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Co1)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hE hc
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
    CFSG.AGLEmbeddingD2.pRank_visQuot_eq hp (by norm_num)] at h4
  exact h4.trans (CFSG.AGLEmbeddingD2.pRank_Gvis_le_Gmat hp)

end Monster

@[expose] def MonsterThreeRankFour : Prop :=
  ∀ [Finite (CFSGIndex.sporadic .M).Group],
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (CFSGIndex.sporadic .M).Group)

theorem sporadicThreeRankThree_of_monster
    (hM : MonsterThreeRankFour) : SporadicThreeRankThree := by
  intro s _ hrank h4
  have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  have small : s ∈ sporadicsThm3 → ¬ 3 ^ 4 ∣ sporadicOrder s → False := fun hs hn =>
    not_pow_four_dvd_of_carrier s hbr
      (by rw [card_carrier_eq_sporadicOrder hs]; exact hn) h4
  have big : (∃ E : Subgroup (NativeSporadic.Carrier s),
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) → False := fun hE => by
    have := four_le_pRank_of_elem s hbr hE
    omega
  cases s
  case M11 => exact (small (by decide) (by decide)).elim
  case M12 => exact (small (by decide) (by decide)).elim
  case M22 => exact (small (by decide) (by decide)).elim
  case M23 => exact (small (by decide) (by decide)).elim
  case M24 => exact (small (by decide) (by decide)).elim
  case J1 => exact (small (by decide) (by decide)).elim
  case J2 => exact (small (by decide) (by decide)).elim
  case J3 => rfl
  case J4 => exact (small (by decide) (by decide)).elim
  case HS => exact (small (by decide) (by decide)).elim
  case McL => exact (big CFSG.SectionRank.McL_elementary_three_rank_four).elim
  case He => exact (small (by decide) (by decide)).elim
  case Ru => exact (small (by decide) (by decide)).elim
  case Suz => exact (big CFSG.SectionRank.Suz_elementary_three_rank_four).elim
  case ONan => exact (big CFSG.SectionRank.ON_elementary_three_rank_four).elim
  case Co1 => exact (big CFSG.SectionRank.Co1_elementary_three_rank_four).elim
  case Co2 => exact (big CFSG.SectionRank.Co2_elementary_three_rank_four).elim
  case Co3 => exact (big CFSG.SectionRank.Co3_elementary_three_rank_four).elim
  case Fi22 => exact (big CFSG.SectionRank.Fi22_elementary_three_rank_four).elim
  case Fi23 => exact (big CFSG.SectionRank.Fi23_elementary_three_rank_four).elim
  case Fi24Prime => exact (big CFSG.SectionRank.Fi24prime_elementary_three_rank_four).elim
  case HN => exact (big CFSG.SectionRank.HN_elementary_three_rank_four).elim
  case Ly => exact (big CFSG.SectionRank.Ly_elementary_three_rank_four).elim
  case Th => exact (big CFSG.SectionRank.Th_elementary_three_rank_four).elim
  case B => exact (big CFSG.SectionRank.B_elementary_three_rank_four).elim
  case M =>
    have := hM
    omega

theorem monsterThreeRankFour_holds
    : MonsterThreeRankFour := by
  intro _
  have hiso : Nonempty (CFSG.Monster.Generated.Gmat ≃* NativeSporadic.Carrier .M) := by
    haveI : IsSimpleGroup (NativeSporadic.Carrier .M) :=
      CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
    obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
      (T := NativeSporadic.Carrier .M) (MulEquiv.refl _)
    exact ⟨ε.symm⟩
  exact four_le_pRank_of_iso .M CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
    (R := CFSG.Monster.Generated.Gmat) four_le_pRank_Gmat hiso

theorem sporadicThreeRankThree_holds
    : SporadicThreeRankThree :=
  sporadicThreeRankThree_of_monster monsterThreeRankFour_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

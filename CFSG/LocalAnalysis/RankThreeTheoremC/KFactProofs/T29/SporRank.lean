module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal
public import CFSG.RankThree.Asc83Table.Reduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Assembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

section SporRank


open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3 CFSG.Blueprint TauCeti
  CFSG.RankThree.PartOne.F106 CFSG.RankThree.PartOne.Census3

theorem spor_factorization_three
    {s : SporadicName} (hs : s ∈ sporadicsThm3) {k : ℕ}
    (hk : 3 ^ k ∣ sporadicOrder s ∧ ¬ 3 ^ (k + 1) ∣ sporadicOrder s) :
    (Nat.card (NativeSporadic.Carrier s)).factorization 3 = k := by
  rw [card_carrier_eq_sporadicOrder hs]
  refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.factorization_eq_of_pow_dvd
    Nat.prime_three ?_ hk
  intro h0
  exact hk.2 (by rw [h0]; exact dvd_zero _)

theorem spor_pRank_le_two_of_order
    (s : SporadicName) (hs : s ∈ sporadicsThm3)
    (hord : ¬ 3 ^ (2 + 1) ∣ sporadicOrder s)
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* s.Group))
    [Finite (CFSGIndex.sporadic s).Group] :
    CFSG.Open.pRank 3 (⊤ : Subgroup (CFSGIndex.sporadic s).Group) ≤ 2 := by
  obtain ⟨b⟩ := hbr
  have b' : NativeSporadic.Carrier s ≃* (CFSGIndex.sporadic s).Group := b
  haveI : Finite (NativeSporadic.Carrier s) := Finite.of_equiv _ b'.symm.toEquiv
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier s)) ≤ 2 :=
    CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd Nat.prime_three
      (by rw [card_carrier_eq_sporadicOrder hs]; exact hord)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) b'] at h2
  exact h2

theorem spor_pRank_le_two_of_witness
    (s : SporadicName)
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* s.Group))
    (x y : NativeSporadic.Carrier s)
    (hord : (Nat.card (NativeSporadic.Carrier s)).factorization 3 = 3)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hz1 : ⁅x, y⁆ ≠ 1) [Finite (CFSGIndex.sporadic s).Group] :
    CFSG.Open.pRank 3 (⊤ : Subgroup (CFSGIndex.sporadic s).Group) ≤ 2 := by
  obtain ⟨b⟩ := hbr
  have b' : NativeSporadic.Carrier s ≃* (CFSGIndex.sporadic s).Group := b
  haveI : Finite (NativeSporadic.Carrier s) := Finite.of_equiv _ b'.symm.toEquiv
  have h2 : CFSG.pRank 3 (NativeSporadic.Carrier s) = 2 :=
    CFSG.RankThree.Asc83Table.ex27_pRank hx hy hzx hzy hz1 hord
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 (NativeSporadic.Carrier s),
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) b'] at h2
  exact h2.le

theorem spor_pRank_ne_three
    (s : SporadicName) (hs : s ≠ .J3)
    [Finite (CFSGIndex.sporadic s).Group] :
    CFSG.Open.pRank 3 (⊤ : Subgroup (CFSGIndex.sporadic s).Group) ≠ 3 := by
  intro h3
  have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  have big : (∃ E : Subgroup (NativeSporadic.Carrier s),
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) → False := fun hE => by
    have := four_le_pRank_of_elem s hbr hE
    omega
  cases s
  case M11 =>
    have := spor_pRank_le_two_of_order .M11 (by decide) (by decide) hbr
    omega
  case M12 =>
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
    have hord : (Nat.card (NativeSporadic.Carrier .M12)).factorization 3 = 3 :=
      spor_factorization_three (by decide) (by decide)
    have := spor_pRank_le_two_of_witness .M12 hbr x y hord hx hy hzx hzy hz
    omega
  case M22 =>
    have := spor_pRank_le_two_of_order .M22 (by decide) (by decide) hbr
    omega
  case M23 =>
    have := spor_pRank_le_two_of_order .M23 (by decide) (by decide) hbr
    omega
  case M24 =>
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
    have hord : (Nat.card (NativeSporadic.Carrier .M24)).factorization 3 = 3 :=
      spor_factorization_three (by decide) (by decide)
    have := spor_pRank_le_two_of_witness .M24 hbr x y hord hx hy hzx hzy hz
    omega
  case J1 =>
    have := spor_pRank_le_two_of_order .J1 (by decide) (by decide) hbr
    omega
  case J2 =>
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
    have hord : (Nat.card (NativeSporadic.Carrier .J2)).factorization 3 = 3 :=
      spor_factorization_three (by decide) (by decide)
    have := spor_pRank_le_two_of_witness .J2 hbr x y hord hx hy hzx hzy hz
    omega
  case J3 => exact (hs rfl).elim
  case J4 =>
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
    have hord : (Nat.card (NativeSporadic.Carrier .J4)).factorization 3 = 3 :=
      spor_factorization_three (by decide) (by decide)
    have := spor_pRank_le_two_of_witness .J4 hbr x y hord hx hy hzx hzy hz
    omega
  case HS =>
    have := spor_pRank_le_two_of_order .HS (by decide) (by decide) hbr
    omega
  case McL => exact (big CFSG.SectionRank.McL_elementary_three_rank_four).elim
  case He =>
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
    have hord : (Nat.card (NativeSporadic.Carrier .He)).factorization 3 = 3 :=
      spor_factorization_three (by decide) (by decide)
    have := spor_pRank_le_two_of_witness .He hbr x y hord hx hy hzx hzy hz
    omega
  case Ru =>
    obtain ⟨x, y, -, hx, hy, hz, hzx, hzy, -, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
    have hord : (Nat.card (NativeSporadic.Carrier .Ru)).factorization 3 = 3 :=
      spor_factorization_three (by decide) (by decide)
    have := spor_pRank_le_two_of_witness .Ru hbr x y hord hx hy hzx hzy hz
    omega
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
    have hM : ∀ [Finite (CFSGIndex.sporadic SporadicName.M).Group],
        4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (CFSGIndex.sporadic SporadicName.M).Group) :=
      monsterThreeRankFour_holds
    have := hM
    omega

theorem sporadic_three_rank_ne_three
    (s : TauCeti.SporadicName) (hs : s ≠ .J3)
    {A : Type} [Group A] [Finite A]
    (e : A ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    CFSG.Open.pRank 3 (⊤ : Subgroup A) ≠ 3 := by
  intro h3
  haveI : Finite (TauCeti.CFSGIndex.sporadic s).Group := Finite.of_equiv A e.toEquiv
  have h3S : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.sporadic s).Group) = 3 :=
    ((CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).symm).trans h3
  exact spor_pRank_ne_three s hs h3S

end SporRank

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

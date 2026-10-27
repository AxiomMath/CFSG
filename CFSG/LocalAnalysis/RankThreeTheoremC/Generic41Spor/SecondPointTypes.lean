module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointPSL2
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Swap
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Sylow
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Torus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

theorem spt_exists_not_mem_zpowers {p : ℕ} [Fact p.Prime] {K : Type} [Group K] [Finite K]
    {S : Subgroup K} (hS : IsElemAbelian p S) (hcard : Nat.card S = p ^ 2) {t : K} (ht : t ∈ S)
    (ht1 : t ≠ 1) : ∃ b ∈ S, b ∉ zpowers t := by
  by_contra hcon
  push_neg at hcon
  have hle : S ≤ zpowers t := fun b hb => hcon b hb
  have h1 : Nat.card S ≤ Nat.card (zpowers t) := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, orderOf_eq_prime (hS.2 t ht) ht1, hcard] at h1
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have : p * p ≤ p * 1 := by simpa [pow_two] using h1
  have := Nat.le_of_mul_le_mul_left this (by omega)
  omega

theorem spt_movesLines_of_transitive {p : ℕ} [Fact p.Prime] {K : Type} [Group K] [Finite K]
    (hK : SylowIsPlane p K) (htr : NormalizerTransitive p K) : NormalizerMovesLines p K := by
  intro S t ht ht1
  obtain ⟨b, hbS, hb⟩ := spt_exists_not_mem_zpowers (hK S).1 (hK S).2 ht ht1
  have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
  obtain ⟨n, hn, hnt⟩ := htr S t ht ht1 b hbS hb1
  exact ⟨n, hn, hnt ▸ hb⟩

theorem spt_autBound_plane {p : ℕ} [Fact p.Prime] {K : Type} [Group K] [Finite K]
    (hK : SylowIsPlane p K) (hno : NoOuterP p K) (hz : Subgroup.center K = ⊥) :
    ∀ (S : Sylow p K) (A : Subgroup (MulAut K)), IsPGroup p A →
      Nat.card A ∣ Nat.card (S : Subgroup K) := by
  intro S A hA
  rw [(hK S).2]
  exact plane_aut_pgroup_card_dvd hK hno hz A hA

theorem spt_autBound_heis {p : ℕ} [Fact p.Prime] {K : Type} [Group K] [Finite K]
    (hK : SylowIsHeisenberg p K) (hno : NoOuterP p K) (hz : Subgroup.center K = ⊥) :
    ∀ (S : Sylow p K) (A : Subgroup (MulAut K)), IsPGroup p A →
      Nat.card A ∣ Nat.card (S : Subgroup K) := by
  intro S A hA
  rw [(hK S).1]
  exact typeII_aut_pgroup_card_dvd hK hno hz A hA

theorem spt_zin_eq {K : Type} [Group K] (S : Subgroup K) :
    Zin S = S ⊓ Subgroup.centralizer (S : Set K) := by
  ext y
  constructor
  · rintro ⟨⟨z, hz⟩, hzc, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hz, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro h hh
    have := Subgroup.mem_center_iff.mp hzc ⟨h, hh⟩
    exact congrArg Subtype.val this
  · intro hy
    obtain ⟨hyS, hyc⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_map.2 ⟨⟨y, hyS⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.2 fun g => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hyc g g.2)

open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3_sylow_data u3_aut_pgroup_card u3_torus_on_center
  card_inf_centralizer_of_nonabelian_card_p_cube)
open CFSG.LocalAnalysis.RankThreeTheoremC (IsU3Pred)

theorem secondPointFacts_u3 {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {Q : Type} [Group Q] [Finite Q]
    (hQ : ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧
      CFSG.RankThree.PartOne.Census3.IsoLie Q (.twistedA 2 q)) (hz : Subgroup.center Q = ⊥) :
    SecondPointFacts p Q := by
  have hU : IsU3Pred p Q := hQ
  have hheis : SylowIsHeisenberg p Q := by
    intro S
    obtain ⟨hc, hexp, hnc, -⟩ := u3_sylow_data h5 hU S
    refine ⟨hc, ?_, hexp⟩
    by_contra hcon
    push_neg at hcon
    exact hnc (isMulCommutative_iff.2 fun a b => Subtype.ext (hcon a a.2 b b.2))
  refine ⟨?_, Or.inr ⟨hheis, ?_⟩⟩
  · intro S A hA
    rw [(u3_sylow_data h5 hU S).1]
    exact u3_aut_pgroup_card h5 hU A hA
  · intro S z hzZ hz1 w hwZ hw1
    obtain ⟨hc, hexp, hnc, -⟩ := u3_sylow_data h5 hU S
    rw [spt_zin_eq] at hzZ hwZ
    obtain ⟨hzS, hzC⟩ := Subgroup.mem_inf.1 hzZ
    have hZcard := card_inf_centralizer_of_nonabelian_card_p_cube hc hnc
    have hzpow : zpowers z = (S : Subgroup Q) ⊓ Subgroup.centralizer ((S : Subgroup Q) : Set Q) := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzZ) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime (hexp z hzS) hz1, hZcard]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hzpow ▸ hwZ)
    have hkp : ¬ (p : ℤ) ∣ k := by
      rintro ⟨c, rfl⟩
      apply hw1
      rw [← hk, zpow_mul, zpow_natCast, hexp z hzS, one_zpow]
    obtain ⟨n, hn, hnz⟩ := u3_torus_on_center h5 hU S hzS hzC hz1 k hkp
    exact ⟨n, hn, hnz.trans hk⟩

theorem secondPointFacts_tits (hX : TitsFacts) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsTitsType 5 Q) (hz : Subgroup.center Q = ⊥) : SecondPointFacts 5 Q := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsyl := hX.sylow Q hQ
  exact ⟨spt_autBound_plane hsyl (hX.noOuter Q hQ) hz,
    Or.inl ⟨hsyl, spt_movesLines_of_transitive hsyl (hX.trans Q hQ)⟩⟩

theorem secondPointFacts_a10 (hX : A10Facts) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsA10Type 5 Q) (hz : Subgroup.center Q = ⊥) : SecondPointFacts 5 Q := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hsyl := hX.sylow Q hQ
  exact ⟨spt_autBound_plane hsyl (hX.noOuter Q hQ) hz, Or.inl ⟨hsyl, a10_movesLines Q hQ⟩⟩

theorem secondPointFacts_extra {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} {p : ℕ} [Fact p.Prime]
    {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}
    (hX : ExtraFacts Typ p Shape) {Q : Type} [Group Q] [Finite Q] (hQ : Typ p Q)
    (hz : Subgroup.center Q = ⊥) : SecondPointFacts p Q :=
  ⟨spt_autBound_heis (hX.sylow Q hQ) (hX.noOuter Q hQ) hz,
    Or.inr ⟨hX.sylow Q hQ, hX.transCenter Q hQ⟩⟩

theorem secondPointFacts_of_class {p : ℕ} (h5 : 5 ≤ p) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsRankTwoSEGroupE3 p Q) (hz : Subgroup.center Q = ⊥) (hTits : TitsFacts) (hA10 : A10Facts)
    (hMcL : ExtraFacts IsMcLType 5 McLShape) (hJ4 : ExtraFacts IsJ4Type 11 J4Shape) :
    SecondPointFacts p Q := by
  rcases hQ with ⟨hp, ⟨e⟩⟩ | ⟨q, hqp, hqe, hiso⟩ | ⟨rfl, hA | hT | hM⟩ | ⟨rfl, hJ⟩
  · exact secondPointFacts_psl2 h5 ⟨e⟩ hz
  · haveI : Fact p.Prime := ⟨hqp ▸ q.prime_p⟩
    exact secondPointFacts_u3 h5 ⟨q, hqp, hqe, hiso⟩ hz
  · exact secondPointFacts_a10 hA10 ⟨rfl, hA⟩ hz
  · exact secondPointFacts_tits hTits ⟨rfl, hT⟩ hz
  · haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact secondPointFacts_extra hMcL ⟨rfl, hM⟩ hz
  · haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact secondPointFacts_extra hJ4 ⟨rfl, hJ⟩ hz

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

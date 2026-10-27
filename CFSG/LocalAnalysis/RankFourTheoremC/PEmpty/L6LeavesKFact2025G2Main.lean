module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025G2Fact
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley KF2025.G2
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)

namespace KF2025.G2

theorem exists_G2_of_isG2OddIndex {dd : TauCeti.LieTypeIndex} (hd : IsG2OddIndex dd) :
    ∃ q : TauCeti.PrimePower, dd = .G2 q ∧ q.p ≠ 2 := by
  rcases dd with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q |
    q | q | q | q | m | m | m | _
  all_goals first
    | exact ⟨_, rfl, hd⟩
    | (exfalso; simp [IsG2OddIndex] at hd)

section Model


theorem kxSection_of_g2_equiv {A : Type} [Group A] [Finite A] {L S : Subgroup A} {z : A} {p : ℕ}
    {q : TauCeti.PrimePower} (hq2 : q.p ≠ 2) (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (e : ↥L ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.G2 q, hv⟩)
    (hp : p.Prime) (hp2 : p ≠ 2) (hzp : orderOf z = p) (hzL : z ∈ L)
    (hrank : CFSG.Open.pRank p L ≤ 1) (hSL : S ≤ L) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hzS : z ∈ normalizer (S : Set A)) : KxSection z (normalizer (S : Set A) ⊓ L) 3 := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hqpos := q.exponent_pos
  let F := GaloisField q.p q.exponent
  have hFcard : Nat.card F = q.card := by
    rw [GaloisField.card q.p q.exponent (by omega), TauCeti.PrimePower.card_def]
  have hodd : Odd (Nat.card F) := by
    rw [hFcard, TauCeti.PrimePower.card_def]
    exact (q.prime_p.odd_of_ne_two hq2).pow
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hq2 F hFcard
  let eK : ↥L ≃* ↥(adjointGroup .G2 F) :=
    (e.trans b.symm).trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .G2 F)
  haveI := finite_adjointGroup_G2 (F := F) (Finite.one_lt_card)
  have hrank' : CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup .G2 F)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eK,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact hrank
  have hp3 : p ≠ 3 := by
    rintro rfl
    have := two_le_pRank_three_g2 hodd
    omega
  have hp5 := five_le_of_prime hp hp2 hp3
  have ha : NoCentralInvolution (⟨z, hzL⟩ : ↥L) := by
    refine NoCentralInvolution.of_mulEquiv eK (noCentralInvolution_g2 hodd hp hp2 hrank' ?_)
    rw [MulEquiv.orderOf_eq]
    exact (Subgroup.orderOf_coe (⟨z, hzL⟩ : ↥L)).symm.trans hzp
  have hb : TwoRankLeThree ↥L := TwoRankLeThree.of_mulEquiv eK (twoRankLeThree_g2 hodd)
  have hc : SelfCentralizingEight ↥L :=
    SelfCentralizingEight.of_mulEquiv eK (selfCentralizingEight_g2 hodd)
  have hd : 16 ∣ Nat.card ↥L := by
    rw [Nat.card_congr eK.toEquiv]
    exact sixteen_dvd_card_g2 hodd
  exact kxSection_of_facts_ambient hp hp5 hzp hzL hSL hS2 hS1 hzS ha hb hc hd

end Model

end KF2025.G2

section Main


theorem kFact2025G2_holds : KFact2025G2 := by
  intro A _ _ L S z p hcat hp hp2 hzp hzL hrank hSL hS2 hS1 hzS _hcomm
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact (hi : False).elim
  | alternating _ _ => exact (hi : False).elim
  | sporadic _ => exact (hi : False).elim
  | lie v =>
    obtain ⟨dd, hv⟩ := v
    have hd : IsG2OddIndex dd := hi
    obtain ⟨q, rfl, hq2⟩ := KF2025.G2.exists_G2_of_isG2OddIndex hd
    exact KF2025.G2.kxSection_of_g2_equiv hq2 hv e hp hp2 hzp hzL hrank hSL hS2 hS1 hzS

theorem kFact2025_holds : KFact2025 := kFact2025_of_g2 kFact2025G2_holds

end Main

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

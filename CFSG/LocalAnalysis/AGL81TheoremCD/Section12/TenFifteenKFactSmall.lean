module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutPrime
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.KS.Basic
import CFSG.GH74.KGroups.U33
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMOrder

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem card_outer_le_four_of_mulEquiv_alternating {Y : Type} [Group Y] {n : ℕ} (hn : 5 ≤ n)
    (e : Y ≃* alternatingGroup (Fin n)) : Nat.card (Outer Y) ≤ 4 :=
  (Nat.card_congr
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv).trans_le
    (CFSG.RankThree.PartOne.card_outer_alternating_le_four hn)

theorem card_outer_le_two_of_psl_seven {Y : Type} [Group Y] {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.card = 7) (hd : d.1 = .A 1 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : Nat.card (Outer Y) ≤ 2 := by
  obtain ⟨d', hv⟩ := d
  have hd' : d' = .A 1 q := hd
  subst hd'
  have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  have h7 : q.p = 7 ∧ q.exponent = 1 :=
    (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).1 (by simpa using hq)
  rw [h7.1, h7.2] at hm
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ := hm
  have hdvd := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
    (p := 7) (f := 1) (by norm_num) F (by simpa using hcard)).2 Y
    ⟨e'.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩
  have h2 : Nat.card (Outer Y) ∣ 2 := by simpa using hdvd
  exact Nat.le_of_dvd (by norm_num) h2

theorem card_outer_le_two_of_lie_psu_three_three {Y : Type} [Group Y] [IsSimpleGroup Y]
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.card = 3)
    (hd : d.1 = .twistedA 2 q) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Nat.card (Outer Y) ≤ 2 := by
  obtain ⟨d', hv⟩ := d
  have hd' : d' = .twistedA 2 q := hd
  subst hd'
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  have h3 : q.p = 3 ∧ q.exponent = 1 :=
    (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).1 (by simpa using hq)
  rw [h3.1, h3.2] at hm
  have hl := (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mpr hm
  obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hl
  have hY : Nat.card Y = 6048 := by
    rw [Nat.card_congr e'.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
      CFSG.GH74.KGroups.U33.QP_valid.2]
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY]; norm_num)
  have hnab := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.exists_mul_ne_mul_of_isSimpleGroup
    (G := Y) (by rw [hY]; norm_num)
  exact CFSG.AGLEmbedding.LieOut.card_outer_le_two_of_psu_three_three
    (CFSG.RankThree.PartOne.conj_injective_of_center_eq_bot
      (CFSG.RankThree.PartOne.center_eq_bot_of_simple hnab)) hl

theorem card_outer_le_four_of_small {Y : Type} [Group Y] [IsSimpleGroup Y]
    (h : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (Y ≃* alternatingGroup (Fin n))) ∨
      ∃ d : TauCeti.ValidLieTypeIndex,
        ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
          (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (Outer Y) ≤ 4 := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩, ⟨e⟩⟩
  · exact card_outer_le_four_of_mulEquiv_alternating (by omega) e
  · exact (card_outer_le_two_of_psl_seven hq hd e).trans (by norm_num)
  · exact (card_outer_le_two_of_lie_psu_three_three hq hd e).trans (by norm_num)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIMain
public import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3Models
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemG23

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA

theorem transport_E27 {Q H : Type} [Group Q] [Group H] (φ : Q ≃* H)
    (hH : ∃ D : Subgroup H, CFSG.Assembly.IsElemAbelian 3 D ∧ Nat.card D = 27) :
    ∃ E : Subgroup Q, IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  obtain ⟨D, hD, hD27⟩ := hH
  have hD' : IsElemAbelian 3 D := hD
  refine ⟨D.map φ.symm.toMonoidHom, isElemAbelian_map_of_injective φ.symm.injective hD', ?_⟩
  rw [Subgroup.card_map_of_injective φ.symm.injective, hD27]

section G2Certs


theorem lieModel_G2_three_of_iso
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hcard : q.card = 3)
    {Q : Type} [Group Q] (e : Q ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.G2 q, hv⟩) :
    LieModel Q .G2 0 3 1 := by
  have hcard' : q.p ^ q.exponent = 3 := (TauCeti.PrimePower.card_def q).symm.trans hcard
  have hpe : q.p = 3 ∧ q.exponent = 1 :=
    (Nat.Prime.pow_eq_iff Nat.prime_three).1 hcard'
  have hq2 : q.p ≠ 2 := by
    intro h
    have hpos := q.exponent_pos
    obtain ⟨k, hk⟩ : ∃ k, q.exponent = k + 1 := ⟨q.exponent - 1, by omega⟩
    have h2 : (2 : ℕ) ^ (k + 1) = 3 := by
      rw [← hk, ← h]
      exact hcard'
    rw [pow_succ] at h2
    omega
  have h3 : 3 ≤ q.p ^ q.exponent := hcard'.ge
  have hU := CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.g2
    q hv hq2 e
  have hadm : StatedLieAdmissible .G2 0 q.p q.exponent :=
    ⟨q.prime_p, q.exponent_pos, rfl, h3⟩
  have hC : ChevalleyExceptionalModel Q .G2 q.p q.exponent := ⟨hadm, hU⟩
  have hL : LieModel Q .G2 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by simp [chevalleyExceptionalTags], hC⟩)
  rw [hpe.1, hpe.2] at hL
  exact hL

set_option maxHeartbeats 400000 in
theorem cfgIRank_th_three :
    CfgIRankRow 3 S8.Row.th := by
  unfold CfgIRankRow
  intro Q _ _ hcat hcard
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  have hi' : S8.isG2of 3 i := hi
  have hbot : Subgroup.center Q = ⊥ := (Subgroup.eq_bot_iff_card _).2 hcard
  cases i with
  | cyclic p hp => exact False.elim hi'
  | alternating n hn => exact False.elim hi'
  | sporadic s => exact False.elim hi'
  | lie idx =>
    obtain ⟨d, hd⟩ := idx
    cases d with
    | G2 q =>
      have hq : q.card = 3 := hi'
      let f : Q ⧸ Subgroup.center Q ≃* Q :=
        (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
      let eQ : Q ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.G2 q, hd⟩ :=
        f.symm.trans e
      have hL := lieModel_G2_three_of_iso q hd hq eQ
      obtain ⟨ψ⟩ :=
        CFSG.HardMathSupport.Timmesfeld.LieRank.nonempty_mulEquiv_adjointGroup_G2_of_lieModel hL
      let φ : Q ≃* CFSG.RankThree.PartTwo.Census.Carrier.G2Three.R3 :=
        ψ.trans CFSG.RankThree.PartTwo.Census.Carrier.G2Three.adjointEquivR3
      obtain ⟨E, hE, hE27⟩ := transport_E27 φ CFSG.RankThree.PartTwo.Sec4.Item434RemG23.exists_E27_R3
      refine ⟨E, hE, ?_⟩
      rw [hbot, inf_bot_eq, Subgroup.card_bot, hE27]
      norm_num [S8.Row.rank]
    | _ => exact False.elim hi'

end G2Certs

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

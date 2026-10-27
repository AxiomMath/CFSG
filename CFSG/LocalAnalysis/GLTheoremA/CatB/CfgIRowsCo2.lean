module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIRowsG2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA CFSG.GH74.Exceptional

theorem bridge_B2_three {S : Type} [Group S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) (hq : q.card = 3)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩) : Nonempty (S ≃* PSp43) := by
  have hcard' : q.p ^ q.exponent = 3 := (TauCeti.PrimePower.card_def q).symm.trans hq
  have hpe : q.p = 3 ∧ q.exponent = 1 := (Nat.Prime.pow_eq_iff Nat.prime_three).1 hcard'
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  rw [hpe.1, hpe.2] at hm
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card]
    simpa using hK
  let φ : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  exact ⟨e'.trans (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 2 ⊕ Fin 2) φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 2)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ))⟩

theorem exists_B2_of_onLie_three {d : TauCeti.LieTypeIndex}
    (h : (match d with | .B 2 q => q.card = 3 | _ => False)) :
    ∃ q : TauCeti.PrimePower, d = .B 2 q ∧ q.card = 3 := by
  cases d with
  | B r q =>
    rcases r with _ | _ | _ | r
    · exact False.elim h
    · exact False.elim h
    · exact ⟨q, rfl, h⟩
    · exact False.elim h
  | _ => exact False.elim h

theorem cfgIRank_co2_three : CfgIRankRow 3 S8.Row.co2 := by
  unfold CfgIRankRow
  intro Q _ _ hcat hcard
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  have hbot : Subgroup.center Q = ⊥ := (Subgroup.eq_bot_iff_card _).2 hcard
  have hPSp : Nonempty (Q ⧸ Subgroup.center Q ≃* PSp43) := by
    rcases hi with hU | hB
    · exact CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_u4two ⟨i, hU, ⟨e⟩⟩
    · cases i with
      | cyclic p hp => exact False.elim hB
      | alternating n hn => exact False.elim hB
      | sporadic s => exact False.elim hB
      | lie idx =>
        obtain ⟨d, hd⟩ := idx
        obtain ⟨q, rfl, hq⟩ := exists_B2_of_onLie_three hB
        exact bridge_B2_three q hd hq e
  obtain ⟨e2⟩ := hPSp
  let f : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let φ : Q ≃* PSp43 := f.symm.trans e2
  obtain ⟨E, hE, hE27⟩ := transport_E27 φ CFSG.LocalAnalysis.GLTheoremA.CatB.U42.psp43_exists_E27
  refine ⟨E, hE, ?_⟩
  rw [hbot, inf_bot_eq, Subgroup.card_bot, hE27]
  norm_num [S8.Row.rank]

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

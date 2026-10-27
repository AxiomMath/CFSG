module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIMain
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporHN
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporRank
public import CFSG.Sporadic.HNOddCore.Five

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA

theorem exists_elemAbelian_of_le_pRank {G : Type*} [Group G] [Finite G] {p k : ℕ} (hp : 1 < p)
    {H : Subgroup G} (h : k ≤ CFSG.Open.pRank p H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ p ^ k ≤ Nat.card E := by
  classical
  set A := {j | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ j} with hA
  have hne : A.Nonempty := ⟨0, ⊥, bot_le,
    ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩,
    by simp⟩
  have hbdd : BddAbove A := by
    refine ⟨Nat.card G, ?_⟩
    rintro j ⟨E, -, -, hc⟩
    calc j ≤ p ^ j := (Nat.lt_pow_self hp).le
      _ = Nat.card E := hc.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group E
  obtain ⟨E, hEH, hE, hc⟩ := Nat.sSup_mem hne hbdd
  refine ⟨E, hEH, hE, ?_⟩
  rw [hc]
  exact Nat.pow_le_pow_right (by omega) h

theorem factorization_pow_mul {p k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    (p ^ k * m).factorization p = k := by
  have hm0 : m ≠ 0 := fun e => hm (e ▸ dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
    add_zero]

theorem e125_of_witness {S : Type} [Group S] [Finite S] {x : S}
    (hw : CFSG.LocalAnalysis.RankFourTheoremC.RankThreeWitness 5 x)
    (hfac : (Nat.card S).factorization 5 = 6)
    (hC : ¬ 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({x} : Set S))) :
    ∃ E : Subgroup S, IsElemAbelian 5 E ∧ 5 ^ 3 ≤ Nat.card E := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases hw with ⟨P, hP⟩ | ⟨Q', Z', hexp, hZQ, hZc, hZ', hcomm, hcard, hxQ, hxZ⟩ |
    ⟨E, hE, hcard, -⟩
  · exfalso
    apply hC
    have hPc : Nat.card (P : Subgroup S) = 5 ^ 6 := by rw [Sylow.card_eq_multiplicity, hfac]
    rw [← hPc]
    exact Subgroup.card_dvd_of_le hP
  · obtain ⟨E, -, hE, hEc⟩ := exists_elemAbelian_of_le_pRank (by norm_num)
      (CFSG.LocalAnalysis.RankFourTheoremC.three_le_pRank_centralizer_of_extraspecial hexp hZQ
        hZc hZ' hcomm hcard hxQ hxZ)
    exact ⟨E, hE, hEc⟩
  · exact ⟨E, hE, hcard.ge⟩

theorem e125_of_key {S : Type} [Group S] {x : S} (hx : orderOf x = 5) [Finite S]
    (key : CFSG.LocalAnalysis.RankFourTheoremC.SporadicClassWitnessAt .HN 5)
    (hne : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .HN).Group))
    (hfac : (Nat.card S).factorization 5 = 6)
    (hC : ¬ 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({x} : Set S))) :
    ∃ E : Subgroup S, IsElemAbelian 5 E ∧ 5 ^ 3 ≤ Nat.card E :=
  e125_of_witness (key S hne x hx) hfac hC

theorem cfgIRank_m5_of_model {S : Type} [Group S]
    (hE : ∃ E : Subgroup S, IsElemAbelian 5 E ∧ 5 ^ 3 ≤ Nat.card E)
    (hne : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .HN).Group)) :
    CfgIRankRow 5 S8.Row.m5 := by
  obtain ⟨φ⟩ := hne
  intro Q _ _ hcat hZ
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  have hi' : i = TauCeti.CFSGIndex.sporadic .HN := hi
  subst hi'
  have hbot : Subgroup.center Q = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  let eQ : Q ≃* (TauCeti.CFSGIndex.sporadic .HN).Group :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e
  obtain ⟨E, hEel, hEc⟩ := hE
  let ψ : S ≃* Q := φ.trans eQ.symm
  refine ⟨E.map ψ.toMonoidHom, isElemAbelian_map_of_injective ψ.injective hEel, ?_⟩
  rw [hbot, inf_bot_eq, Subgroup.card_bot, mul_one,
    Subgroup.card_map_of_injective ψ.injective]
  exact hEc

section HNCerts


set_option maxHeartbeats 1000000 in
theorem cfgIRank_m5_five : CfgIRankRow 5 S8.Row.m5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have eJ : NativeSporadic.HN ≃* CFSG.Sporadic.HNSchreier.JH := CFSG.Sporadic.HNSchreier.hnEquivJ
  have φ : ↥CFSG.Sporadic.HNSchreier.JH ≃* (TauCeti.CFSGIndex.sporadic .HN).Group :=
    eJ.symm.trans b
  haveI hfin : Finite ↥CFSG.Sporadic.HNSchreier.JH := Finite.of_equiv _ eJ.toEquiv
  obtain ⟨-, -, -, hfo, hCc, -⟩ := CFSG.Sporadic.HNOddCore.ctuc_hn_five_centralizer_perfect_factor
  have hcardJ : Nat.card ↥CFSG.Sporadic.HNSchreier.JH = 5 ^ 6 * 17473978368 := by
    rw [← Nat.card_congr eJ.toEquiv, CFSG.Sporadic.HN.card_HN]
    norm_num
  have hfac : (Nat.card ↥CFSG.Sporadic.HNSchreier.JH).factorization 5 = 6 := by
    rw [hcardJ]; exact factorization_pow_mul Nat.prime_five (by norm_num)
  have hC6 : ¬ 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({CFSG.Sporadic.HNSchreier.fJ} :
      Set ↥CFSG.Sporadic.HNSchreier.JH)) := by
    rw [hCc]; decide
  have hfo' : orderOf CFSG.Sporadic.HNSchreier.fJ = 5 := hfo
  have key : CFSG.LocalAnalysis.RankFourTheoremC.SporadicClassWitnessAt .HN 5 :=
    CFSG.LocalAnalysis.RankFourTheoremC.sporadicClassWitnessAt_HN_five
  have hne : Nonempty (↥CFSG.Sporadic.HNSchreier.JH ≃* (TauCeti.CFSGIndex.sporadic .HN).Group) :=
    ⟨φ⟩
  have h1 := e125_of_key hfo key hne
  have h3 := h1 hfac (fun hd => by rw [hCc] at hd; exact absurd hd (by decide))
  exact cfgIRank_m5_of_model h3 hne

end HNCerts

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

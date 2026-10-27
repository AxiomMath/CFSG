module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestTypeDet
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreExcB
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDetExc
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDetExcMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDetExc
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetExc
public import CFSG.RankThree.PartOne.S12K.OrdRigidL
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Adapters.TauCetiExceptional.BridgeAll
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4

private theorem tag_T_of_markTag (lab : LargeEvenLabel) (h : markTag lab = .trialityD4) :
    lab.tag = .triD4 := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [markTag] at h <;> (try split_ifs at h) <;> simp_all

private theorem lie_of_onLie' {P : TauCeti.LieTypeIndex → Prop} {i : TauCeti.CFSGIndex}
    (h : onLie P i) : ∃ j : TauCeti.ValidLieTypeIndex, i = .lie j ∧ P j.1 := by
  rcases i with _ | _ | j | _
  · exact h.elim
  · exact h.elim
  · exact ⟨j, rfl, h⟩
  · exact h.elim

private theorem index_T {i : TauCeti.CFSGIndex}
    (h : onLie (fun | .trialityD4 _ => True | _ => False) i) : ∃ (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), i = .lie ⟨.trialityD4 q, hv⟩ := by
  obtain ⟨j, rfl, hj⟩ := lie_of_onLie' h
  obtain ⟨d, hv⟩ := j
  split at hj
  next q heq => subst heq; exact ⟨q, hv, rfl⟩
  next => exact hj.elim

theorem evenLieOrder_eq_ordTrialityD4 {t : StatedLieTag} {n f g : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (hg : 1 ≤ g)
    (h : CFSG.SeitzReduction.F4Pilot.evenLieOrder t n f = ordTrialityD4 (2 ^ g)) :
    t = .trialityD4 := by
  have hf : 1 ≤ f := hadm.2.1
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    have hm : 1 ≤ m := by have := hadm.2.2.1; omega
    have h' : ordA m (2 ^ f) = ordTrialityD4 (2 ^ g) := by simpa [CFSG.SeitzReduction.F4Pilot.evenLieOrder] using h
    rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm2
    · exact absurd h'.symm (CFSG.RankThree.PartOne.S12K.ordTrialityD4_ne_ordA_one hg hf)
    · exact absurd h'.symm (CFSG.SeitzReduction.LinearPilot.ordTrialityD4_ne_ordA hg hm2 hf)
  | PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have h' : ordTwistedA (n - 1) (2 ^ f) = ordTrialityD4 (2 ^ g) := h
    exact absurd h'.symm (CFSG.Timmesfeld.Orders.ordTrialityD4_ne_ordTwistedA hg (by omega) hf)
  | PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have h' : ordBC n (2 ^ f) = ordTrialityD4 (2 ^ g) := h
    exact absurd h'.symm (CFSG.SeitzReduction.SymplecticPilot.ordTrialityD4_ne_ordBC hg hn hf)
  | POmegaOdd => exact absurd rfl hadm.2.2.2
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    have h' : ordD n (2 ^ f) = ordTrialityD4 (2 ^ g) := h
    exact absurd h'.symm (CFSG.SeitzReduction.OmegaPilot.ordTrialityD4_ne_ordD hg hn hf)
  | POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    have h' : ordTwistedD n (2 ^ f) = ordTrialityD4 (2 ^ g) := h
    exact absurd h'.symm (CFSG.SeitzReduction.OmegaPilot.ordTrialityD4_ne_ordTwistedD hg hn hf)
  | G2 => exact absurd h (CFSG.StandardType.NbrInnerMore.ordG2_ne_ordTrialityD4 hf hg)
  | F4 => exact absurd h.symm (CFSG.StandardType.MpTypeDet.ordTrialityD4_ne_ordF4 hg hf)
  | E6 => exact absurd h.symm (CFSG.StandardType.MpTypeDet.ordTrialityD4_ne_ordE6 hg hf)
  | E7 => exact absurd h.symm (CFSG.SeitzReduction.E8Pilot.ordTrialityD4_ne_ordE7 hg hf)
  | E8 => exact absurd h.symm (CFSG.StandardType.MpTypeDet.ordTrialityD4_ne_ordE8 hg hf)
  | twistedE6 =>
    exact absurd h.symm (CFSG.StandardType.MpTypeDet.ordTrialityD4_ne_ordTwistedE6 hg hf)
  | trialityD4 => rfl
  | twistedB2 => exact absurd h (CFSG.StandardType.NbrInnerMore.ordSuzuki_ne_ordTrialityD4 hf hg)
  | twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  | twistedF4 =>
    exact absurd h.symm (CFSG.StandardType.NbrInnerMore.ordTrialityD4_ne_ordTwistedF4 hg hf)
  | Tits =>
    exact absurd h.symm (evenLieOrder_ne_ordTits (t := .trialityD4) (n := 0) (f := g)
      ⟨Nat.prime_two, hg, rfl⟩ (by decide))

section Certs


theorem tri_odd_data {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (hp : q.p ≠ 2) {S : Type} [Group S]
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    LieModel S .trialityD4 0 q.p q.exponent ∧ 3 ^ 20 ≤ Nat.card S := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hto : 0 < (CFSG.Blueprint.Chevalley.TwistTag.D4).order := by decide
  have hKc : Nat.card (GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order)) =
      (q.p ^ q.exponent) ^ (CFSG.Blueprint.Chevalley.TwistTag.D4).order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' hto.ne'), pow_mul]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q hv hp
    (GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order))
    (by rw [hKc, TauCeti.PrimePower.card_def]) (iterateFrobenius _ q.p q.exponent)
    (fun x => by rw [iterateFrobenius_def, TauCeti.PrimePower.card_def])
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order), inferInstance,
      inferInstance, hKc, iterateFrobenius _ q.p q.exponent,
      fun x => by rw [iterateFrobenius_def], ⟨e.trans b.symm⟩⟩
  have hodd : CFSG.Blueprint.LieModel S .trialityD4 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hC⟩)
  refine ⟨hodd, ?_⟩
  have hadm := CFSG.Blueprint.LieModel.admissible hodd
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hcard := (hO S .trialityD4 0 q.p q.exponent hadm hodd).2.1
  have hp3 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have hQ : 3 ≤ q.p ^ q.exponent := le_trans hp3 (Nat.le_self_pow q.exponent_pos.ne' _)
  have hNS : Nat.card S = (q.p ^ q.exponent) ^ 12 * ((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
      ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1) := by
    simpa [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
      CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] using hcard
  rw [hNS]
  set Q := q.p ^ q.exponent with hQdef
  have h6 : 1 ≤ Q ^ 6 - 1 := by
    have : 2 ≤ Q ^ 6 := le_trans (by omega) (Nat.pow_le_pow_left hQ 6)
    omega
  have h2 : 1 ≤ Q ^ 2 - 1 := by
    have : 2 ≤ Q ^ 2 := le_trans (by omega) (Nat.pow_le_pow_left hQ 2)
    omega
  have h1 : 3 ^ 20 ≤ Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) :=
    calc 3 ^ 20 ≤ Q ^ 20 := Nat.pow_le_pow_left hQ 20
      _ = Q ^ 12 * Q ^ 8 := by ring
      _ ≤ Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) := Nat.mul_le_mul_left _ (by omega)
  calc 3 ^ 20 ≤ Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) := h1
    _ = Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) * 1 * 1 := by ring
    _ ≤ Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ h6) h2

theorem tag_triD4_of_isTD4 {lab : LargeEvenLabel} {R S : Type} [Group R] [Group S]
    (hM : MarkedModel lab R)
    (hS : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)) (e : S ≃* R) :
    lab.tag = .triD4 := by
  obtain ⟨i, hi, ⟨eS⟩⟩ := hS
  obtain ⟨q, hv, rfl⟩ := index_T hi
  by_cases hp2 : q.p = 2
  · have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
    have hS3 : LieModel S .trialityD4 0 2 q.exponent :=
      Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
        ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
        CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge hB.trialityD4 q hv hp2 eS⟩)
    have hR3 : LieModel R .trialityD4 0 2 q.exponent := lieModel_of_mulEquiv' e hS3
    have hcR3 : Nat.card R = ordTrialityD4 (2 ^ q.exponent) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hR3
    have hprof := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTrialityD4' q.exponent_pos
    by_cases hb : lab.tag = .B2der
    · have h360 := ggMarkedModel_card_b2der hb hM
      refine absurd ?_ (hprof.ne_of_ne (r := 45) (a := 3) (by decide) (by omega))
      rw [← hcR3, h360]
      norm_num
    by_cases hg : lab.tag = .G2der
    · have h6048 := card_markedModel_g2der hg hM
      refine absurd ?_ (hprof.ne_of_ne (r := 189) (a := 5) (by decide) (by omega))
      rw [← hcR3, h6048]
      norm_num
    by_cases ht : lab.tag = .twF4der
    · have hT := card_markedModel_twF4der ht hM
      refine absurd ?_ (hprof.ne_of_ne (r := 3 ^ 3 * 5 ^ 2 * 13) (a := 11) tits_odd (by omega))
      rw [← hcR3, hT, ordTits_eq]
    have hY := lieModel_of_markedModel (markChar_eq_two_of_ne hb hg) hM
    have hc1 := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hY
    exact tag_T_of_markTag lab (evenLieOrder_eq_ordTrialityD4
      (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hY) q.exponent_pos
      (hc1.symm.trans hcR3))
  · exfalso
    obtain ⟨hodd, hbig⟩ := tri_odd_data hv hp2 eS
    have hbigR : 3 ^ 20 ≤ Nat.card R := by rwa [Nat.card_congr e.toEquiv] at hbig
    have hadm := CFSG.Blueprint.LieModel.admissible hodd
    have hoddR : OddLieType R :=
      ⟨.trialityD4, 0, q.p, q.exponent, q.prime_p, hp2, hadm, lieModel_of_mulEquiv' e hodd⟩
    by_cases hb : lab.tag = .B2der
    · have := ggMarkedModel_card_b2der hb hM
      norm_num at hbigR
      omega
    by_cases hg : lab.tag = .G2der
    · have := card_markedModel_g2der hg hM
      norm_num at hbigR
      omega
    by_cases ht : lab.tag = .twF4der
    · have := card_markedModel_twF4der ht hM
      rw [ordTits_eq] at this
      norm_num at hbigR
      omega
    have hY := lieModel_of_markedModel (markChar_eq_two_of_ne hb hg) hM
    have hc1 := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hY
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType_of_ne_Tits hY
      (markTag_ne_Tits ht) hoddR with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2, h3] at hc1
      have : CFSG.SeitzReduction.F4Pilot.evenLieOrder .PSL 2 2 = 60 := by decide
      norm_num at hbigR
      omega
    · rw [h1, h2, h3] at hc1
      have : CFSG.SeitzReduction.F4Pilot.evenLieOrder .PSL 3 1 = 168 := by decide
      norm_num at hbigR
      omega
    · rw [h1, h2, h3] at hc1
      have : CFSG.SeitzReduction.F4Pilot.evenLieOrder .PSU 4 1 = 25920 := by decide
      norm_num at hbigR
      omega

end Certs

end MI

end CFSG.LocalAnalysis.GLTheoremA

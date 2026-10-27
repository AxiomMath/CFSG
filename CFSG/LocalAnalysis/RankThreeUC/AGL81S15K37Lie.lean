module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Setup
public import CFSG.LieType.SeitzGeneration.QuasiHigh5E6CoverTw
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Rest

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LieType.Seitz (seitzHyperGamma)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)
open CFSG.RankThree.PartTwo.Sec4.Census (IsThreeCenterCover)

section Unitary

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormD)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)


theorem seitzHyperGamma_eq_top_unitary_three {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {m : ℕ} {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA m q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA m q, hv⟩).Group)
    (hq : 3 ∣ q.card + 1) (hq2 : q.card ≠ 2) {E : Subgroup (MulAut K)}
    (h8 : m = 2 → q.card = 8 → E ≤ (MulAut.conj : K →* MulAut K).range)
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  obtain ⟨hℓ, -, hn3, hne, Kf, _, hU, ⟨θ'⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv e)
  haveI := hU.finite
  haveI : Fact q.p.Prime := ⟨hℓ⟩
  haveI : CharP Kf q.p := hU.charP
  have hqcard : q.p ^ q.exponent = q.card := (TauCeti.PrimePower.card_def q).symm
  have hpq1 : 3 ∣ q.p ^ q.exponent + 1 := hqcard ▸ hq
  have hq2' : q.p ^ q.exponent ≠ 2 := hqcard ▸ hq2
  have hpq : 3 ≠ q.p := by
    intro h3
    have h3' : 3 ∣ q.p ^ q.exponent := h3 ▸ dvd_pow_self 3 q.exponent_pos.ne'
    omega
  have hq4 : Even (m + 1) → 4 ≤ q.p ^ q.exponent := by
    intro _
    have h2 : 2 ≤ q.p ^ q.exponent :=
      le_trans hℓ.two_le (Nat.le_self_pow q.exponent_pos.ne' q.p)
    have h3 : q.p ^ q.exponent ≠ 3 := fun h3 => by rw [h3] at hpq1; omega
    omega
  by_cases hD : E.map (QuasiHigh2.modelAut θ') ≤ primeFormD hU (idGram Kf (m + 1))
  · exact QuasiHigh5.seitzHyperGamma_eq_top_unitary_diag hperf hU hn3 hq2' Nat.prime_three
      (by norm_num) hpq1 hq4 θ' hE hcard hD
  · refine QuasiHigh5.seitzHyperGamma_eq_top_unitary_field hperf hU hn3 hne Nat.prime_three
      (by norm_num) hpq hq4 ?_ θ' hE hcard hD
    intro hm3 h8'
    exact hD (QuasiHigh5.map_modelAut_le_primeFormD_of_inner hU θ'
      (h8 (by omega) (by rw [← hqcard, h8']; norm_num)))

end Unitary

section E6


theorem seitzHyperGamma_eq_top_E6_three {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {d : TauCeti.ValidLieTypeIndex}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) {q : TauCeti.PrimePower}
    (hdq : d.1 = .E6 q) (hpd : 3 ≠ d.1.characteristic) (hq : 3 ∣ q.card - 1)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) :
    seitzHyperGamma 3 E = ⊤ := by
  have hD2 : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 := by
    rw [hdq]
    simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
  have hcardq : 2 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' q.p)
  have hqmod : q.card % 3 = 1 := by omega
  have hcardĒ : Nat.card (coverImage e E) = 3 ^ 2 := card_coverImage hperf e E ▸ hcard
  have hgen := QuasiHigh5E6Cover.uniSeitzPlanes_E6_three_one d 3 Nat.prime_three (by norm_num)
    hpd hD2 _ (isElemAbelian_coverImage e hE) hcardĒ ⟨rfl, ⟨q, hdq, hqmod⟩⟩
  have hr : Nat.Prime d.1.characteristic := by
    rw [hdq, TauCeti.LieTypeIndex.characteristic_E6]
    exact q.prime_p
  exact seitzHyperGamma_eq_top_of_uniPlaneGen hperf e Nat.prime_three hr (fun h => hpd h.symm) hE
    hcard hgen

theorem seitzHyperGamma_eq_top_twE6_inner {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {d : TauCeti.ValidLieTypeIndex}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) {q : TauCeti.PrimePower}
    (hdq : d.1 = .twistedE6 q) (hpd : 3 ≠ d.1.characteristic) (hq : 3 ∣ q.card + 1)
    (hq2 : q.card ≠ 2) {E : Subgroup (MulAut K)}
    (hin : E ≤ (MulAut.conj : K →* MulAut K).range) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) : seitzHyperGamma 3 E = ⊤ := by
  have hD2 : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 := by
    rw [hdq]
    simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
  have hqmod : q.card % 3 = 2 := by omega
  have hEĒ := isElemAbelian_coverImage e hE
  have hcardĒ : Nat.card (coverImage e E) = 3 ^ 2 := card_coverImage hperf e E ▸ hcard
  have hinĒ : InnerPlane d 3 (coverImage e E) := coverImage_le_range_conj e hin
  have hgen : Inputs2311c.UniPlaneGen d.1.characteristic (coverImage e E) := by
    by_cases hn : NormalizesRSubgroup d (coverImage e E)
    · exact Inputs2311c.uniSeitzPlanes_excParabolic d 3 Nat.prime_three (by norm_num) hpd hD2 _
        hEĒ hcardĒ ⟨hinĒ, Or.inr (Or.inr ⟨q, hdq⟩), hn⟩
    · exact QuasiHigh5E6Cover.twE6ThreeOpenInner_holds d 3 Nat.prime_three (by norm_num) hpd hD2
        _ hEĒ hcardĒ ⟨hinĒ, rfl, ⟨q, hdq, hqmod, hq2⟩, hn⟩
  have hr : Nat.Prime d.1.characteristic := by
    rw [hdq, TauCeti.LieTypeIndex.characteristic_twistedE6]
    exact q.prime_p
  exact seitzHyperGamma_eq_top_of_uniPlaneGen hperf e Nat.prime_three hr (fun h => hpd h.symm) hE
    hcard hgen

end E6

section Lie


theorem K37Setting.false_of_lie (hSR : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {X : Type} [Group X] [Finite X] {K E S : Subgroup X} (h : K37Setting X K E S)
    (d : TauCeti.ValidLieTypeIndex) (hd3 : d.1.characteristic ≠ 3)
    (hd : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hO : ¬ K37Open K E) (hL34 : ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type ↥K)
    (hexc : ¬ ((∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q) ∨ d.1 = .tits)) :
    False := by
  obtain ⟨e⟩ := hd
  apply h.seitzHyperGamma_ne_top
  have hpd : 3 ≠ d.1.characteristic := fun h3 => hd3 h3.symm
  have hperf : commutator ↥K = ⊤ := Group.isPerfect_def.mp h.quasi.1
  have hE := h.isElemAbelian_autIm
  have hcard := h.card_autIm
  by_cases hz : 3 ∣ Nat.card (Subgroup.center ↥K)
  · have hci := QuasiHigh.coverIndex_of_dvd_card_center hGA Nat.prime_three (by norm_num)
      ⟨hperf, h.quasi.2.1⟩ d e hpd hz
    have hcov : IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group := ⟨h.quasi, hz, ⟨e⟩⟩
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A m q =>
      exact QuasiHigh5.seitzHyperGamma_eq_top_linear Nat.prime_three (by norm_num) hperf e
        (by simpa using hpd) hci
        (fun h34 => hL34 ⟨_, ⟨q, h34.2.2, congrArg (TauCeti.LieTypeIndex.A · q) h34.2.1⟩, ⟨e⟩⟩)
        hE hcard
    | twistedA m q =>
      refine seitzHyperGamma_eq_top_unitary_three hperf e hci.2
        (fun h2 => hO (Or.inr (Or.inl ⟨_, hcov, m, q, rfl, Or.inl h2⟩))) (fun hm h8 => ?_) hE hcard
      by_contra hn
      exact hO (Or.inr (Or.inl ⟨_, hcov, m, q, rfl, Or.inr ⟨hm, h8, hn⟩⟩))
    | E6 q => exact seitzHyperGamma_eq_top_E6_three hperf e rfl hpd hci.2 hE hcard
    | twistedE6 q =>
      have hq2 : q.card ≠ 2 := fun h2 => hO (Or.inl ⟨_, hcov, q, rfl, Or.inl h2⟩)
      have hin : autIm E K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range := by
        by_contra hn
        exact hO (Or.inl ⟨_, hcov, q, rfl, Or.inr hn⟩)
      exact seitzHyperGamma_eq_top_twE6_inner hperf e rfl hpd hci.2 hq2 hin hE hcard
    | _ => exact False.elim hci
  · have hZ : Subgroup.center ↥K = ⊥ := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rcases h.isPGroup_center.card_eq_or_dvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd h3 hz
    refine InputsSeitz3.seitzHyperGamma_eq_top_of_plane hSR Nat.prime_three (by norm_num) hZ d e hpd
      (fun hx => ?_) hE hcard
    rcases hx with ⟨-, h1 | ⟨q, hp, he, hdq⟩ | h3 | ⟨q, hp, he, hB3 | hB4⟩ | h5⟩ | ⟨h35, -⟩
    · exact hexc (Or.inl h1)
    · exact hL34 ⟨d, ⟨q, by rw [TauCeti.PrimePower.card_def, hp, he]; norm_num, hdq⟩, ⟨e⟩⟩
    · exact hO (Or.inr (Or.inr (Or.inl ⟨d, h3, ⟨e⟩⟩)))
    · exact hexc (Or.inr (Or.inl ⟨q, hp, he, hB3⟩))
    · exact hO (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, ⟨q, hp, he, hB4⟩, ⟨e⟩⟩))))
    · exact hexc (Or.inr (Or.inr h5))
    · omega

end Lie

end CFSG.LocalAnalysis.RankThreeUC.S15.K37

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
import CFSG.LocalAnalysis.GL83PartI.I_24_3.List
import CFSG.Quasithin.Vol2.Ch12Sec6P31WXMult
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerPair
import CFSG.Adapters.StatedPSLTwoNine
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
import CFSG.Models.Blueprint
import CFSG.Alternating.Multipliers.Main
import CFSG.Sporadic.Bridge.J4Surj
import CFSG.Sporadic.Presentation.McLExact
import CFSG.Sporadic.Recognition.McLMultiplierCert
import CFSG.Sporadic.Recognition.HeMultiplier
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverSporadic
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ReeMain
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

open CFSG
open CFSG.LocalAnalysis.RankThreeTheoremC (IsNineFourIndex NineFourListGroup)


section Alternating

variable {p : ℕ} {K : Type} [Group K] [Finite K]

private theorem false_of_alternating_six (hK : CFSG.IsQuasisimple K) {n : ℕ} (hn : n = 6)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.alternating n (by omega)).Group)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hqZ : ¬ 3 ∣ Nat.card (Subgroup.center K)) : False := by
  subst hn
  have hdvd := GL83.I243.CoverList.card_center_dvd_alternating
    (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput) hK (by norm_num) e
  rw [if_pos (Or.inl rfl)] at hdvd
  have hp3 : p = 3 :=
    GL83.I243.CoverList.eq_three_of_dvd_twelve hp hp2 (hpZ.trans hdvd |>.trans (by norm_num))
  exact hqZ (hp3 ▸ hpZ)

private theorem false_of_alternating_ten (hK : CFSG.IsQuasisimple K) {n : ℕ} (hn : n = 10)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.alternating n (by omega)).Group)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpZ : p ∣ Nat.card (Subgroup.center K)) : False := by
  subst hn
  have hdvd := GL83.I243.CoverList.card_center_dvd_alternating
    (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput) hK (by norm_num) e
  rw [if_neg (by omega)] at hdvd
  have hp2' : p = 2 :=
    (Nat.dvd_prime Nat.prime_two).1 (hpZ.trans hdvd) |>.resolve_left hp.ne_one
  exact hp2 hp2'

end Alternating

section Linear

variable {q p : ℕ} {K : Type} [Group K] [Finite K]

private theorem false_of_linTwo_nine (hK : CFSG.IsQuasisimple K)
    {Q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.A 1 Q).Valid}
    (hQp : Q.p = q) (hQexp : 2 ≤ Q.exponent) (h9 : Q.card = 9)
    (hcard : Q.card = Q.p ^ Q.exponent)
    (hclass : CFSG.Open.StatedClassicalModel
      (TauCeti.CFSGIndex.lie ⟨.A 1 Q, hv⟩).Group .PSL 2 Q.p Q.exponent)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 Q, hv⟩).Group)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hqZ : ¬ q ∣ Nat.card (Subgroup.center K)) : False := by
  have hQp3 : Q.p = 3 := by
    have h9' : Q.p ^ Q.exponent = 9 := by
      rw [← hcard]
      exact h9
    have hdvd : Q.p ∣ 3 ^ 2 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at h9'
      exact h9' ▸ dvd_pow_self Q.p (by omega)
    exact (Nat.dvd_prime Nat.prime_three).1
      (Q.prime_p.dvd_of_dvd_pow hdvd) |>.resolve_left Q.prime_p.ne_one
  have hq3 : q = 3 := hQp.symm.trans hQp3
  subst q
  have hexp : Q.exponent = 2 := by
    have hpq : 3 ^ Q.exponent = 3 ^ 2 := by
      have hc := hcard
      rw [h9, hQp3] at hc
      rw [← hc]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpq
  rw [hQp3, hexp] at hclass
  obtain ⟨eA⟩ :=
    CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine hclass
  rw [hQp3] at hqZ
  exact false_of_alternating_six hK rfl (e.trans eA) hp hp2 hpZ hqZ

private theorem false_of_linTwo_ne_nine (hK : CFSG.IsQuasisimple K)
    {Q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.A 1 Q).Valid}
    (hQp : Q.p = q) (hQexp : 2 ≤ Q.exponent) (h9 : Q.card ≠ 9)
    (hcard : Q.card = Q.p ^ Q.exponent)
    (eP : (TauCeti.CFSGIndex.lie ⟨.A 1 Q, hv⟩).Group ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField Q.p Q.exponent))
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 Q, hv⟩).Group)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hq2 : q ≠ 2) : False := by
  have hQodd : Q.p ≠ 2 := by rw [hQp]; exact hq2
  have hcard9 : Q.card ≠ 9 := h9
  have hQcard5 : 5 ≤ Q.card := by
    have h3 : 3 ≤ Q.p := by
      have h2 := Q.prime_p.two_le
      omega
    have h9le : 9 ≤ Q.card := by
      rw [hcard]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ Q.p ^ 2 := Nat.pow_le_pow_left h3 2
        _ ≤ Q.p ^ Q.exponent := Nat.pow_le_pow_right Q.prime_p.pos hQexp
    omega
  haveI : Fintype (GaloisField Q.p Q.exponent) := Fintype.ofFinite _
  have hk5 : 5 ≤ Fintype.card (GaloisField Q.p Q.exponent) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', ← hcard]
    exact hQcard5
  have hk9 : Fintype.card (GaloisField Q.p Q.exponent) ≠ 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', ← hcard]
    exact hcard9
  obtain ⟨-, ⟨hM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_two_hopfMultiplier_of_mulEquiv
      (k := GaloisField Q.p Q.exponent) hk5 hk9 (e.trans eP).symm
  have hdvd := CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess hK.1
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) =
      Nat.gcd 2 (Fintype.card (GaloisField Q.p Q.exponent) - 1) := by
    rw [Nat.card_congr hM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [hcardM] at hdvd
  have hp2' : p = 2 :=
    (Nat.dvd_prime Nat.prime_two).1
      (hpZ.trans (hdvd.trans (Nat.gcd_dvd_left _ _))) |>.resolve_left hp.ne_one
  exact hp2 hp2'

private theorem false_of_linTwo (hq : q.Prime) (hq2 : q ≠ 2) (hK : CFSG.IsQuasisimple K)
    {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ Q : TauCeti.PrimePower, Q.p = q ∧ 2 ≤ Q.exponent ∧ d.1 = .A 1 Q)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hqZ : ¬ q ∣ Nat.card (Subgroup.center K)) : False := by
  obtain ⟨Q, hQp, hQexp, hQd⟩ := hd
  obtain ⟨d1, hv⟩ := d
  change d1 = .A 1 Q at hQd
  subst hQd
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hm := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA 1 Q hv
  have hclass : CFSG.Open.StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.A 1 Q, hv⟩).Group
      .PSL 2 Q.p Q.exponent :=
    (CFSG.Models.LieModel.toBlueprint (by decide) hm).statedClassicalModel (by decide)
  obtain ⟨eP⟩ :=
    CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField
      (TauCeti.CFSGIndex.lie ⟨.A 1 Q, hv⟩).Group 2 Q.p Q.exponent hclass
  have hcard : Q.card = Q.p ^ Q.exponent := TauCeti.PrimePower.card_def Q
  by_cases h9 : Q.card = 9
  · exact false_of_linTwo_nine hK hQp hQexp h9 hcard hclass e hp hp2 hpZ hqZ
  · exact false_of_linTwo_ne_nine hK hQp hQexp h9 hcard eP e hp hp2 hpZ hq2

end Linear

section Unitary

variable {q p : ℕ} {K : Type} [Group K] [Finite K]

private theorem unitary_case (hK : CFSG.IsQuasisimple K) {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ Q : TauCeti.PrimePower, Q.p = q ∧ d.1 = .twistedA 2 Q)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hp : p.Prime) (hpZ : p ∣ Nat.card (Subgroup.center K)) :
    p = 3 ∧ Nat.card (Subgroup.center K) = 3 ∧
      (∃ (d' : TauCeti.ValidLieTypeIndex) (Q' : TauCeti.PrimePower),
        d'.1 = .twistedA 2 Q' ∧ Q'.p = q ∧ 3 ∣ Q'.card + 1 ∧
          Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d').Group)) := by
  obtain ⟨Q, hQp, hQd⟩ := hd
  obtain ⟨d1, hv⟩ := d
  change d1 = .twistedA 2 Q at hQd
  subst hQd
  have hclass : CFSG.Open.StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.twistedA 2 Q, hv⟩).Group
      .PSU 3 Q.p Q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 Q hv (MulEquiv.refl _)
  have hmodel : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 3 Q.p Q.exponent :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hclass
  have hdvd := CFSG.SectionRank.QTK.CentreFact.LayerPair.card_center_dvd_gcd_psu_three hK hmodel
  have hpdvd3 : p ∣ 3 := hpZ.trans (hdvd.trans (Nat.gcd_dvd_left 3 _))
  have hp3 : p = 3 :=
    (Nat.dvd_prime Nat.prime_three).1 hpdvd3 |>.resolve_left hp.ne_one
  have h3Z : 3 ∣ Nat.card (Subgroup.center K) := hp3 ▸ hpZ
  have hZ3 : Nat.card (Subgroup.center K) = 3 := by
    have hZ3' : 3 ∣ Nat.card (Subgroup.center K) := h3Z
    have hZ3'' : Nat.card (Subgroup.center K) ∣ 3 := hdvd.trans (Nat.gcd_dvd_left 3 _)
    exact (Nat.dvd_antisymm hZ3' hZ3'').symm
  have h3Q : 3 ∣ Q.card + 1 := by
    have h3g : 3 ∣ Nat.gcd 3 (Q.p ^ Q.exponent + 1) := h3Z.trans hdvd
    rw [TauCeti.PrimePower.card_def]
    exact (Nat.dvd_gcd_iff.mp h3g).2
  exact ⟨hp3, hZ3, ⟨⟨.twistedA 2 Q, hv⟩, Q, rfl, hQp, h3Q, ⟨e⟩⟩⟩

end Unitary

section LinThree

variable {q p : ℕ} {K : Type} [Group K] [Finite K]

private theorem false_of_linThree_four (hK : CFSG.IsQuasisimple K) (hq3 : q = 3)
    {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower} (hQp2 : Q.p = 2)
    (hQexp : Q.exponent = 2) (hQd : d.1 = .A 2 Q)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hodd : Odd (Nat.card (Subgroup.center K)))
    (hp : p.Prime) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hqZ : ¬ q ∣ Nat.card (Subgroup.center K)) : False := by
  obtain ⟨d1, hv⟩ := d
  change d1 = .A 2 Q at hQd
  subst hQd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA 2 Q hv
  have hclass : CFSG.Open.StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.A 2 Q, hv⟩).Group
      .PSL 3 2 2 := by
    simpa [hQp2, hQexp] using
      (CFSG.Models.LieModel.toBlueprint (by decide) hm).statedClassicalModel (by decide)
  obtain ⟨eP⟩ :=
    CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField
      (TauCeti.CFSGIndex.lie ⟨.A 2 Q, hv⟩).Group 3 2 2 hclass
  have eK : K ⧸ Subgroup.center K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2) := e.trans eP
  obtain ⟨-, ⟨hM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_three_four_hopfMultiplier
  have hdvd := CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess hK.1 eK
  have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2))) = 48 := by
    rw [Nat.card_congr hM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
      Nat.card_prod, Nat.card_zmod]
    norm_num
  rw [hcardM] at hdvd
  have hodd2 : Nat.Coprime (Nat.card (Subgroup.center K)) 2 := by
    rw [Nat.coprime_two_right]
    exact hodd
  have h48 : Nat.card (Subgroup.center K) ∣ 2 ^ 4 * 3 := by
    simpa using hdvd
  have h3Z : Nat.card (Subgroup.center K) ∣ 3 :=
    (Nat.Coprime.pow_right 4 hodd2).dvd_of_dvd_mul_left h48
  have hp3 : p = 3 :=
    (Nat.dvd_prime Nat.prime_three).1 (hpZ.trans h3Z) |>.resolve_left hp.ne_one
  exact (hq3 ▸ hqZ) (hp3 ▸ hpZ)

end LinThree

section Suzuki

variable {p : ℕ} {K : Type} [Group K] [Finite K]

private theorem false_of_suzuki (hK : CFSG.IsQuasisimple K)
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hodd : Odd (Nat.card (Subgroup.center K)))
    (hp : p.Prime) (hpZ : p ∣ Nat.card (Subgroup.center K)) : False := by
  obtain ⟨d1, hv⟩ := d
  change d1 = .suzuki 2 at hd
  subst hd
  have hSz : CFSG.Blueprint.SuzukiModel (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group 2 5 := by
    simpa using CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index 2 hv
  obtain ⟨a, ha, ⟨eS⟩⟩ :=
    CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hSz
  let eS' : K ⧸ Subgroup.center K ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    e.trans eS
  let π : K →* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    eS'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  haveI : Group.IsPerfect K := hK.1
  have hπ : Function.Surjective π :=
    eS'.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : π.ker = Subgroup.center K :=
    CFSG.SectionRank.center_eq_ker_of_mulEquiv eS'
  have hZ : Subgroup.center K = ⊥ := by
    have h := CFSG.SectionRank.suzuki_perfect_odd_cover_trivial a ha π hπ
      (by rw [hker]) (by rw [hker]; exact hodd)
    rwa [hker] at h
  have hcard : Nat.card (Subgroup.center K) = 1 := by rw [hZ, Subgroup.card_bot]
  rw [hcard] at hpZ
  exact hp.not_dvd_one hpZ

end Suzuki

section Tits

variable {p : ℕ} {K : Type} [Group K] [Finite K]

private theorem false_of_tits (hK : CFSG.IsQuasisimple K)
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .tits)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hodd : Odd (Nat.card (Subgroup.center K)))
    (hp : p.Prime) (hpZ : p ∣ Nat.card (Subgroup.center K)) : False := by
  obtain ⟨d1, hv⟩ := d
  change d1 = .tits at hd
  subst hd
  have hmodel : CFSG.Blueprint.ReeTitsModel
      (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group .Tits 2 1 :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨F, hF, hFfin, hFchar, hFcard, ⟨eT⟩⟩ :=
    CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hmodel
  letI : Field F := hF
  letI : Finite F := hFfin
  letI : CharP F CFSG.LieType.Ree.ReeTag.F4.prime := hFchar
  let eT' : K ⧸ Subgroup.center K ≃*
      ↥(commutator (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 F 0)) :=
    e.trans eT
  let π : K →*
      ↥(commutator (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 F 0)) :=
    eT'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  haveI : Group.IsPerfect K := hK.1
  have hπ : Function.Surjective π :=
    eT'.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker : π.ker = Subgroup.center K :=
    CFSG.SectionRank.center_eq_ker_of_mulEquiv eT'
  have hZ : Subgroup.center K = ⊥ := by
    have h := CFSG.SectionRank.Tits_perfect_odd_cover_trivial (K := F) hFcard π hπ
      (by rw [hker]) (by rw [hker]; exact hodd)
    rwa [hker] at h
  have hcard : Nat.card (Subgroup.center K) = 1 := by rw [hZ, Subgroup.card_bot]
  rw [hcard] at hpZ
  exact hp.not_dvd_one hpZ

end Tits

section Ree

variable {p : ℕ} {K : Type} [Group K] [Finite K]

private theorem false_of_ree (hK : CFSG.IsQuasisimple K) {m : ℕ}
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .reeG2 m)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hp : p.Prime) (hpZ : p ∣ Nat.card (Subgroup.center K)) : False := by
  obtain ⟨d1, hv⟩ := d
  change d1 = .reeG2 m at hd
  subst hd
  have hmodel : CFSG.Blueprint.ReeTitsModel
      (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group .twistedG2 3 (2 * m + 1) :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨MulEquiv.refl _⟩⟩
  have hmodel' : CFSG.Blueprint.ReeTitsModel
      (K ⧸ Subgroup.center K) .twistedG2 3 (2 * m + 1) :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e hmodel
  have hm1 : 1 ≤ 2 * m + 1 := by omega
  have hF : CFSG.GH74.GLS.Stage2.Signalizer.Odd87.FRee (K ⧸ Subgroup.center K) :=
    ⟨2 * m + 1, hm1, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hmodel'⟩))⟩
  have hZ : Nat.card (Subgroup.center K) = 1 :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.ree_card_center_eq_one hK hF
  rw [hZ] at hpZ
  exact hp.not_dvd_one hpZ

end Ree

section Sporadic

variable {q p : ℕ} {K : Type} [Group K] [Finite K]

private theorem false_of_M11 (hK : CFSG.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .M11).Group)
    (hodd : Odd (Nat.card (Subgroup.center K)))
    (hp : p.Prime) (hpZ : p ∣ Nat.card (Subgroup.center K)) : False := by
  obtain ⟨eB⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  let e' : K ⧸ Subgroup.center K ≃* TauCeti.SporadicName.M11.Group := e
  let eN : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.M11 := e'.trans eB.symm
  let π : K →* CFSG.Blueprint.NativeSporadic.M11 := CFSG.GH74.Generic.centralQuotientMap eN
  haveI : Group.IsPerfect K := hK.1
  have hπ : Function.Surjective π := CFSG.GH74.Generic.centralQuotientMap_surjective eN
  have hker : π.ker = Subgroup.center K := CFSG.GH74.Generic.centralQuotientMap_ker eN
  have hZ : Subgroup.center K = ⊥ := by
    have h := CFSG.QuasithinUnique.Ch1.M11_perfect_odd_cover_trivial π hπ
      (by rw [hker]) (by rw [hker]; exact hodd)
    rwa [hker] at h
  have hcard : Nat.card (Subgroup.center K) = 1 := by rw [hZ, Subgroup.card_bot]
  rw [hcard] at hpZ
  exact hp.not_dvd_one hpZ

private theorem false_of_J4 (hK : CFSG.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .J4).Group)
    (hodd : Odd (Nat.card (Subgroup.center K)))
    (hp : p.Prime) (hpZ : p ∣ Nat.card (Subgroup.center K)) : False := by
  obtain ⟨eB⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  let e' : K ⧸ Subgroup.center K ≃* TauCeti.SporadicName.J4.Group := e
  have eN : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.J4 := e'.trans eB.symm
  let π : K →* CFSG.Blueprint.NativeSporadic.J4 :=
    MonoidHom.mk' (fun x => eN (QuotientGroup.mk x)) (by intro a b; simp)
  haveI : Group.IsPerfect K := hK.1
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨z, rfl⟩ := eN.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨x, rfl⟩
  have hker : π.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h y
      have h' : eN (QuotientGroup.mk x) = 1 := h
      rw [MulEquiv.map_eq_one_iff] at h'
      have hx : x ∈ Subgroup.center K := by rwa [← QuotientGroup.eq_one_iff]
      exact Subgroup.mem_center_iff.1 hx y
    · intro h
      have hx : x ∈ Subgroup.center K := Subgroup.mem_center_iff.2 h
      have h1 : QuotientGroup.mk x = (1 : K ⧸ Subgroup.center K) :=
        (QuotientGroup.eq_one_iff x).2 hx
      change eN (QuotientGroup.mk x) = 1
      rw [h1, map_one]
  have hZ : Subgroup.center K = ⊥ := by
    have h := CFSG.SectionRank.J4_perfect_odd_cover_trivial CFSG.SectionRank.j4OrderHyp
      π hπ (by rw [hker]) (by rw [hker]; exact hodd)
    rwa [hker] at h
  have hcard : Nat.card (Subgroup.center K) = 1 := by rw [hZ, Subgroup.card_bot]
  rw [hcard] at hpZ
  exact hp.not_dvd_one hpZ

private theorem McL_case (hq5 : q = 5) (hK : CFSG.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .McL).Group)
    (hp : p.Prime) (hpZ : p ∣ Nat.card (Subgroup.center K)) :
    p = 3 ∧ Nat.card (Subgroup.center K) = 3 ∧
      ((∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower),
          d.1 = .twistedA 2 Q ∧ Q.p = q ∧ 3 ∣ Q.card + 1 ∧
            Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
        (q = 5 ∧
          Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .McL).Group))) := by
  obtain ⟨eB⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  let e' : K ⧸ Subgroup.center K ≃* TauCeti.SporadicName.McL.Group := e
  have eN : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.McL := e'.trans eB.symm
  have hdvd : Nat.card (Subgroup.center K) ∣ 3 :=
    CFSG.Sporadic.Recognition.McLMultiplier.card_center_dvd_three_of_certificate hK.1 eN
  have hp3 : p = 3 :=
    (Nat.dvd_prime Nat.prime_three).1 (hpZ.trans hdvd) |>.resolve_left hp.ne_one
  have h3Z : 3 ∣ Nat.card (Subgroup.center K) := hp3 ▸ hpZ
  have hZ3 : Nat.card (Subgroup.center K) = 3 :=
    (Nat.dvd_antisymm h3Z hdvd).symm
  exact ⟨hp3, hZ3, Or.inr ⟨hq5, ⟨e⟩⟩⟩

end Sporadic

section LinTwoEight

variable {p : ℕ} {K : Type} [Group K] [Finite K]

private theorem false_of_linTwo_eight (hK : CFSG.IsQuasisimple K)
    {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower} (hQp2 : Q.p = 2)
    (hQexp3 : Q.exponent = 3) (hQd : d.1 = .A 1 Q)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hp : p.Prime) (hpZ : p ∣ Nat.card (Subgroup.center K)) : False := by
  obtain ⟨d1, hv⟩ := d
  change d1 = .A 1 Q at hQd
  subst hQd
  have hm := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA 1 Q hv
  have hclass : CFSG.Open.StatedClassicalModel
      (TauCeti.CFSGIndex.lie ⟨.A 1 Q, hv⟩).Group .PSL 2 2 3 := by
    simpa [hQp2, hQexp3] using
      (CFSG.Models.LieModel.toBlueprint (by decide) hm).statedClassicalModel (by decide)
  have hclass' : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 3 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hclass
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.Quasithin.H13.P31X.center_eq_bot_of_isPSL_two_even hK (by norm_num) hclass'
  have hcard : Nat.card (Subgroup.center K) = 1 := by rw [hZ, Subgroup.card_bot]
  rw [hcard] at hpZ
  exact hp.not_dvd_one hpZ

end LinTwoEight

theorem centralLift_cases {q p : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hlist : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q (K ⧸ Subgroup.center K))
    (hodd : Odd (Nat.card (Subgroup.center K))) (hqZ : ¬ q ∣ Nat.card (Subgroup.center K))
    (hpZ : p ∣ Nat.card (Subgroup.center K)) :
    p = 3 ∧ Nat.card (Subgroup.center K) = 3 ∧
      ((∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), d.1 = .twistedA 2 Q ∧
          Q.p = q ∧ 3 ∣ Q.card + 1 ∧
          Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
        (q = 5 ∧
          Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .McL).Group))) := by
  obtain ⟨-, i, hi, ⟨e⟩⟩ := hlist
  cases i with
  | cyclic n hn => exact hi.elim
  | alternating n hn =>
      rcases hi with ⟨hq3, hn6⟩ | ⟨hq5, hn10⟩
      · subst q
        subst hn6
        exact (false_of_alternating_six hK rfl e hp hp2 hpZ hqZ).elim
      · subst q
        subst hn10
        exact (false_of_alternating_ten hK rfl e hp hp2 hpZ).elim
  | sporadic s =>
      rcases hi with ⟨hq3, hs⟩ | ⟨hq5, hs⟩ | ⟨hq11, hs⟩
      · subst s
        exact (false_of_M11 hK e hodd hp hpZ).elim
      · subst s
        exact McL_case hq5 hK e hp hpZ
      · subst s
        exact (false_of_J4 hK e hodd hp hpZ).elim
  | lie d =>
      rcases hi with h1 | h2 | h3 | h4 | h5
      · rcases h1 with ⟨Q, hQp, hQexp, hQd⟩
        exact (false_of_linTwo hq hq2 hK ⟨Q, hQp, hQexp, hQd⟩ e hp hp2 hpZ hqZ).elim
      · rcases h2 with ⟨Q, hQp, hQd⟩
        obtain ⟨hp3, hZ3, hU⟩ := unitary_case hK ⟨Q, hQp, hQd⟩ e hp hpZ
        exact ⟨hp3, hZ3, Or.inl hU⟩
      · rcases h3 with ⟨hq3, m, hm⟩
        exact (false_of_ree hK hm e hp hpZ).elim
      · rcases h4 with ⟨hq3, h4a | h4b⟩
        · rcases h4a with ⟨Q, hQp2, hQexp3, hQd⟩
          exact (false_of_linTwo_eight hK hQp2 hQexp3 hQd e hp hpZ).elim
        · rcases h4b with ⟨Q, hQp2, hQexp2, hQd⟩
          exact (false_of_linThree_four hK hq3 hQp2 hQexp2 hQd e hodd hp hpZ hqZ).elim
      · rcases h5 with ⟨hq5, h5a | h5b⟩
        · exact (false_of_suzuki hK h5a e hodd hp hpZ).elim
        · exact (false_of_tits hK h5b e hodd hp hpZ).elim

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcReeData
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Ree
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.RankThree.PartTwo.Sec8.Item82Res2ProofSLThree
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
public import CFSG.ClassicalInvolution.RouteD.TWRExoticArith
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXS
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification
open CFSG.Assembly (LargeEvenInduces LargeEvenMarking)
open CFSG.LieType.Ree

theorem l154_even_padicVal_ordTrialityD4 (Q : TauCeti.PrimePower) :
    Even (padicValNat 2 (ordTrialityD4 Q.card)) := by
  by_cases h2 : Q.p = 2
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, h2]
    rw [CFSG.ClassicalInvolution.RouteD.TWR.padicValNat_ordTrialityD4 hq Q.exponent_pos]
    exact ⟨Q.exponent * 6, by ring⟩
  · have hodd : Odd Q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact (Q.prime_p.odd_of_ne_two h2).pow
    have h3 : 3 ≤ Q.card := by
      rw [TauCeti.PrimePower.card_def]
      calc 3 ≤ Q.p := by
            have := Q.prime_p.two_le
            omega
        _ = Q.p ^ 1 := (pow_one _).symm
        _ ≤ Q.p ^ Q.exponent := Nat.pow_le_pow_right Q.prime_p.pos Q.exponent_pos
    rw [CFSG.ComponentClassification.GSThmB.P211X.v2_ordTrialityD4 hodd h3]
    exact even_two_mul _

theorem l154_exists_trialityD4 {S : Type} [Group S]
    (h : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)) :
    ∃ (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 Q).Valid),
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 Q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | trialityD4 Q => exact ⟨Q, hv, ⟨e⟩⟩
    | _ => exact hi.elim

theorem l154_padicVal_quot_unitarySU {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ f) ^ 2) :
    padicValNat 2 (Nat.card (↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F 3) ⧸
      Subgroup.center ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F 3))) = 3 * f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv := CFSG.RankThree.PartTwo.Sec8.Item82Proof.padicValNat_card_statedSU_three
    (m := f) (by omega) hF
  have hZ3 := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three hF hf).2
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F 3))
  have hz : padicValNat 2 (Nat.card ↥(Subgroup.center
      ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F 3))) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have := h.trans hZ3
    omega
  have h1 : padicValNat 2 (Nat.card ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F 3)) =
      3 * f := hv
  rw [hmul, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hz, add_zero] at h1
  exact h1

section Quot


theorem l154_ree_T_eq_centralizer_three {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {s : ReeTag.F4.reeGamma K a}
    (hs : orderOf s = 3) {T : Subgroup (ReeTag.F4.reeGamma K a)}
    (hT : GLAPComponent 3
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s)) T) :
    T = Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a)) := by
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hC : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a))) :=
    CFSG.RankThree.PartTwo.Sec19.SimsC198.reeGamma_isQuasisimple_centralizer ha hK s hs
  rw [CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj] at hT
  exact l154_eq_of_subnormal_quasisimple hT.2.1
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hC)
    (glaPComponent_perfect hT)
    (CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hT)

theorem l154_ree_padicVal_centralizer_quot {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {s : ReeTag.F4.reeGamma K a}
    (hs : orderOf s = 3) :
    padicValNat 2 (Nat.card (↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a))) ⧸
      Subgroup.center ↥(Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a))))) =
      3 * (2 * a + 1) := by
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨E⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK s hs
  have hF : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  haveI : Finite ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (2 * a + 1)
      (GaloisField 2 (2 * (2 * a + 1))) 3) := Finite.of_equiv _ E.toEquiv
  rw [Nat.card_congr (QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)).toEquiv]
  exact l154_padicVal_quot_unitarySU (by omega) hF

end Quot

section TD4


theorem l154_false_of_ree_td4 {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x y : Ω}
    {J : Subgroup Ω} (hSn : S.Normal) (hqS : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore 3 ↥S = ⊥) (hc : IsChevSimple 2 (PSimple 3 S))
    (hQ : catalogIs (PSimple 3 S) l154ExcRee) (hxp : x ^ 3 = 1) (hyp : y ^ 3 = 1)
    (hxy : x * y = y * x) (hInn : InnDiagOn 3 (Subgroup.zpowers x) S) (hF : FieldOn 3 y S)
    (hJ : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (hcm : ¬ CentMod 3 S x) (hT : IsTD4 3 J) :
    False := by
  obtain ⟨a, K, _, _, _, θ, s, φ, ha, hK, hs, -, -, -, hindx, hindy⟩ :=
    l154_ree_setup Nat.prime_three (by norm_num) hSn hqS hSp hc hQ hxp hyp hxy hInn hF hcm
  have hxN := l154_mem_normalizer_of_normal hSn x
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  have hTc := l154_JImage_glaPComponent Nat.prime_three hxp hxN hJ θ (MulAut.conj s) hindx
  have hTeq := l154_ree_T_eq_centralizer_three ha hK hs hTc
  have hqT : CFSG.Open.IsQuasisimple ↥(l154JImage 3 S J θ) := by
    rw [hTeq]
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple
      (CFSG.RankThree.PartTwo.Sec19.SimsC198.reeGamma_isQuasisimple_centralizer ha hK s hs)
  obtain ⟨-, e₀, -, -⟩ := l154_JImage_equiv Nat.prime_three hSp hJ hJS hJy θ φ hindy hqT
  obtain ⟨Q, hv, ⟨f⟩⟩ := l154_exists_trialityD4 hT
  have h1 : Nat.card (↥(l154JImage 3 S J θ) ⧸ Subgroup.center ↥(l154JImage 3 S J θ)) =
      ordTrialityD4 Q.card := by
    rw [Nat.card_congr (e₀.symm.trans f).toEquiv,
      CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_trialityD4_carrier Q hv]
  have h2 : padicValNat 2 (Nat.card (↥(l154JImage 3 S J θ) ⧸
      Subgroup.center ↥(l154JImage 3 S J θ))) = 3 * (2 * a + 1) := by
    generalize l154JImage 3 S J θ = T at hTeq ⊢
    subst hTeq
    exact l154_ree_padicVal_centralizer_quot ha hK hs
  rw [h1] at h2
  obtain ⟨r, hr⟩ := l154_even_padicVal_ordTrialityD4 Q
  omega

end TD4

end CFSG.LocalAnalysis.GLTheoremA.K155X

end

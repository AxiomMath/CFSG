module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3
public import CFSG.RankThree.PerfectCover.HopfCentralCovers
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LieType.Steinberg.CentralExt.PSLAlternating
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.LieType.SteinbergBRSemidirectSL2
public import CFSG.LieType.HighestRoot.CentTrialityThree
public import CFSG.GH74.Generic.Context
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.GH74.Generic.Shapes
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3M

open CFSG CFSG.Open CFSG.RankThree.PerfectCover CFSG.Blueprint
open CFSG.LieType.Steinberg.CentralExt

variable {L X : Type} [Group L] [Group X] [Finite L]

omit [Finite L] in
theorem natCard_center_dvd (hL : CFSG.IsQuasisimple L) (e : L ⧸ Subgroup.center L ≃* X) :
    Nat.card ↥(Subgroup.center L) ∣ Nat.card (griessHopfMultiplier X) := by
  let q := centralQuotientMap e
  have hq : Function.Surjective q := centralQuotientMap_surjective e
  have hk : q.ker = Subgroup.center L := centralQuotientMap_ker e
  let : Group.IsPerfect L := hL.1
  let ψ : griessHopfMultiplier X →* q.ker :=
    (hopfMultiplierToKer q hq hk.le).comp (hopfMultiplierEquivGriess X).toMonoidHom
  have hψ : Function.Surjective ψ :=
    (hopfMultiplierToKer_surjective q hq hk.le).comp (hopfMultiplierEquivGriess X).surjective
  have h := Subgroup.card_dvd_of_surjective hψ
  rw [hk] at h
  exact h

theorem center_eq_bot_of_odd (hL : CFSG.IsQuasisimple L) (e : L ⧸ Subgroup.center L ≃* X)
    (h2 : IsPGroup 2 ↥(Subgroup.center L)) (hodd : Odd (Nat.card (griessHopfMultiplier X))) :
    Subgroup.center L = ⊥ := by
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have h := natCard_center_dvd hL e
  rw [hk] at h
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat h)) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem natCard_multiplicative_zmod (m : ℕ) : Nat.card (Multiplicative (ZMod m)) = m := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem odd_natCard_hopf_psl3 {p f : ℕ} (h : LieModel X .PSL 3 p f) (hp2 : p ≠ 2) :
    Odd (Nat.card (griessHopfMultiplier X)) := by
  obtain ⟨hp, hf, F, _, _, hF, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data h
  have : Fintype F := Fintype.ofFinite F
  have hodd : Odd (Fintype.card F) := by
    rw [Fintype.card_eq_nat_card, hF]
    exact (hp.odd_of_ne_two hp2).pow
  have h3 : 3 ≤ Fintype.card F := by
    rw [Fintype.card_eq_nat_card, hF]
    have h1 : 3 ≤ p := by have := hp.two_le; omega
    exact h1.trans (Nat.le_self_pow (by omega) p)
  have h34 : ¬(3 = 3 ∧ Fintype.card F = 4) := fun h4 => by
    rw [h4.2] at hodd
    exact absurd hodd (by decide)
  obtain ⟨-, ⟨eM⟩⟩ := SLClosed.psl_hopfMultiplier_of_three_le (k := F) (n := 3) le_rfl h3 h34
  let e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
  have hcard : Nat.card (griessHopfMultiplier X) = Nat.gcd 3 (Fintype.card F - 1) := by
    rw [Nat.card_congr ((griessHopfMultiplierCongr e).trans eM).toEquiv,
      natCard_multiplicative_zmod]
  rw [hcard]
  exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)

theorem odd_natCard_hopf_psu3
    {p f : ℕ} (h : LieModel X .PSU 3 p f) (hp2 : p ≠ 2) :
    Odd (Nat.card (griessHopfMultiplier X)) := by
  obtain ⟨hp, hf, F, _, _, hF, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data h
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hF
  have hq : ((3 : ℕ), p ^ f) ≠ (3, 2) := by
    intro h2
    have h2' : p ^ f = 2 := (Prod.mk.inj h2).2
    have : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    rw [h2'] at this
    exact absurd this (by decide)
  obtain ⟨-, ⟨eM⟩⟩ := SUOdd.psu_odd_hopfMultiplier hF hf le_rfl (by decide) hq
  have hcard : Nat.card (griessHopfMultiplier X) = Nat.gcd 3 (p ^ f + 1) := by
    rw [Nat.card_congr ((griessHopfMultiplierCongr e₀).trans eM).toEquiv,
      natCard_multiplicative_zmod]
  rw [hcard]
  exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)

theorem natCard_sylow_two_of_card {M : Type} [Group M] [Finite M]
    (hM : Nat.card M = 2 ∨ Nat.card M = 6) (S : Sylow 2 M) : Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity]
  rcases hM with h | h <;> rw [h]
  · rw [Nat.Prime.factorization_self Nat.prime_two, pow_one]
  · have e : (6 : ℕ) = 2 * 3 := by norm_num
    rw [e, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero, pow_one]

section L2


omit [Finite L] in
theorem natCard_hopf_psl2 {F : Type} [Field F] [Fintype F] (hodd : Odd (Fintype.card F))
    (h5 : 5 ≤ Fintype.card F) :
    Nat.card (griessHopfMultiplier (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = 2 ∨
      Nat.card (griessHopfMultiplier (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = 6 := by
  by_cases h9 : Fintype.card F = 9
  · right
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let φ : F ≃+* GaloisField 3 2 := CFSG.ClassicalModels.finiteFieldEquivGaloisField F 3 2
      (by norm_num) (by rw [← Fintype.card_eq_nat_card, h9]; norm_num)
    obtain ⟨-, ⟨eM⟩⟩ := SLClosed.psl_two_nine_hopfMultiplier
    rw [Nat.card_congr ((griessHopfMultiplierCongr
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))).trans eM).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
  · left
    obtain ⟨-, ⟨eM⟩⟩ := SL2Closed.psl_two_hopfMultiplier (k := F) h5 h9
    rw [Nat.card_congr eM.toEquiv, natCard_multiplicative_zmod]
    obtain ⟨m, hm⟩ := hodd
    have e1 : Fintype.card F - 1 = 2 * m := by omega
    rw [e1, Nat.gcd_mul_right_right]

theorem center_eq_bot_of_psl2 (hL : CFSG.IsQuasisimple L) (e : L ⧸ Subgroup.center L ≃* X)
    {p f : ℕ} (h : LieModel X .PSL 2 p f) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (h2 : IsPGroup 2 ↥(Subgroup.center L)) {x : L} (hx : x * x = 1)
    (hxc : x ∉ Subgroup.center L) : Subgroup.center L = ⊥ := by
  obtain ⟨hp, hf, F, _, _, hF, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data h
  have : Fintype F := Fintype.ofFinite F
  let eP : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hodd : Odd (Fintype.card F) := by
    rw [Fintype.card_eq_nat_card, hF]
    exact (hp.odd_of_ne_two hp2).pow
  have h5' : 5 ≤ Fintype.card F := by rw [Fintype.card_eq_nat_card, hF]; exact h5
  have hM : Nat.card (griessHopfMultiplier X) = 2 ∨ Nat.card (griessHopfMultiplier X) = 6 := by
    rw [Nat.card_congr (griessHopfMultiplierCongr eP).toEquiv]
    exact natCard_hopf_psl2 hodd h5'
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hdvd := natCard_center_dvd hL e
  rw [hk] at hdvd
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have h4 : 4 ∣ 2 ^ k := by
      have : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      simpa using this
    rcases hM with hM | hM <;> rw [hM] at hdvd <;> have := h4.trans hdvd <;> omega
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  · exfalso
    let q := centralQuotientMap e
    have hq : Function.Surjective q := centralQuotientMap_surjective e
    let : Group.IsPerfect L := hL.1
    let : Finite X := finite_of_surjective_monoidHom q hq
    let : Group.IsPerfect X := isPerfect_of_quasisimple_quotient hL e
    let : Finite (hopfMultiplier X) := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
    let : Finite (griessHopfMultiplier X) :=
      Finite.of_equiv (hopfMultiplier X) (hopfMultiplierEquivGriess X).symm.toEquiv
    have hchar : ringChar F ≠ 2 := fun hc => by
      have h0 := FiniteField.even_card_iff_char_two.mp hc
      obtain ⟨m, hm⟩ := hodd
      omega
    have hSyl : ∀ S : Sylow 2 (griessHopfMultiplier X), Nat.card S = 2 :=
      natCard_sylow_two_of_card hM
    have hL' : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le
        (by rw [← Fintype.card_eq_nat_card]; omega)
    have hc' := CFSG.LieType.SteinbergBR.card_center_SL2_eq_two hchar
    obtain ⟨φ⟩ := (hopf_central_cover_consequences X).2 hSyl L
      (Matrix.SpecialLinearGroup (Fin 2) F) hL hL' (by rw [hk, pow_one]) hc' ⟨e⟩ ⟨eP.symm⟩
    have hx1 : x ≠ 1 := fun h1 => hxc (h1 ▸ Subgroup.one_mem _)
    have hφx : φ x ^ 2 = 1 := by rw [sq, ← map_mul, hx, map_one]
    have hφx1 : φ x ≠ 1 := fun h1 => hx1 (φ.injective (h1.trans (map_one φ).symm))
    have hneg := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq (Ring.two_ne_zero hchar) (φ x)
      hφx hφx1
    apply hxc
    rw [Subgroup.mem_center_iff]
    intro g
    apply φ.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, hneg, mul_neg, mul_one, neg_mul, one_mul]

end L2

end CFSG.ClassicalInvolution.Q3.TL4.E3S3M

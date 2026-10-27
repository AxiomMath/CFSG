module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagChev
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestField
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Models.Blueprint
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Bridge.Catalogue
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate16026
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.Models.Transport
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate9124

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10

private theorem fieldOrder_unitary {K : Type} [Field K] [Finite K] {d n : ℕ}
    (h : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hφ : φ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :
    φ ^ (2 * n) = 1 := by
  obtain ⟨σ, hσ⟩ := RecipeFieldSU.congr_field_eq h hd hφ
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality Nat.prime_two
      (by omega) hK'
  have hσm : σ ^ (2 * n) = 1 := hcard ▸ pow_card_eq_one'
  apply (MulAut.congr (InndiagSU.projEquiv h hd)).injective
  rw [map_pow, hσ, ← map_pow, hσm, map_one, map_one]

private theorem fo_linear {d n : ℕ} {Q : CFSG.Assembly.LargeEvenRawCont} (hn : 1 ≤ n)
    (hraw : LargeEvenRecipeLinear d (2 ^ n) Q)
    (h3 : ∀ (S : Type) [Group S] (I F : Set (MulAut S)), Q S I F → ∃ f ∈ F, orderOf f = 3) :
    3 ∣ n := by
  obtain ⟨K, _, _, hK, hQK⟩ := hraw
  obtain ⟨f, hf, hord⟩ := h3 _ _ _ hQK
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one (NbrLangRest.pow_eq_one_of_mem_field_linear hn hK hf)

private theorem fo_linear_sq {n : ℕ} {Q : CFSG.Assembly.LargeEvenRawCont} (hn : 1 ≤ n)
    (hraw : LargeEvenRecipeLinear 2 ((2 ^ n) ^ 2) Q)
    (h3 : ∀ (S : Type) [Group S] (I F : Set (MulAut S)), Q S I F → ∃ f ∈ F, orderOf f = 3) :
    3 ∣ 2 * n := by
  obtain ⟨K, _, _, hK, hQK⟩ := hraw
  obtain ⟨f, hf, hord⟩ := h3 _ _ _ hQK
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one (NbrLangRest.pow_eq_one_of_mem_field_linear (by omega) hK' hf)

private theorem fo_unitary {d n : ℕ} {Q : CFSG.Assembly.LargeEvenRawCont} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hraw : LargeEvenRecipeUnitary d (2 ^ n) Q)
    (h3 : ∀ (S : Type) [Group S] (I F : Set (MulAut S)), Q S I F → ∃ f ∈ F, orderOf f = 3) :
    3 ∣ 2 * n := by
  obtain ⟨K, _, _, hK, hQK⟩ := hraw
  obtain ⟨f, hf, hord⟩ := h3 _ _ _ hQK
  have hUFD : LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one (fieldOrder_unitary hUFD hd hn hK hf)

private theorem fo_B2der {Q : CFSG.Assembly.LargeEvenRawCont} (hraw : LargeEvenRecipeSymplectic 2 2 true Q)
    (h3 : ∀ (S : Type) [Group S] (I F : Set (MulAut S)), Q S I F → ∃ f ∈ F, orderOf f = 3) :
    False := by
  obtain ⟨K, _, _, hK, hQK⟩ := hraw
  obtain ⟨f, hf, hord⟩ := h3 _ _ _ hQK
  rw [matFieldImage_eq_one_of_card_two hK _ hf, orderOf_one] at hord
  exact absurd hord (by norm_num)

private theorem fo_G2der {Q : CFSG.Assembly.LargeEvenRawCont} (hraw : LargeEvenRecipeG2Derived Q)
    (h3 : ∀ (S : Type) [Group S] (I F : Set (MulAut S)), Q S I F → ∃ f ∈ F, orderOf f = 3) :
    False := by
  obtain ⟨K, _, _, hK, hQK⟩ := hraw
  obtain ⟨f, hf, hord⟩ := h3 _ _ _ hQK
  rw [chevFieldImage_eq_one_of_card_two hK _ hf, orderOf_one] at hord
  exact absurd hord (by norm_num)

private theorem fo_twF4der {Q : CFSG.Assembly.LargeEvenRawCont} (hraw : LargeEvenRecipeTwF4Inherited 0 Q)
    (h3 : ∀ (S : Type) [Group S] (I F : Set (MulAut S)), Q S I F → ∃ f ∈ F, orderOf f = 3) :
    False := by
  obtain ⟨K, _, _, hK, hQK⟩ := hraw
  obtain ⟨f, hf, hord⟩ := h3 _ _ _ hQK
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  rw [chevFieldImage_eq_one_of_card_two hK2 _ hf, orderOf_one] at hord
  exact absurd hord (by norm_num)

private theorem two_pow_mod_nine {m : ℕ} (h : 3 ∣ m) : 2 ^ m % 9 = 1 ∨ 2 ^ m % 9 = 8 := by
  have key : ∀ k : ℕ, 8 ^ k % 9 = 1 ∨ 8 ^ k % 9 = 8 := by
    intro k
    induction k with
    | zero => left; rfl
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h' | h' <;> rw [h'] <;> norm_num
  obtain ⟨k, rfl⟩ := h
  have hk : 2 ^ (3 * k) = 8 ^ k := by rw [pow_mul]; norm_num
  rw [hk]
  exact key k

private theorem div_PSL3 {lab : LargeEvenLabel} {Q : CFSG.Assembly.LargeEvenRawCont}
    (hl : LargeEvenInLambda2 lab) (hraw : CFSG.Assembly.LargeEvenRawDatum lab Q)
    (h3 : ∀ (S : Type) [Group S] (I F : Set (MulAut S)), Q S I F → ∃ f ∈ F, orderOf f = 3)
    (t1 : markTag lab = .PSL) (t2 : markRank lab = 3) : 3 ∣ markDeg lab := by
  obtain ⟨tg, r, nn⟩ := lab
  obtain ⟨hn, -⟩ := hl
  change 1 ≤ nn at hn
  cases tg
  all_goals first
    | exact fo_linear hn hraw h3
    | (exfalso
       simp only [markTag, markRank] at t1 t2
       (try split_ifs at t1 t2) <;> simp_all)

private theorem div_PSU3 {lab : LargeEvenLabel} {Q : CFSG.Assembly.LargeEvenRawCont}
    (hl : LargeEvenInLambda2 lab) (hraw : CFSG.Assembly.LargeEvenRawDatum lab Q)
    (h3 : ∀ (S : Type) [Group S] (I F : Set (MulAut S)), Q S I F → ∃ f ∈ F, orderOf f = 3)
    (t1 : markTag lab = .PSU) (t2 : markRank lab = 3) : 3 ∣ 2 * markDeg lab := by
  obtain ⟨tg, r, nn⟩ := lab
  obtain ⟨hn, -⟩ := hl
  change 1 ≤ nn at hn
  cases tg
  all_goals first
    | exact fo_unitary (by omega) hn hraw h3
    | exact (fo_G2der hraw h3).elim
    | (exfalso
       simp only [markTag, markRank] at t1 t2
       (try split_ifs at t1 t2) <;> simp_all)

private theorem coinc_contra {lab : LargeEvenLabel} {Q : CFSG.Assembly.LargeEvenRawCont}
    (hl : LargeEvenInLambda2 lab) (hraw : CFSG.Assembly.LargeEvenRawDatum lab Q)
    (h3 : ∀ (S : Type) [Group S] (I F : Set (MulAut S)), Q S I F → ∃ f ∈ F, orderOf f = 3)
    (h2 : markChar lab = 2)
    (hc : (markTag lab = .PSL ∧ markRank lab = 2 ∧ markDeg lab = 2) ∨
      (markTag lab = .PSL ∧ markRank lab = 3 ∧ markDeg lab = 1) ∨
      (markTag lab = .PSU ∧ markRank lab = 4 ∧ markDeg lab = 1)) : False := by
  obtain ⟨tg, r, nn⟩ := lab
  obtain ⟨hn, -⟩ := hl
  change 1 ≤ nn at hn
  cases tg
  all_goals simp only [markTag, markRank, markDeg, markChar] at hc h2
  all_goals (try split_ifs at hc h2)
  all_goals (try subst_vars)
  all_goals first
    | exact absurd (fo_linear hn hraw h3) (by omega)
    | exact absurd (fo_linear_sq hn hraw h3) (by omega)
    | exact absurd (fo_unitary (by omega) hn hraw h3) (by omega)
    | (exfalso; simp_all)

private theorem markChar_cases (lab : LargeEvenLabel) :
    markChar lab = 2 ∨ markChar lab = 3 := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;> simp [markChar]

private theorem char3_or_tits_contra {lab : LargeEvenLabel} {Q : CFSG.Assembly.LargeEvenRawCont}
    (hl : LargeEvenInLambda2 lab) (hraw : CFSG.Assembly.LargeEvenRawDatum lab Q)
    (h3 : ∀ (S : Type) [Group S] (I F : Set (MulAut S)), Q S I F → ∃ f ∈ F, orderOf f = 3)
    (hc : markChar lab = 3 ∨ markTag lab = .Tits) : False := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg
  all_goals first
    | exact fo_B2der hraw h3
    | exact fo_G2der hraw h3
    | (obtain ⟨-, hr, hn1⟩ := hl
       subst hr hn1
       exact fo_twF4der hraw h3)
    | (exfalso
       simp only [markChar, markTag] at hc
       (try split_ifs at hc) <;> simp_all)

private theorem lieModel_psl29_of_alt6 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    CFSG.Blueprint.LieModel X .PSL 2 3 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
  have hF : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  obtain ⟨φ⟩ :=
    LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      (GaloisField 3 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  refine Or.inl ⟨by decide, ?_⟩
  exact ⟨by norm_num [StatedLieAdmissible], GaloisField 3 2, inferInstance, inferInstance, hK,
    ⟨e.trans (φ.symm.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 3 2)))⟩⟩

section Cert


private theorem core_F {R : Type} [Group R] [Finite R] {lab : LargeEvenLabel}
    {Q : CFSG.Assembly.LargeEvenRawCont}
    (hl : LargeEvenInLambda2 lab) (hraw : CFSG.Assembly.LargeEvenRawDatum lab Q)
    (h3 : ∀ (S : Type) [Group S] (I F : Set (MulAut S)), Q S I F → ∃ f ∈ F, orderOf f = 3)
    (hM : MarkedModel lab R) (hcat : catalogIs R excIndex) : False := by
  by_cases hc : markChar lab = 3 ∨ markTag lab = .Tits
  · exact char3_or_tits_contra hl hraw h3 hc
  have h2 : markChar lab = 2 := (markChar_cases lab).resolve_right (fun h => hc (Or.inl h))
  have hT : markTag lab ≠ .Tits := fun h => hc (Or.inr h)
  have hX : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
    unfold MarkedModel at hM
    rwa [h2] at hM
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating n _ =>
    simp only [excIndex] at hi
    rcases hi with rfl | rfl
    ·
      have e6 : R ≃* alternatingGroup (Fin 6) := e
      have hm6 := lieModel_psl29_of_alt6 e6
      have hodd : CFSG.Blueprint.OddLieType R :=
        ⟨.PSL, 2, 3, 2, Nat.prime_three, by decide, hm6.admissible, hm6⟩
      rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType_of_ne_Tits hX hT hodd with
        hc' | hc' | hc'
      · exact coinc_contra hl hraw h3 h2 (Or.inl hc')
      · exact coinc_contra hl hraw h3 h2 (Or.inr (Or.inl hc'))
      · exact coinc_contra hl hraw h3 h2 (Or.inr (Or.inr hc'))
    ·
      have e7 : R ≃* alternatingGroup (Fin 7) := e
      have hcard : Nat.card R = 2520 := by
        rw [Nat.card_congr e7.toEquiv, nat_card_alternatingGroup]
        norm_num [Nat.card_eq_fintype_card, Nat.factorial]
      exact CFSG.ComponentClassification.CatFC.not_lieModel_two_card_2520
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hcard hX.admissible hX
  | sporadic s =>
    simp only [excIndex] at hi
    subst hi
    obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group SporadicName.M22
    have eM : R ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22 := e.trans eC.symm
    have hcard : Nat.card R = 443520 := by
      rw [Nat.card_congr eM.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M22
    exact CFSG.LocalAnalysis.GLTheoremA.i112d_not_lieModel_two_card_443520 hcard hX.admissible hX
  | lie j =>
    obtain ⟨d, hv⟩ := j
    cases d with
    | A r q =>
      rcases r with _ | _ | _ | r
      · exact hi.elim
      · exact hi.elim
      ·
        have hq : q.card % 9 = 4 ∨ q.card % 9 = 7 := hi
        have hcardq : q.card = q.p ^ q.exponent := PrimePower.card_def q
        by_cases hp : q.p = 2
        · have hm : CFSG.Blueprint.LieModel R .PSL 3 2 q.exponent := by
            have h := (CFSG.Models.lieModel_A 2 q hv e).toBlueprint (by decide)
            rw [hp] at h
            exact h
          obtain ⟨t1, t2, t3⟩ :=
            CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by norm_num) hm hX
          have hdiv := div_PSL3 hl hraw h3 t1 t2
          rw [t3] at hdiv
          have hc2 : q.card = 2 ^ q.exponent := by rw [hcardq, hp]
          rcases two_pow_mod_nine hdiv with h | h <;> rw [hc2] at hq <;> omega
        · have hm : CFSG.Blueprint.LieModel R .PSL 3 q.p q.exponent :=
            (CFSG.Models.lieModel_A 2 q hv e).toBlueprint (by decide)
          have hodd : CFSG.Blueprint.OddLieType R :=
            ⟨.PSL, 3, q.p, q.exponent, q.prime_p, hp, hm.admissible, hm⟩
          rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType_of_ne_Tits hX hT hodd with
            hc' | hc' | hc'
          · exact coinc_contra hl hraw h3 h2 (Or.inl hc')
          · exact coinc_contra hl hraw h3 h2 (Or.inr (Or.inl hc'))
          · exact coinc_contra hl hraw h3 h2 (Or.inr (Or.inr hc'))
      · exact hi.elim
    | twistedA r q =>
      rcases r with _ | _ | _ | r
      · exact hi.elim
      · exact hi.elim
      ·
        have hq : q.card % 9 = 2 ∨ q.card % 9 = 5 := hi
        have hcardq : q.card = q.p ^ q.exponent := PrimePower.card_def q
        by_cases hp : q.p = 2
        · have hm : CFSG.Blueprint.LieModel R .PSU 3 2 q.exponent := by
            have h := lieModel_twistedA' 2 q hv e
            rw [hp] at h
            exact h.toBlueprint (by decide)
          obtain ⟨t1, t2, t3⟩ :=
            CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet R q.exponent _ _ _ hm hX.admissible hX
          have hdiv := div_PSU3 hl hraw h3 t1 t2
          rw [t3] at hdiv
          have hdiv' : 3 ∣ q.exponent := by omega
          have hc2 : q.card = 2 ^ q.exponent := by rw [hcardq, hp]
          rcases two_pow_mod_nine hdiv' with h | h <;> rw [hc2] at hq <;> omega
        · have hm : CFSG.Blueprint.LieModel R .PSU 3 q.p q.exponent :=
            (lieModel_twistedA' 2 q hv e).toBlueprint (by decide)
          have hodd : CFSG.Blueprint.OddLieType R :=
            ⟨.PSU, 3, q.p, q.exponent, q.prime_p, hp, hm.admissible, hm⟩
          rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType_of_ne_Tits hX hT hodd with
            hc' | hc' | hc'
          · exact coinc_contra hl hraw h3 h2 (Or.inl hc')
          · exact coinc_contra hl hraw h3 h2 (Or.inr (Or.inl hc'))
          · exact coinc_contra hl hraw h3 h2 (Or.inr (Or.inr hc'))
      · exact hi.elim
    | _ => exact hi.elim

theorem excNoFieldAt_holds (G : Type) [Group G] [Finite G] : ExcNoFieldAt G := by
  intro X J d _ hE hF
  obtain ⟨-, -, hcat⟩ := hE
  obtain ⟨-, hMark⟩ := hF
  obtain ⟨-, lab, hlab, hraw⟩ := CFSG.StandardType.Canonical.largeEvenMarking_markedModel hMark
  obtain ⟨S₀, _, I₀, F₀, hQ₀⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, -, hM₀⟩ := hQ₀
  have hM : MarkedModel lab (PSimple 3 J) := MarkedModel.of_mulEquiv θ₀.symm hM₀
  refine core_F hlab hraw ?_ hM hcat
  intro S _ I F hQ
  obtain ⟨-, -, θ, hP, -⟩ := hQ
  obtain ⟨-, f, hf, -, -, hord, -⟩ := hP
  exact ⟨f, hf, hord⟩

end Cert

end CFSG.LocalAnalysis.GLTheoremA

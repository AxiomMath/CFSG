module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Amb
public import CFSG.GH74.KGroups.A5
public import CFSG.GH74.KGroups.A6
public import CFSG.GH74.KGroups.L28
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.LieType.Multipliers.U42
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint
public import CFSG.Blueprint.LieModelAPI
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Goldschmidt.Basic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019A
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S11.Basic
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Models.Transport
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem card_lt_sq_of_not_dvd {p : ℕ} (hp : p.Prime) {M : Type*} [Group M] [Finite M]
    (hM : ¬ p ^ 2 ∣ Nat.card M) {A : Subgroup M} (hA : IsElemAbelian p A) :
    Nat.card A < p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p A := by
    intro g
    refine ⟨1, ?_⟩
    have := hA.2 g g.2
    apply Subtype.ext
    simpa using this
  obtain ⟨m, hm⟩ := hpg.exists_card_eq
  have hdvd : Nat.card A ∣ Nat.card M := Subgroup.card_subgroup_dvd_card A
  rw [hm] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hm2 : 2 ≤ m := by
    by_contra hc
    push Not at hc
    have : m ≤ 1 := by omega
    exact absurd (Nat.pow_le_pow_right hp.pos this) (by
      have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega)
  exact hM ((pow_dvd_pow p hm2).trans hdvd)

theorem primePower_eight (q : TauCeti.PrimePower) (h : q.card = 8) : q.p = 2 ∧ q.exponent = 3 := by
  have hc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [h] at hc
  have hdvd : q.p ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, hc]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  have hp : q.p = 2 :=
    (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)
  refine ⟨hp, ?_⟩
  rw [hp] at hc
  exact Nat.pow_right_injective (le_refl 2)
    (show 2 ^ q.exponent = 2 ^ 3 by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact hc.symm)

theorem primePower_two (q : TauCeti.PrimePower) (h : q.card = 2) : q.p = 2 ∧ q.exponent = 1 := by
  have hc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [h] at hc
  have hdvd : q.p ∣ 2 := by
    rw [hc]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  have hp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
  refine ⟨hp, ?_⟩
  rw [hp] at hc
  exact Nat.pow_right_injective (le_refl 2)
    (show 2 ^ q.exponent = 2 ^ 1 by rw [pow_one]; exact hc.symm)

theorem not_sq_dvd_120 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 120 := by
  intro hd
  have hle : p ^ 2 ≤ 120 := Nat.le_of_dvd (by norm_num) hd
  have : p ≤ 10 := by nlinarith
  interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)

theorem not_sq_dvd_1440 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ 1440 := by
  intro hd
  have hle : p ^ 2 ≤ 1440 := Nat.le_of_dvd (by norm_num) hd
  have : p ≤ 37 := by nlinarith
  interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)

theorem not_sq_dvd_1512 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ 1512 := by
  intro hd
  have hle : p ^ 2 ≤ 1512 := Nat.le_of_dvd (by norm_num) hd
  have : p ≤ 38 := by nlinarith
  interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)

theorem not_sq_dvd_51840 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ 51840 := by
  intro hd
  have hle : p ^ 2 ≤ 51840 := Nat.le_of_dvd (by norm_num) hd
  have : p ≤ 227 := by nlinarith
  interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)

theorem lieModel_L28 {S : Type} [Group S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq : q.card = 8)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩).Group) :
    CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.PSL 2 2 3 := by
  obtain ⟨hp, hf⟩ := primePower_eight q hq
  have h : CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.PSL 2 q.p q.exponent :=
    CFSG.Models.LieModel.toBlueprint (by decide) (CFSG.Models.lieModel_A 1 q hv e)
  rw [hp, hf] at h
  exact h

theorem lieModel_U42 {S : Type} [Group S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩).Group) :
    CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.PSU 4 2 1 := by
  obtain ⟨hp, hf⟩ := primePower_two q hq
  have h := CFSG.Models.lieModel_twistedA 3 q hv e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩ =
      q.p := TauCeti.LieTypeIndex.characteristic_twistedA 3 q
  have hf' : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩ =
      q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA 3 q
  rw [hc, hf'] at h
  have h' : CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.PSU (3 + 1) q.p q.exponent :=
    CFSG.Models.LieModel.toBlueprint (by decide) h
  rw [hp, hf] at h'
  exact h'

theorem card_mulAut_U42 {K : Type} [Group K]
    (e : K ≃* CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45.originalSubgroup) :
    Finite (MulAut K) ∧ Nat.card (MulAut K) = 51840 := by
  obtain ⟨M, hP, hA⟩ := CFSG.ComponentClassification.CatFactsSmall.PSp43.exists_model e
  refine ⟨Finite.of_equiv M.A M.Φ.symm.toEquiv, ?_⟩
  rw [M.card_mulAut, hA, CFSG.GH74.KGroups.card_group
    CFSG.ComponentClassification.CatFactsSmall.PSp43.QA45
    CFSG.ComponentClassification.CatFactsSmall.PSp43.QA45_ok,
    (CFSG.ComponentClassification.CatFactsSmall.PSp43.QA45_valid).2]

theorem s2019FactAmbAut_holds :
    S2019FactAmbAut := by
  intro p q hp hp2 hq hq2 hqp S _ hcat A hA
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  suffices h : ∃ _ : Finite (MulAut S), ¬ p ^ 2 ∣ Nat.card (MulAut S) by
    obtain ⟨hfin, hord⟩ := h
    exact card_lt_sq_of_not_dvd hp hord hA
  cases i with
  | cyclic r hr => simp [ambiguousChev] at hi
  | sporadic s => simp [ambiguousChev] at hi
  | alternating n hn =>
    have hi' : (n = 5 ∧ (q = 2 ∨ q = 5)) ∨ (n = 6 ∧ (q = 2 ∨ q = 3)) ∨ (n = 8 ∧ q = 2) := hi
    rcases hi' with ⟨rfl, hq'⟩ | ⟨rfl, hq'⟩ | ⟨rfl, hq'⟩
    · have e5 : S ≃* alternatingGroup (Fin 5) := e
      obtain ⟨e'⟩ := CFSG.GH74.KGroups.A5.equiv_of_alt e5
      exact ⟨CFSG.GH74.KGroups.A5.finite_mulAut e', by
        rw [CFSG.GH74.KGroups.A5.card_mulAut e']
        exact not_sq_dvd_120 hp hp2⟩
    · have e6 : S ≃* alternatingGroup (Fin 6) := e
      obtain ⟨e'⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 ⟨e6⟩
      rcases hq' with h | h
      · exact absurd h hq2
      · subst h
        exact ⟨CFSG.GH74.KGroups.A6.finite_mulAut e', by
          rw [CFSG.GH74.KGroups.A6.card_mulAut e']
          exact not_sq_dvd_1440 hp hp2 (Ne.symm hqp)⟩
    · exact absurd hq' hq2
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    have hi' : ambiguousChev q (TauCeti.CFSGIndex.lie ⟨d1, hv⟩) := hi
    cases d1 <;> try (simp [ambiguousChev] at hi'; done)
    case A r q' =>
      rcases r with _ | _ | _ | r
      · simp [ambiguousChev] at hi'
      · have h1 : (q'.card = 7 ∧ q = 2) ∨ (q'.card = 8 ∧ q = 3) := by
          simpa [ambiguousChev] using hi'
        rcases h1 with ⟨-, h⟩ | ⟨hc8, rfl⟩
        · exact absurd h hq2
        · have hL := lieModel_L28 q' hv hc8 e
          exact ⟨CFSG.GH74.KGroups.L28.finite_mulAut hL, by
            rw [CFSG.GH74.KGroups.L28.card_mulAut hL]
            exact not_sq_dvd_1512 hp hp2 (Ne.symm hqp)⟩
      · simp [ambiguousChev] at hi'
      · simp [ambiguousChev] at hi'
    case twistedA r q' =>
      rcases r with _ | _ | _ | _ | r
      · simp [ambiguousChev] at hi'
      · simp [ambiguousChev] at hi'
      · have h1 : q'.card = 3 ∧ q = 2 := by simpa [ambiguousChev] using hi'
        exact absurd h1.2 hq2
      · have h1 : q'.card = 2 ∧ q = 3 := by simpa [ambiguousChev] using hi'
        obtain ⟨hc2, rfl⟩ := h1
        have hU := lieModel_U42 q' hv hc2 e
        obtain ⟨e₁⟩ := CFSG.LieType.Multipliers.U42.nonempty_mulEquiv_PSp43 hU
        have e₂ := e₁.trans CFSG.ComponentClassification.CatFactsSmall.PSp43.psp43EquivP
        obtain ⟨hfin, hc⟩ := card_mulAut_U42 e₂
        exact ⟨hfin, by rw [hc]; exact not_sq_dvd_51840 hp hp2 (Ne.symm hqp)⟩
      · simp [ambiguousChev] at hi'

end CFSG.LocalAnalysis.GLTheoremA.S2019

end

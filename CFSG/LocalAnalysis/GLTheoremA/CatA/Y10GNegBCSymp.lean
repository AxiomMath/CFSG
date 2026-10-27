module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCLab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.Open.GLADefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore
import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldGrp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsSympA6
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.MarkingSmall
import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
import CFSG.LieType.SemisimpleCentralizers.HeldLangPSL
import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
import CFSG.RankThree.PartOne.CTP.SpEven
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec4.Item426A6
import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.Walter.J1Props
import CFSG.Walter.J1Recog
import CFSG.Walter.PSL2Facts
import CFSG.Walter.W67.Statements

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem innDiagKind_symp_data_BC {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hBC : labK.tag = .B ∨ labK.tag = .C)
    (hin : InnDiagKind S labK α) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (m : ℕ), 2 ≤ m ∧
      Nat.card K = 2 ^ (canonLabel labK).n ∧
      ∃ (e : S ≃* StatedProj (StatedSp m K)) (A : gsp m K),
        ∀ l : S, e (α l) = conjAut m K A (e l) := by
  unfold InnDiagKind CFSG.Assembly.LargeEvenMarking at hin
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hBC with ht | ht
  all_goals
    have hm : 2 ≤ labK.rank := by
      have h := hlam
      simp only [LargeEvenInLambda2, ht] at h
      exact h.2.1
    unfold CFSG.Assembly.LargeEvenRawDatum at hraw
    simp only [ht] at hraw
    unfold LargeEvenRecipeSymplectic at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A, hA⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage hu
    let e : S ≃* StatedProj (StatedSp labK.rank K) :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans θ
    have hαu : ∀ l : S, e (α l) = conjAut labK.rank K A (e l) := by
      intro l
      rw [hA]
      exact (hind l (α l) rfl).symm
    have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, ht]
    exact ⟨K, hK, hKf, labK.rank, hm, by rw [hc]; exact hcard, e, A, hαu⟩

theorem quotCenter_cases_symp_of_component {m n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (x : StatedSp m K) (hx : x ^ p = 1) {J : Subgroup (StatedProj (StatedSp m K))}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj m K x)))) :
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ k ∧
        n ∣ k ∧ Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL a E))) ∨
      (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
          (hτ : ∀ y, τ (τ y) = y), 2 ≤ a ∧ (∀ y, τ y = y ^ (2 ^ k)) ∧
          Nat.card E = (2 ^ k) ^ 2 ∧ n ∣ k ∧
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            ↥(heldSU a E τ hτ) ⧸ Subgroup.center ↥(heldSU a E τ hτ))) ∨
      (∃ s : ℕ, 2 ≤ s ∧ ¬(s = 2 ∧ Nat.card K = 2) ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSp s K))) ∨
      (Nat.card K = 2 ∧ Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6))) := by
  classical
  obtain ⟨-, hcomp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsCore_conj_sp_card (a6 := False)
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds
      (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
      hp hp2 Nat.prime_two hn hK hm hp2 (fun h => h.elim) x hx
  obtain ⟨X, inst, hXfin, ⟨hXLie, hA6⟩, hfac, f, hf, hker⟩ := hcomp J hJ
  letI := inst
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hXLie.perfect f hf hker
  unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SpFactorOver at hfac
  rcases hfac with hSL | hSU | hSp | hSp42
  · rw [hK] at hSL
    exact Or.inl (Y10GCenterQuot.linCase_of_factor eJ hSL)
  · rw [hK] at hSU
    exact Or.inr (Or.inl (Y10GCenterQuot.uniCase_of_factor eJ hSU))
  · obtain ⟨-, -, s, hs2, hne, ⟨eX⟩⟩ := hSp
    have hne' : ¬(s = 2 ∧ Nat.card K = 2) := fun h => hne (by rw [h.1, h.2])
    have hchar : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
    obtain ⟨eXZ⟩ := Y10GCenterQuot.nonempty_centerQuot_sp (s := s) hs2 hne' hchar eX
    exact Or.inr (Or.inr (Or.inl ⟨s, hs2, hne', ⟨eJ.trans eXZ⟩⟩))
  ·
    obtain ⟨-, -, hK2, ⟨eX4⟩⟩ := hSp42
    obtain ⟨e3⟩ := CFSG.StandardType.nonempty_largeEvenSpGroup_equiv_sympFour hK2
    obtain ⟨e4⟩ := CFSG.StandardType.nonempty_commutator_equiv e3
    let eXS : X ≃* ↥(commutator CFSG.ComponentClassification.PresentationLocal.sympFour) :=
      eX4.trans e4
    haveI hsS : IsSimpleGroup (commutator CFSG.ComponentClassification.PresentationLocal.sympFour) :=
      CFSG.ComponentClassification.PresentationLocal.isSimpleGroup_commutator_sympFour
    haveI hpS : Group.IsPerfect (commutator CFSG.ComponentClassification.PresentationLocal.sympFour) :=
      CFSG.ComponentClassification.PresentationLocal.isPerfect_commutator_sympFour
    haveI : IsSimpleGroup X := eXS.isSimpleGroup
    haveI : Group.IsPerfect X :=
      Group.IsPerfect.ofSurjective (f := eXS.symm.toMonoidHom) eXS.symm.surjective
    obtain ⟨eXZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.nonempty_quotCenter_equiv
      (eXS.trans CFSG.ComponentClassification.PresentationLocal.commutatorEquivAlternating)
    exact Or.inr (Or.inr (Or.inr ⟨hK2, ⟨eJ.trans eXZ⟩⟩))

theorem quotCenter_cases_symp {m n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (x : StatedSp m K) (hx : x ^ p = 1) {J : Subgroup (StatedProj (StatedSp m K))}
    (hJ : GLAPComponent p (fixSubgroup (MulAut.conj (proj m K x))) J) :
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ k ∧
        n ∣ k ∧ Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL a E))) ∨
      (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
          (hτ : ∀ y, τ (τ y) = y), 2 ≤ a ∧ (∀ y, τ y = y ^ (2 ^ k)) ∧
          Nat.card E = (2 ^ k) ^ 2 ∧ n ∣ k ∧
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            ↥(heldSU a E τ hτ) ⧸ Subgroup.center ↥(heldSU a E τ hτ))) ∨
      (∃ s : ℕ, 2 ≤ s ∧ ¬(s = 2 ∧ Nat.card K = 2) ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSp s K))) ∨
      (Nat.card K = 2 ∧ Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6))) := by
  classical
  obtain ⟨hPIL, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsCore_conj_sp_card (a6 := False)
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds
      (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
      hp hp2 Nat.prime_two hn hK hm hp2 (fun h => h.elim) x hx
  have hperfJ := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle := hPIL J hJ.1 hperfJ
  have hJcomp : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj m K x))) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hJle).1
  exact quotCenter_cases_symp_of_component hK hn hm hp hp2 x hx hJcomp

private theorem not_D_or_twD_high_of_canon {labJ : GLALabel} {t : LargeEvenLieTag} {r k : ℕ}
    (h : canonLabel labJ = ⟨t, r, k⟩) (htD : t ≠ .D) (htwD : t ≠ .twD) :
    ¬ ((labJ.tag = .D ∨ labJ.tag = .twD) ∧ 4 ≤ labJ.rank) := by
  obtain ⟨t', r', n'⟩ := labJ
  rintro ⟨h1 | h1, h4⟩
  · subst h1
    dsimp at h4
    have hr : r' ≠ 3 := by omega
    simp [canonLabel, hr] at h
    exact htD h.1.symm
  · subst h1
    dsimp at h4
    have hr3 : r' ≠ 3 := by omega
    have hr2 : r' ≠ 2 := by omega
    simp [canonLabel, hr3, hr2] at h
    exact htwD h.1.symm

private theorem negC_symp_inn_common (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S]
    {p : ℕ} {α : MulAut S} {J : Subgroup S} {labK labJ : GLALabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hBC : labK.tag = .B ∨ labK.tag = .C)
    (hin : InnDiagKind S labK α) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup α) ∨ GLAPComponent p (fixSubgroup α) J) :
    ¬ ((labJ.tag = .D ∨ labJ.tag = .twD) ∧ 4 ≤ labJ.rank) := by
  obtain ⟨K, hK, hKf, m, hm, hcard, e, A, hαA⟩ := innDiagKind_symp_data_BC hcen hBC hin
  have hn : 1 ≤ (canonLabel labK).n := by
    rcases Nat.eq_zero_or_pos (canonLabel labK).n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hcard
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have h2 : (2 : K) = 0 := by
    haveI := Fintype.ofFinite K
    obtain ⟨q, hq, k, hqp, hqcard⟩ := FiniteField.card' K
    have hc := hcard
    rw [Nat.card_eq_fintype_card, hqcard] at hc
    have hdvd : q ∣ 2 ^ (canonLabel labK).n := by
      rw [← hc]
      exact dvd_pow_self q (PNat.ne_zero k)
    have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
    subst hq2
    exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨x, hx⟩ := Y10GInnSympRed.exists_conjAut_eq_conj h2 A
  have hMEq : MulAut.congr e α = MulAut.conj (proj m K x) := by
    rw [← hx]
    ext r
    have h1 := hαA (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hZ : Subgroup.center (StatedProj (StatedSp m K)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e.symm z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hz (e g)
    rw [hcen, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hz'
  have hpow : MulAut.conj (proj m K x) ^ p = 1 := by
    rw [← hMEq, ← map_pow, hα, map_one]
  have hxp : x ^ p = 1 := Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ hpow
  have hJ' : CFSG.Open.IsComponentOf (J.map e.toMonoidHom)
      (fixSubgroup (MulAut.conj (proj m K x))) ∨
      GLAPComponent p (fixSubgroup (MulAut.conj (proj m K x))) (J.map e.toMonoidHom) := by
    rw [← hMEq, ← Y10F.fixSubgroup_map_congr]
    rcases hJ with hJc | hJp
    · exact Or.inl ((Y10F.isComponentOf_map_iff e.injective).mpr hJc)
    · exact Or.inr ((Y10F.glaPComponent_map_iff hp e.injective).mpr hJp)
  have hlabJ' := Y10F.hasLabel_transport e hlabJ
  have hcases := hJ'.elim
    (fun hJc => quotCenter_cases_symp_of_component hcard hn (by omega) hp hp2 x hxp hJc)
    (fun hJp => quotCenter_cases_symp hcard hn (by omega) hp hp2 x hxp hJp)
  rcases hcases with
      ⟨a, k, E, _, _, ha, hE, -, hφ⟩ | ⟨a, k, E, _, _, τ, hτ, ha, hτk, hE, -, hφ⟩ |
      ⟨s, hs, hne, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  ·
    exact not_D_or_twD_high_of_canon
      (Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig _ labJ a k E ha hE hlabJ' hφ)
      (by decide) (by decide)
  ·
    rcases uniLabel_cases hRig τ hτ ha hτk hE hlabJ' hφ with h | h
    · exact not_D_or_twD_high_of_canon h (by decide) (by decide)
    · exact not_D_or_twD_high_of_canon h (by decide) (by decide)
  ·
    exact not_D_or_twD_high_of_canon
      (Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig hs hcard hne hlabJ' φ)
      (by decide) (by decide)
  ·
    exact not_D_or_twD_high_of_canon
      (Y10GSympLabel.canonLabel_eq_of_quot_alternating hRig hlabJ' φ) (by decide) (by decide)

theorem negC_symp_inn (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S] {p : ℕ}
    {α : MulAut S} {J : Subgroup S} {labK labJ : GLALabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hBC : labK.tag = .B ∨ labK.tag = .C)
    (hin : InnDiagKind S labK α) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : GLAPComponent p (fixSubgroup α) J) :
    ¬ (labJ.tag = .twD ∧ labJ.rank = 5) := by
  rintro ⟨ht, hr⟩
  exact negC_symp_inn_common hRig hp hp2 hcen hBC hin hα hlabJ (Or.inr hJ)
    ⟨Or.inr ht, by omega⟩

theorem negC_symp (hRig : GGLabelRigidInput) (hFld : FldSymp) {S : Type} [Group S] [Finite S]
    {p : ℕ} {α : MulAut S} {J : Subgroup S} {labK labJ : GLALabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hBC : labK.tag = .B ∨ labK.tag = .C)
    (hlabK : HasLabel S (fun l : GLALabel => l = labK)) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : GLAPComponent p (fixSubgroup α) J) :
    ¬ (labJ.tag = .twD ∧ labJ.rank = 5) := by
  have hFam : FamSymp labK := by
    rcases hBC with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rcases ClsSymp_holds S p α labK hFam hp hp2 hcen hlabK hα with hin | hfld
  · exact negC_symp_inn hRig hp hp2 hcen hBC hin hα hlabJ hJ
  · obtain ⟨-, htag, -⟩ := hFld S p α J labK labJ hFam hp hp2 hcen hfld hα hlabJ hJ
    refine not_twD5_of_canon (t := (canonLabel labJ).tag) (r := (canonLabel labJ).rank)
      (k := (canonLabel labJ).n) rfl ?_
    rw [← htag]
    rcases hBC with h | h <;> simp [canonLabel, h]

end CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC

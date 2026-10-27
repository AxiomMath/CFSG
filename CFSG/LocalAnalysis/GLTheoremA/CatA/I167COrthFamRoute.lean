module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthMinus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFamOuter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFamD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFamModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFamTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFamDesc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFamOut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFamType
import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CBridgePlus
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33b
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrth
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverNormalize
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Field
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusClassDescent
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.G11Stmts
import CFSG.HardMathSupport.Dickson.I271.SporGenBM
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBM
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveHN
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveShape
import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitStatement412
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCheck
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFiveB
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh7
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveB
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporThreeSmall
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1113
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import CFSG.RankThree.PartOne.S11d.OrthModels
import Certificates.Certificate41501

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open Module QuadraticMap CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10GField
  CFSG.RankThree.PartOne.OutStructure
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer)
open CFSG.StandardType (GGLabelRigidInput GGLabelIso)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCOrthogonal (fixedSpace supportedFixedDerived)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT exists_ne_zero_of_nondeg SubfieldSetup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (coordinateFieldMap matrixProjectiveDerived)
open CFSG.SeitzReduction.OmegaPilot (orthDerivedProjEquiv)

@[expose] def COrthConcl (p : ℕ) (S : Type) [Group S] (J : Subgroup S) : Prop :=
  (p = 3 ∧ ∃ n : ℕ, Even n ∧ catalogIs (PSimple 3 J) (isOmMA n 2) ∧
      catalogIs S (isOmPA (n + 1) 2)) ∨
    ∃ n k : ℕ, Odd n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p J) (isOmPA n (2 ^ k)) ∧
      catalogIs S (isOmMA (n + 1) (2 ^ k))

theorem i167COrth_fermat {p m : ℕ} (hp : p.Prime) (h : p ∣ m ^ p + 1) : p ∣ m + 1 := by
  haveI := Fact.mk hp
  have h1 : ((m ^ p + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  have h2 : (m : ZMod p) ^ p = m := ZMod.pow_card (m : ZMod p)
  have h3 : ((m + 1 : ℕ) : ZMod p) = 0 := by
    push_cast at h1 ⊢
    rw [h2] at h1
    exact h1
  exact (ZMod.natCast_eq_zero_iff _ _).1 h3

theorem i167COrth_psi_fix_iff {S : Type} [Group S] {β : MulAut S} {K : Type} [Field K] [Finite K]
    [CharP K 2] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) (hQ : ∃ v, Q v ≠ 0)
    (ψ : S ≃* matrixProjectiveDerived Q) (hψ : MulAut.congr ψ β = fieldAutT Q σ hQσ)
    (a : ↥(orthDerived Q)) :
    (MulAut.congr (ψ.trans (orthDerivedProjEquiv Q hQ).symm) β) a = a ↔
      SigmaEquivariant σ (a : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
  set Ψ : S ≃* ↥(orthDerived Q) := ψ.trans (orthDerivedProjEquiv Q hQ).symm with hΨ
  have h1 := i167COrth_fieldModel_fix_iff Q σ hQσ hQ ψ hψ (Ψ.symm a)
  have h2 : (orthDerivedProjEquiv Q hQ).symm (ψ (Ψ.symm a)) = a := by
    have := Ψ.apply_symm_apply a
    rwa [hΨ, MulEquiv.trans_apply] at this
  rw [h2] at h1
  rw [MulAut.congr_apply, ← h1]
  constructor
  · intro h
    have := congrArg Ψ.symm h
    simpa using this
  · intro h
    show Ψ (β (Ψ.symm a)) = a
    rw [h]
    simp

theorem i167COrth_prelude (hD : COrthLabelDict) (hRig : GGLabelRigidInput) {S : Type} [Group S]
    [Finite S] {p : ℕ} {α : MulAut S} {J : Subgroup S} {labK : GLALabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hFam : FamOrth labK) (hZ : Subgroup.center S = ⊥) (hαp : orderOf α = p)
    (hInn : InnDiagKind S labK α)
    (hhalf : ∃ labH : GLALabel, GGLabelIso labH labK ∧ GLAHalfSplit16 p labH True)
    (hJc : GLAPComponent p (fixSubgroup α) J) (hJt : Type167J p J) :
    ∃ a₀ : S, α = MulAut.conj a₀ ∧ IsComponentOf J (fixSubgroup (MulAut.conj a₀)) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J) ∧ p ∣ 2 ^ (canonLabel labK).n + 1 := by
  obtain ⟨hmod, a₀, rfl⟩ := Y10GInnOrthMark.innDiagKind_orth_data hZ hFam hInn
  have hinj := i167COrth_conj_injective hZ
  have hαp1 : (MulAut.conj a₀ : MulAut S) ^ p = 1 := by
    rw [← hαp]
    exact pow_orderOf_eq_one _
  have ha : a₀ ^ p = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact hαp1
  have hperf : PerfectInLayer (MulAut.conj a₀) := by
    rcases hmod with h | h
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_omega
        (Or.inr (Or.inl rfl)) h hp hp2 hp2 a₀ ha
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_omega
        (Or.inr (Or.inr rfl)) h hp hp2 hp2 a₀ ha
  obtain ⟨hJcomp, eJ⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.component_of_glaPComponent hp hperf hJc
  exact ⟨a₀, rfl, hJcomp, eJ, i167COrth_hpq hD hRig hp hp2 hZ hFam hInn hαp1 hhalf hJc hJcomp.2.2 eJ hJt⟩

theorem i167COrth_route_d4 (hD : COrthLabelDict) (hRig : GGLabelRigidInput)
    (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S] {p : ℕ} {α : MulAut S}
    {J : Subgroup S} {labK : GLALabel} (hp : p.Prime) (hp2 : p ≠ 2) (hFam : FamOrth labK)
    (hZ : Subgroup.center S = ⊥) (hαp : orderOf α = p) (hInn : InnDiagKind S labK α)
    (hhalf : ∃ labH : GLALabel, GGLabelIso labH labK ∧ GLAHalfSplit16 p labH True)
    (hJc : GLAPComponent p (fixSubgroup α) J) (hJt : Type167J p J) (h4 : labK.rank = 4) :
    COrthConcl p S J := by
  obtain ⟨a₀, rfl, hJcomp, eJ, hpq⟩ := i167COrth_prelude hD hRig hp hp2 hFam hZ hαp hInn hhalf hJc hJt
  have hinj := i167COrth_conj_injective hZ
  have hαp1 : (MulAut.conj a₀ : MulAut S) ^ p = 1 := by
    rw [← hαp]
    exact pow_orderOf_eq_one _
  obtain ⟨hN, ha1, hcat⟩ := i167COrth_catalog_of_innDiag hZ hFam hInn
  have hlb := i167COrth_d4_lb hD hRig hb hp hp2 hZ hFam hInn hαp1 hJc hJcomp.2.2 eJ hJt
  rcases hcat with hcat | hcat
  · obtain ⟨F, _, _, _, V, _, _, _, Q, hcard, hQ, hdim, -, hX⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S172C.exists_omegaPlus_model hN ha1
    obtain ⟨e⟩ := hX S hcat
    have hpqF : p ∣ Nat.card F + 1 := by rw [hcard]; exact hpq
    have hg : orderOf (e a₀) = p := by
      rw [MulEquiv.orderOf_eq, ← hαp, orderOf_injective _ hinj a₀]
    exact i167COrth_outer_model hD hRig hb hQ hp hp2 hpqF hdim hN e hZ hαp hJcomp eJ hJt
      (i167COrth_d4_witt hQ hp hp2 hpqF hcard (by omega) e hg hlb)
  · obtain ⟨F, _, _, _, V, _, _, _, Q, hcard, hQ, hdim, -, hX⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S172C.exists_omegaMinus_model hN ha1
    obtain ⟨e⟩ := hX S hcat
    have hpqF : p ∣ Nat.card F + 1 := by rw [hcard]; exact hpq
    have hg : orderOf (e a₀) = p := by
      rw [MulEquiv.orderOf_eq, ← hαp, orderOf_injective _ hinj a₀]
    exact i167COrth_outer_model hD hRig hb hQ hp hp2 hpqF hdim hN e hZ hαp hJcomp eJ hJt
      (i167COrth_d4_witt hQ hp hp2 hpqF hcard (by omega) e hg hlb)

theorem i167COrth_field_cyc {S : Type} [Group S] [Finite S] {p : ℕ} {Bb : Subgroup (MulAut S)}
    {α β : MulAut S} {labK : GLALabel} (hp : p.Prime) (hp2 : p ≠ 2) (hFam : FamOrth labK)
    (hZ : Subgroup.center S = ⊥) (hInn : InnDiagKind S labK α) (hBb : IsElemAbelian p Bb)
    (hβ : β ∈ Bb) (hout : ∀ s : S, (MulAut.conj s : MulAut S) ≠ β)
    (h43 : ¬ (labK.rank = 4 ∧ p = 3)) :
    ∀ β' ∈ Bb, ∃ (j : ℤ) (s : S), (MulAut.conj s : MulAut S) ∈ Bb ∧
      β' = MulAut.conj s * β ^ j := by
  obtain ⟨hmod, -⟩ := Y10GInnOrthMark.innDiagKind_orth_data hZ hFam hInn
  obtain ⟨hN, -, -⟩ := i167COrth_catalog_of_innDiag hZ hFam hInn
  have hO : OutPChain p S := i167COrth_outPChain hp hp2 hN
    (hmod.imp (fun h => ⟨h, fun h4 h3 => h43 ⟨h4, h3⟩⟩) id)
  exact fun β' hβ' => i167COrth_outer_cyclic hp hO hBb hβ hout hβ'

theorem i167COrth_field_fm {S : Type} [Group S] {p : ℕ} {β : MulAut S} {labK : GLALabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hFam : FamOrth labK) (hZ : Subgroup.center S = ⊥)
    (hfld : FieldKind S labK β) (hβp : β ^ p = 1) :
    FieldModel p β labK.rank labK.n ∧ (canonLabel labK).n = labK.n := by
  rcases hFam with ⟨ht, hr3⟩ | ⟨ht, hr2, hr3⟩
  · exact ⟨i167COrth_fieldModel_plus hp hp2 hZ ht hr3 hfld hβp, by simp [canonLabel, ht, hr3]⟩
  · exact ⟨i167COrth_fieldModel_minus hp hp2 hZ ht hr2 hr3 hfld hβp,
      by simp [canonLabel, ht, hr2, hr3]⟩

theorem i167COrth_field_witt {S : Type} [Group S] {p : ℕ} {Bb : Subgroup (MulAut S)}
    {β : MulAut S} {J : Subgroup S} {a₀ : S} {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : Subfield K} {N : ℕ} {Q₀ : QuadraticForm k (Fin (2 * N) → k)}
    {Q : QuadraticForm K (Fin (2 * N) → K)} {σ : K ≃+* K} (SS : SubfieldSetup k Q₀ Q σ p)
    (hp : p.Prime) (hp2 : p ≠ 2) (hN : 4 ≤ N) (hpK : p ∣ Nat.card K + 1)
    (hpk : p ∣ Nat.card k + 1) (e : S ≃* ↥(orthDerived Q)) (hZ : Subgroup.center S = ⊥)
    (hBb : IsElemAbelian p Bb) (hα : (MulAut.conj a₀ : MulAut S) ∈ Bb) (hβ : β ∈ Bb)
    (hfix : ∀ a : ↥(orthDerived Q), (MulAut.congr e β) a = a ↔
      SigmaEquivariant σ (a : (Fin (2 * N) → K) ≃ₗ[K] (Fin (2 * N) → K)))
    (hcyc : ∀ β' ∈ Bb, ∃ (j : ℤ) (s : S), (MulAut.conj s : MulAut S) ∈ Bb ∧
      β' = MulAut.conj s * β ^ j)
    (hScp : ∀ s : S, (∀ β ∈ Bb, β s = s) → s ^ p = 1 → (MulAut.conj s : MulAut S) ∈ Bb)
    (hCent : ∀ β ∈ Bb, (∀ j ∈ J, β j = j) →
      β ∈ Subgroup.zpowers (MulAut.conj a₀ : MulAut S)) (hg : orderOf (e a₀) = p) :
    J.map e.toMonoidHom ≤
        (supportedFixedDerived Q ((e a₀ : ↥(orthDerived Q)) :
          (Fin (2 * N) → K) ≃ₗ[K] (Fin (2 * N) → K))).subgroupOf (orthDerived Q) →
      Module.finrank K (Fin (2 * N) → K) = Module.finrank K (fixedSpace ((e a₀ : ↥(orthDerived Q)) :
          (Fin (2 * N) → K) ≃ₗ[K] (Fin (2 * N) → K))) + 2 ∧
        (IsPlusType Q ↔ ¬ IsPlusType (Q.comp (fixedSpace ((e a₀ : ↥(orthDerived Q)) :
          (Fin (2 * N) → K) ≃ₗ[K] (Fin (2 * N) → K))).subtype)) := by
  intro hJle
  have hA : IsElemAbelian p (COrthInnerImage e Bb) := i167COrth_descent_elem e hZ hBb
  have hgA : e a₀ ∈ COrthInnerImage e Bb := i167COrth_innerImage_mem e hα
  have hrat : ∀ a ∈ COrthInnerImage e Bb, SigmaEquivariant σ
      (a : (Fin (2 * N) → K) ≃ₗ[K] (Fin (2 * N) → K)) :=
    fun a ha => (hfix a).1 (i167COrth_innerImage_fixed e hZ hBb hβ a ha)
  have hmax : ∀ s : ↥(orthDerived Q), SigmaEquivariant σ
      (s : (Fin (2 * N) → K) ≃ₗ[K] (Fin (2 * N) → K)) → s ^ p = 1 →
        (∀ a ∈ COrthInnerImage e Bb, a * s = s * a) → s ∈ COrthInnerImage e Bb :=
    fun s hs hsp hc => i167COrth_descent_max_outer e hβ hcyc hScp s ((hfix s).2 hs) hsp hc
  have hCA := i167COrth_descent_cent_triv SS.hnd hp hp2 e hZ hCent hg hJle
  have hdimW := i167COrth_descent_dim SS rfl hN hpk hA hrat hmax hgA hg hCA
  exact ⟨hdimW, i167COrth_type_of_dim SS.hnd hp hp2 hpK (by simp) hN hA hgA hg hdimW⟩

theorem i167COrth_route_field (hD : COrthLabelDict) (hRig : GGLabelRigidInput)
    (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S] {p : ℕ}
    {Bb : Subgroup (MulAut S)} {α β : MulAut S} {J : Subgroup S} {labK : GLALabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hFam : FamOrth labK) (hZ : Subgroup.center S = ⊥)
    (hBb : IsElemAbelian p Bb) (hα : α ∈ Bb) (hαp : orderOf α = p) (hInn : InnDiagKind S labK α)
    (hScp : ScpS p S Bb) (hCent : CentJ Bb α J) (hhalf : HalfSplitLab p labK)
    (hJc : GLAPComponent p (fixSubgroup α) J) (hJt : Type167J p J) (hβ : β ∈ Bb)
    (hout : ∀ s : S, (MulAut.conj s : MulAut S) ≠ β) (hfld : FieldKind S labK β)
    (h43 : ¬ (labK.rank = 4 ∧ p = 3)) :
    COrthConcl p S J := by
  obtain ⟨hN, -, -⟩ := i167COrth_catalog_of_innDiag hZ hFam hInn
  have hcyc := i167COrth_field_cyc hp hp2 hFam hZ hInn hBb hβ hout h43
  obtain ⟨a₀, rfl, hJcomp, eJ, hpq⟩ := i167COrth_prelude hD hRig hp hp2 hFam hZ hαp hInn hhalf hJc hJt
  obtain ⟨⟨K, _, _, k, Q₀, Q, σ, SS, ψ, hKa, hKk, hψ⟩, hcan⟩ :=
    i167COrth_field_fm hp hp2 hFam hZ hfld (hBb.2 β hβ)
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hKa
  have hQex : ∃ v, Q v ≠ 0 := exists_ne_zero_of_nondeg (by omega) SS.hnd
  have hpK : p ∣ Nat.card K + 1 := by rw [hKa, ← hcan]; exact hpq
  have hdim : Module.finrank K (Fin (2 * labK.rank) → K) = 2 * labK.rank := by simp
  let Ψ : S ≃* ↥(orthDerived Q) := ψ.trans (orthDerivedProjEquiv Q hQex).symm
  have hg : orderOf (Ψ a₀) = p := by
    rw [MulEquiv.orderOf_eq, ← hαp, orderOf_injective _ (i167COrth_conj_injective hZ) a₀]
  exact i167COrth_outer_model hD hRig hb SS.hnd hp hp2 hpK hdim hN Ψ hZ hαp hJcomp eJ hJt
    (i167COrth_field_witt SS hp hp2 hN hpK (i167COrth_fermat hp (by rw [← hKk]; exact hpK)) Ψ hZ
      hBb hα hβ (i167COrth_psi_fix_iff Q σ SS.hQσ hQex ψ hψ) hcyc hScp hCent hg)

end CFSG.LocalAnalysis.GLTheoremA.I167

end

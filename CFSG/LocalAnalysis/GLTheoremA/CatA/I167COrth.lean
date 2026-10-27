module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthMinus
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CBridgePlus
import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33b
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrth
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
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer mem_fixSubgroup)
open CFSG.StandardType (GGLabelRigidInput GGLabelIso)
open CFSG.RankThree.Classical2 (orthDerived)

theorem i167COrth_conj_injective {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro u v h
  have hc : v⁻¹ * u ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 : u * x * u⁻¹ = v * x * v⁻¹ := by
      simpa [MulAut.conj_apply] using congrArg (fun f : MulAut S => f x) h
    calc x * (v⁻¹ * u) = v⁻¹ * (v * x * v⁻¹) * u := by group
      _ = v⁻¹ * (u * x * u⁻¹) * u := by rw [h1]
      _ = v⁻¹ * u * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem i167COrth_halfSplit {p : ℕ} {labK : GLALabel} (hFam : FamOrth labK)
    (h : ∃ labH : GLALabel, GGLabelIso labH labK ∧ GLAHalfSplit16 p labH True) :
    p ∣ 2 ^ (canonLabel labK).n - 1 ∨ p ∣ 2 ^ (canonLabel labK).n + 1 := by
  obtain ⟨labH, hiso, hhs⟩ := h
  have hH : labH = labK := by
    unfold GGLabelIso at hiso
    rcases hFam with ⟨htag, hr3⟩ | ⟨htag, hr2, hr3⟩ <;> rcases labK with ⟨t, r, n⟩ <;>
      simp only at htag hr3 <;> subst htag <;> simp_all
  subst hH
  rcases hFam with ⟨htag, hr3⟩ | ⟨htag, hr2, hr3⟩
  · have hc : (canonLabel labH).n = labH.n := by simp [canonLabel, htag, hr3]
    rw [hc]
    unfold GLAHalfSplit16 CFSG.Assembly.LargeEvenHalfSplit16 CFSG.Assembly.LargeEvenSplit16
      CFSG.Assembly.LargeEvenUntwisted at hhs
    simp [htag] at hhs
    rcases hhs with (h | ⟨h1, h2⟩) | h
    · exact Or.inl h
    · right
      subst h2
      rw [h1]
      norm_num
    · exact Or.inr h
  · have hc : (canonLabel labH).n = labH.n := by simp [canonLabel, htag, hr2, hr3]
    rw [hc]
    unfold GLAHalfSplit16 CFSG.Assembly.LargeEvenHalfSplit16 CFSG.Assembly.LargeEvenSplit16
      CFSG.Assembly.LargeEvenUntwisted at hhs
    simp [htag] at hhs
    rcases hhs with h | h | ⟨h1, h2⟩
    · exact Or.inr h
    · exact Or.inl h
    · right
      subst h2
      rw [h1]
      norm_num

theorem i167COrth_hpq (hD : COrthLabelDict) (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZ : Subgroup.center S = ⊥) {α : MulAut S}
    {labK : GLALabel} (hFam : FamOrth labK) (hInn : InnDiagKind S labK α) (hαp : α ^ p = 1)
    (hhalf : ∃ labH : GLALabel, GGLabelIso labH labK ∧ GLAHalfSplit16 p labH True)
    {J : Subgroup S} (hJc : GLAPComponent p (fixSubgroup α) J) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJp : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J)) (hJt : Type167J p J) :
    p ∣ 2 ^ (canonLabel labK).n + 1 := by
  have hhs := i167COrth_halfSplit hFam hhalf
  obtain ⟨e⟩ := hJp
  have hdiv : ∀ labJ : GLALabel, Y10F.HasLabel ↥J (fun l : GLALabel => l = labJ) →
      (canonLabel labK).n ∣ (canonLabel labJ).n := fun labJ hl =>
    Y10GField.innDiagOrth_of_ggLabelRigidInput hRig S p α J labK labJ hFam hp hp2 hZ hInn hαp hl hJc
  rcases hJt with ⟨rfl, n, -, hn5, hc⟩ | ⟨rfl, n, -, hn6, hc⟩ | ⟨n, k, -, hn3, hk5, hk, hpk, hc⟩
  · obtain ⟨labJ, hl, hcan⟩ := hD.lnA hJq hn5 ((catalogIs_congr e).2 hc)
    have h1 : (canonLabel labK).n ∣ 1 := by simpa [hcan] using hdiv labJ hl
    exact i167COrth_numerics hp hp2 h1 (by norm_num) hhs
  · have hc' : catalogIs (↥J ⧸ Subgroup.center ↥J) (isOmMA n (2 ^ 1)) := by
      simpa using (catalogIs_congr e).2 hc
    obtain ⟨labJ, hl, hcan⟩ := hD.omM hJq (by omega) le_rfl hc'
    have h1 : (canonLabel labK).n ∣ 1 := by simpa [hcan] using hdiv labJ hl
    exact i167COrth_numerics hp hp2 h1 (by norm_num) hhs
  · obtain ⟨labJ, hl, hcan⟩ := hD.omP hJq hn3 hk (fun h3 => by omega) ((catalogIs_congr e).2 hc)
    have h1 : (canonLabel labK).n ∣ k := by
      have := hdiv labJ hl
      rw [hcan] at this
      split_ifs at this <;> exact this
    exact i167COrth_numerics hp hp2 h1 hpk hhs

theorem i167COrth_fix_map {S T : Type} [Group S] [Group T] (e : S ≃* T) (a₀ : S) :
    (fixSubgroup (MulAut.conj a₀)).map e.toMonoidHom = Subgroup.centralizer ({e a₀} : Set T) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixSubgroup, MulAut.conj_apply] at hx
    have h1 : x * a₀ = a₀ * x := by
      calc x * a₀ = a₀ * x * a₀⁻¹ * a₀ := by rw [hx]
        _ = a₀ * x := by group
    show e x * e a₀ = e a₀ * e x
    rw [← map_mul, ← map_mul, h1]
  · intro h
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_fixSubgroup, MulAut.conj_apply]
    have h1 : e.symm y * a₀ = a₀ * e.symm y := by
      apply e.injective
      simpa using h
    calc a₀ * e.symm y * a₀⁻¹ = (e.symm y * a₀) * a₀⁻¹ := by rw [h1]
      _ = e.symm y := by group

theorem i167COrth_type167J_congr {S T : Type} [Group S] [Group T] {p : ℕ} {J : Subgroup S} {J' : Subgroup T}
    (f : PSimple p J ≃* PSimple p J') (h : Type167J p J) : Type167J p J' := by
  rcases h with ⟨rfl, n, h1, h2, hc⟩ | ⟨rfl, n, h1, h2, hc⟩ | ⟨n, k, h1, h2, h3, h4, h5, hc⟩
  · exact Or.inl ⟨rfl, n, h1, h2, (catalogIs_congr f).1 hc⟩
  · exact Or.inr (Or.inl ⟨rfl, n, h1, h2, (catalogIs_congr f).1 hc⟩)
  · exact Or.inr (Or.inr ⟨n, k, h1, h2, h3, h4, h5, (catalogIs_congr f).1 hc⟩)

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem i167COrth_inner_model (hD : COrthLabelDict) (hRig : GGLabelRigidInput) (hb : CatDistinct.OrderBridge)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {N : ℕ} (hdim : Module.finrank F V = 2 * N) (hN : 4 ≤ N) {S : Type} [Group S]
    (e : S ≃* ↥(orthDerived Q)) (hZ : Subgroup.center S = ⊥) {Bb : Subgroup (MulAut S)} {a₀ : S}
    (hBb : IsElemAbelian p Bb) (hα : (MulAut.conj a₀ : MulAut S) ∈ Bb)
    (hαp : orderOf (MulAut.conj a₀ : MulAut S) = p)
    (hBinn : ∀ β ∈ Bb, ∃ s : S, (MulAut.conj s : MulAut S) = β)
    (hScp : ∀ s : S, (∀ β ∈ Bb, β s = s) → s ^ p = 1 → (MulAut.conj s : MulAut S) ∈ Bb)
    {J : Subgroup S}
    (hCent : ∀ β ∈ Bb, (∀ j ∈ J, β j = j) → β ∈ Subgroup.zpowers (MulAut.conj a₀ : MulAut S))
    (hJc : IsComponentOf J (fixSubgroup (MulAut.conj a₀)))
    (hJp : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J)) (hJt : Type167J p J) :
    (p = 3 ∧ ∃ n : ℕ, Even n ∧ catalogIs (PSimple 3 J) (isOmMA n 2) ∧
        catalogIs S (isOmPA (n + 1) 2)) ∨
      ∃ n k : ℕ, Odd n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p J) (isOmPA n (2 ^ k)) ∧
        catalogIs S (isOmMA (n + 1) (2 ^ k)) := by
  have hinj := i167COrth_conj_injective hZ
  have hA := i167COrth_descent_elem e hZ hBb
  have hmax := i167COrth_descent_max e hBinn hScp
  have hgA := i167COrth_innerImage_mem e hα
  have hg : orderOf (e a₀) = p := by
    rw [MulEquiv.orderOf_eq, ← hαp, orderOf_injective _ hinj a₀]
  have hJm : IsComponentOf (J.map e.toMonoidHom)
      (Subgroup.centralizer ({e a₀} : Set ↥(orthDerived Q))) := by
    have h1 : IsComponentOf (J.map e.toMonoidHom) ((fixSubgroup (MulAut.conj a₀)).map e.toMonoidHom) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJc
    rwa [i167COrth_fix_map] at h1
  let eJ : ↥J ≃* ↥(J.map e.toMonoidHom) := J.equivMapOfInjective e.toMonoidHom e.injective
  let hpf : PSimple p J ≃* PSimple p (J.map e.toMonoidHom) :=
    CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p eJ
  obtain ⟨eJ0⟩ := hJp
  have hJmp : Nonempty (↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom) ≃*
      PSimple p (J.map e.toMonoidHom)) :=
    ⟨((QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥(J.map e.toMonoidHom)) eJ
      (Subgroup.map_center_eq eJ)).symm.trans eJ0).trans hpf⟩
  have key := i167COrth_fixed hD hRig hb hQ hp hp2 hpq hdim hN hA hmax hgA hg hJm hJmp
    (i167COrth_descent_cent e hZ hCent) (i167COrth_type167J_congr hpf hJt)
  rcases key with ⟨hp3, n, hn, hc, h2⟩ | ⟨n, k, hn, hk, hpk, hc, h2⟩
  · subst hp3
    exact Or.inl ⟨rfl, n, hn, (catalogIs_congr hpf).2 hc, (catalogIs_congr e).2 h2⟩
  · exact Or.inr ⟨n, k, hn, hk, hpk, (catalogIs_congr hpf).2 hc, (catalogIs_congr e).2 h2⟩

end Model

theorem i167COrth_inner (hD : COrthLabelDict) (hRig : GGLabelRigidInput) (hb : CatDistinct.OrderBridge)
    {S : Type} [Group S] [Finite S] {p : ℕ} {Bb : Subgroup (MulAut S)} {α : MulAut S} {J : Subgroup S}
    {labK : GLALabel} (hp : p.Prime) (hp2 : p ≠ 2) (hFam : FamOrth labK) (hZ : Subgroup.center S = ⊥)
    (hBb : IsElemAbelian p Bb) (hα : α ∈ Bb) (hαp : orderOf α = p) (hInn : InnDiagKind S labK α)
    (hBinn : ∀ β ∈ Bb, ∃ s : S, (MulAut.conj s : MulAut S) = β)
    (hScp : ∀ s : S, (∀ β ∈ Bb, β s = s) → s ^ p = 1 → (MulAut.conj s : MulAut S) ∈ Bb)
    (hCent : ∀ β ∈ Bb, (∀ j ∈ J, β j = j) → β ∈ Subgroup.zpowers α)
    (hhalf : ∃ labH : GLALabel, GGLabelIso labH labK ∧ GLAHalfSplit16 p labH True)
    (hJc : GLAPComponent p (fixSubgroup α) J) (hJt : Type167J p J) :
    (p = 3 ∧ ∃ n : ℕ, Even n ∧ catalogIs (PSimple 3 J) (isOmMA n 2) ∧
        catalogIs S (isOmPA (n + 1) 2)) ∨
      ∃ n k : ℕ, Odd n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p J) (isOmPA n (2 ^ k)) ∧
        catalogIs S (isOmMA (n + 1) (2 ^ k)) := by
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
  have hpq : p ∣ 2 ^ (canonLabel labK).n + 1 :=
    i167COrth_hpq hD hRig hp hp2 hZ hFam hInn hαp1 hhalf hJc hJcomp.2.2 eJ hJt
  obtain ⟨hN, ha1, hcat⟩ := i167COrth_catalog_of_innDiag hZ hFam hInn
  rcases hcat with hcat | hcat
  · obtain ⟨F, _, _, _, V, _, _, _, Q, hcard, hQ, hdim, -, hX⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S172C.exists_omegaPlus_model hN ha1
    obtain ⟨e⟩ := hX S hcat
    exact i167COrth_inner_model hD hRig hb hQ hp hp2 (by rw [hcard]; exact hpq) hdim hN e hZ hBb hα
      hαp hBinn hScp hCent hJcomp eJ hJt
  · obtain ⟨F, _, _, _, V, _, _, _, Q, hcard, hQ, hdim, -, hX⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S172C.exists_omegaMinus_model hN ha1
    obtain ⟨e⟩ := hX S hcat
    exact i167COrth_inner_model hD hRig hb hQ hp hp2 (by rw [hcard]; exact hpq) hdim hN e hZ hBb hα
      hαp hBinn hScp hCent hJcomp eJ hJt

end CFSG.LocalAnalysis.GLTheoremA.I167

end

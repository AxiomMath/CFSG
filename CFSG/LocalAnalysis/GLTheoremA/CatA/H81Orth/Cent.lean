module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.RankThree.PartOne.S10.FiveSuccessorQuasisimple
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.Goldschmidt.Basic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.Open
open scoped commutatorElement

section Plane

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]

theorem commute_of_finrank_two (hU : finrank K U = 2) {y : Module.End K U}
    (hy : ∀ c : K, y ≠ c • 1) {f g : Module.End K U} (hf : Commute f y) (hg : Commute g y) :
    Commute f g := by
  classical
  have : Module.Free K U := Module.Free.of_divisionRing K U
  have : FiniteDimensional K U := Module.finite_of_finrank_eq_succ hU
  obtain ⟨u, hu⟩ : ∃ u : U, LinearIndependent K ![u, y u] := by
    by_contra hne
    push Not at hne
    obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hne
    exact hy c hc
  have hspan : Submodule.span K (Set.range ![u, y u]) = ⊤ :=
    hu.span_eq_top_of_card_eq_finrank (by simpa using hU.symm)
  have hpoly : ∀ h : Module.End K U, Commute h y → ∃ a b : K, h = a • 1 + b • y := by
    intro h hh
    have hmem : h u ∈ Submodule.span K (Set.range ![u, y u]) := by
      rw [hspan]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c 0, c 1, ?_⟩
    have hhu : h u = c 0 • u + c 1 • y u := by
      rw [← hc, Fin.sum_univ_two]
      rfl
    have hyh : h (y u) = y (h u) := by
      rw [← Module.End.mul_apply, hh.eq, Module.End.mul_apply]
    apply LinearMap.ext_on_range hspan
    intro i
    fin_cases i
    · simp [hhu]
    · show h (y u) = (c 0 • 1 + c 1 • y) (y u)
      rw [hyh, hhu, map_add, map_smul, map_smul]
      simp
  obtain ⟨a, b, rfl⟩ := hpoly f hf
  obtain ⟨c, d, rfl⟩ := hpoly g hg
  refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
  · exact ((Commute.one_left 1).smul_left a).smul_right c
  · exact ((Commute.one_left y).smul_left a).smul_right d
  · exact ((Commute.one_right y).smul_left b).smul_right c
  · exact ((Commute.refl y).smul_left b).smul_right d

end Plane

section Centralizer

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

local notation "R" => othersSpace (LinearEquiv.toLinearMap x) (X - 1 : K[X])

@[expose] noncomputable def restrictOthers (g : V ≃ₗ[K] V) (hg : g ∈ isometryCentralizer Q x) :
    Module.End K R :=
  (g.toLinearMap.restrict fun r hr =>
    mem_othersSpace_of_apply (Subgroup.mem_inf.mp hg).2 hr)

theorem coe_restrictOthers_apply (g : V ≃ₗ[K] V) (hg : g ∈ isometryCentralizer Q x) (r : R) :
    ((restrictOthers g hg r : R) : V) = g r :=
  rfl

@[expose] noncomputable def restrictOthersSelf (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    Module.End K R :=
  restrictOthers x ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem commute_restrictOthers_self (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (g : V ≃ₗ[K] V) (hg : g ∈ isometryCentralizer Q x) :
    Commute (restrictOthers g hg) (restrictOthersSelf hx) := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  have hc : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2
  show g (x r) = x (g r)
  exact congrArg (fun f : V ≃ₗ[K] V => f r) hc

theorem restrictOthersSelf_ne_smul (hx : OddOrderIsometry Q p x) (hp2 : p ≠ 2) (hp : p.Prime)
    (h2 : (2 : K) ≠ 0) (hR : R ≠ ⊥) (c : K) : restrictOthersSelf hx.mem ≠ c • 1 := by
  classical
  intro hc
  obtain ⟨hcompl, horth⟩ := hx.fixed_others
  have hreg : ∀ r ∈ R, (∀ s ∈ R, QuadraticMap.polar Q r s = 0) → r = 0 := by
    intro r hr hrs
    apply hx.regular
    intro v
    obtain ⟨w, hw, s, hs, rfl⟩ := exists_add_of_isCompl hcompl v
    rw [QuadraticMap.polar_add_right, hrs s hs, add_zero,
      QuadraticMap.polar_comm, horth w hw r hr]
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  have hQr : ∃ s ∈ R, Q s ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hr0
    refine hreg r hr fun s hs => ?_
    rw [QuadraticMap.polar, hall _ (Submodule.add_mem _ hr hs), hall r hr, hall s hs]
    ring
  obtain ⟨s, hs, hQs⟩ := hQr
  have hxs : x s = c • s := by
    have := congrArg (fun f : Module.End K R => ((f ⟨s, hs⟩ : R) : V)) hc
    simp only [restrictOthersSelf, coe_restrictOthers_apply, LinearMap.smul_apply,
      Module.End.one_apply, Submodule.coe_smul] at this
    exact this
  have hc2 : c ^ 2 = 1 := by
    have hQ := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem) s
    rw [hxs, QuadraticMap.map_smul, smul_eq_mul] at hQ
    have : (c * c - 1) * Q s = 0 := by rw [sub_mul, hQ, one_mul, sub_self]
    have := (mul_eq_zero.mp this).resolve_right hQs
    rw [sq]
    exact sub_eq_zero.mp this
  have hpow : ∀ n : ℕ, (x ^ n) s = c ^ n • s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, LinearEquiv.mul_apply, hxs, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hs0 : s ≠ 0 := fun h => hQs (by rw [h, QuadraticMap.map_zero])
  have hc2' : c * c = 1 := by rw [← sq]; exact hc2
  rcases mul_self_eq_one_iff.mp hc2' with h1 | h1
  ·
    apply hs0
    have hsW : s ∈ fixedSpace x := by
      rw [mem_fixedSpace, hxs, h1, one_smul]
    exact (Submodule.disjoint_def.mp hcompl.disjoint) s hsW hs
  ·
    apply hs0
    have h := hpow p
    rw [hx.pow_eq_one, h1, (hp.eq_two_or_odd'.resolve_left hp2).neg_one_pow, neg_one_smul,
      LinearEquiv.coe_one, id_eq] at h
    have h2s : (2 : K) • s = 0 := by rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel s
    exact (smul_eq_zero.mp h2s).resolve_left h2

omit [FiniteDimensional K V] in
theorem commutatorElement_mem_of_mem {H : Subgroup (V ≃ₗ[K] V)} {g h : V ≃ₗ[K] V} (hg : g ∈ H)
    (hh : h ∈ H) : ⁅g, h⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)) (H.inv_mem hh)

theorem commutatorElement_mem_supportedBlock (hx : OddOrderIsometry Q p x) (hp2 : p ≠ 2)
    (hp : p.Prime) (h2 : (2 : K) ≠ 0) (hR : finrank K R = 2) {g h : V ≃ₗ[K] V}
    (hg : g ∈ isometryCentralizer Q x) (hh : h ∈ isometryCentralizer Q x) :
    ⁅g, h⁆ ∈ supportedBlock Q x (X - 1) := by
  have hRne : R ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hR
    exact absurd hR (by norm_num)
  have hcomm := commute_of_finrank_two hR (restrictOthersSelf_ne_smul hx hp2 hp h2 hRne)
    (commute_restrictOthers_self hx.mem g hg) (commute_restrictOthers_self hx.mem h hh)
  have hgh : ∀ r ∈ R, g (h r) = h (g r) := fun r hr => by
    have := congrArg (fun f : Module.End K R => ((f ⟨r, hr⟩ : R) : V)) hcomm.eq
    simpa [coe_restrictOthers_apply] using this
  refine mem_supportedBlock.mpr ⟨commutatorElement_mem_of_mem hg hh, fun r hr => ?_⟩
  have hinv : (h * g)⁻¹ r ∈ R :=
    mem_othersSpace_of_apply (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_inf.mp hh).2
      (Subgroup.mem_inf.mp hg).2)) hr
  have hc : ⁅g, h⁆ = (g * h) * (h * g)⁻¹ := by group
  rw [hc, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgh _ hinv, ← LinearEquiv.mul_apply,
    ← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl

theorem commutator_isometryCentralizer_le (hx : OddOrderIsometry Q p x) (hp2 : p ≠ 2)
    (hp : p.Prime) (h2 : (2 : K) ≠ 0) (hR : finrank K R = 2) :
    ⁅isometryCentralizer Q x, isometryCentralizer Q x⁆ ≤ supportedBlock Q x (X - 1) :=
  (Subgroup.commutator_le).mpr fun _ hg _ hh =>
    commutatorElement_mem_supportedBlock hx hp2 hp h2 hR hg hh

theorem commutator_supportedBlock_le :
    ⁅supportedBlock Q x (X - 1), supportedBlock Q x (X - 1)⁆ ≤ supportedFixedDerived Q x := by
  rw [Subgroup.commutator_le]
  intro s hs t ht
  refine mem_supportedFixedDerived.mpr ⟨commutatorElement_mem_of_mem hs ht, ?_⟩
  have hc : (⟨⁅s, t⁆, commutatorElement_mem_of_mem hs ht⟩ : ↥(supportedBlock Q x (X - 1))) =
      ⁅(⟨s, hs⟩ : ↥(supportedBlock Q x (X - 1))), ⟨t, ht⟩⁆ := rfl
  rw [hc, map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (restrictFixed_mem_orthogonalGroup _)
    (restrictFixed_mem_orthogonalGroup _)

theorem commutator_commutator_le_supportedFixedDerived (hx : OddOrderIsometry Q p x)
    (hp2 : p ≠ 2) (hp : p.Prime) (h2 : (2 : K) ≠ 0) (hR : finrank K R = 2) :
    ⁅⁅isometryCentralizer Q x, isometryCentralizer Q x⁆,
      ⁅isometryCentralizer Q x, isometryCentralizer Q x⁆⁆ ≤ supportedFixedDerived Q x :=
  (Subgroup.commutator_mono (commutator_isometryCentralizer_le hx hp2 hp h2 hR)
    (commutator_isometryCentralizer_le hx hp2 hp h2 hR)).trans commutator_supportedBlock_le

theorem commutator_commutator_centralizerImage_le (hx : OddOrderIsometry Q p x)
    (hp2 : p ≠ 2) (hp : p.Prime) (h2 : (2 : K) ≠ 0) (hR : finrank K R = 2) :
    ⁅⁅centralizerImage Q x, centralizerImage Q x⁆,
      ⁅centralizerImage Q x, centralizerImage Q x⁆⁆ ≤ fixedComponentImage Q x := by
  unfold centralizerImage fixedComponentImage
  simp only [← Subgroup.map_commutator]
  apply Subgroup.map_mono
  intro z hz
  rw [Subgroup.mem_subgroupOf]
  have hz' : (orthDerived Q).subtype z ∈
      (⁅⁅(isometryCentralizer Q x).subgroupOf (orthDerived Q),
          (isometryCentralizer Q x).subgroupOf (orthDerived Q)⁆,
        ⁅(isometryCentralizer Q x).subgroupOf (orthDerived Q),
          (isometryCentralizer Q x).subgroupOf (orthDerived Q)⁆⁆).map (orthDerived Q).subtype :=
    Subgroup.mem_map_of_mem _ hz
  simp only [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype] at hz'
  refine commutator_commutator_le_supportedFixedDerived hx hp2 hp h2 hR ?_
  exact Subgroup.commutator_mono
    (Subgroup.commutator_mono inf_le_left inf_le_left)
    (Subgroup.commutator_mono inf_le_left inf_le_left) hz'

omit [FiniteDimensional K V] in
theorem isPerfect_of_commutator_eq {G : Type*} [Group G] {L : Subgroup G} (h : ⁅L, L⁆ = L) :
    Group.IsPerfect ↥L := by
  refine ⟨Subgroup.map_injective L.subtype_injective ?_⟩
  rw [Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem le_fixedComponentImage_of_glaPComponent (hx : OddOrderIsometry Q p x) (hp2 : p ≠ 2)
    (hp : p.Prime) (h2 : (2 : K) ≠ 0) (hR : finrank K R = 2) {L : Subgroup (ProjOrthDerived Q)}
    (hL : GLAPComponent p (centralizerImage Q x) L) : L ≤ fixedComponentImage Q x := by
  have hperf : ⁅L, L⁆ = L := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hL
  have hLX : L ≤ centralizerImage Q x := hL.1
  have h22 : ⁅⁅L, L⁆, ⁅L, L⁆⁆ = L := by rw [hperf, hperf]
  rw [← h22]
  exact (Subgroup.commutator_mono (Subgroup.commutator_mono hLX hLX)
    (Subgroup.commutator_mono hLX hLX)).trans
      (commutator_commutator_centralizerImage_le hx hp2 hp h2 hR)

theorem isSubnormal_fixedComponentImage (hx : OddOrderIsometry Q p x) :
    CFSG.Open.IsSubnormal (fixedComponentImage Q x) (centralizerImage Q x) :=
  CFSG.Open.IsSubnormal.step fixedComponentImage_le_centralizerImage
    hx.normal_fixedComponentImage (CFSG.Open.IsSubnormal.refl _)

theorem glaPComponent_fixedComponentImage [Finite K] (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hJ : CFSG.Open.IsQuasisimple ↥(fixedComponentImage Q x))
    (hdvd : p ∣ Nat.card
      (↥(fixedComponentImage Q x) ⧸ Subgroup.center ↥(fixedComponentImage Q x))) :
    GLAPComponent p (centralizerImage Q x) (fixedComponentImage Q x) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  exact CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp
    (isSubnormal_fixedComponentImage hx) hJ hdvd

theorem eq_fixedComponentImage_of_glaPComponent [Finite K] (hx : OddOrderIsometry Q p x)
    (hp2 : p ≠ 2) (hp : p.Prime) (h2 : (2 : K) ≠ 0) (hR : finrank K R = 2)
    (hJ : CFSG.IsQuasisimple ↥(fixedComponentImage Q x)) {L : Subgroup (ProjOrthDerived Q)}
    (hL : GLAPComponent p (centralizerImage Q x) L) : L = fixedComponentImage Q x := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hLJ := le_fixedComponentImage_of_glaPComponent hx hp2 hp h2 hR hL
  have hsn : CFSG.Open.IsSubnormal L (fixedComponentImage Q x) := by
    have := hL.2.1.inf_of_le (fixedComponentImage_le_centralizerImage (Q := Q) (x := x))
    rwa [inf_eq_left.mpr hLJ] at this
  exact CFSG.RankThree.PartOne.eq_of_isSubnormal_of_isPerfect_of_isQuasisimple hJ hLJ
    (isPerfect_of_commutator_eq (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hL))
    (CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hL) hsn.subgroupOf

end Centralizer

end CFSG.LocalAnalysis.GLTheoremA.H81Orth

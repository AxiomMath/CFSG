module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthFrame4
public import CFSG.ClassicalInvolution.ModelFacts.MF15Sign
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutWitt
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Twin
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge
public import CFSG.ClassicalInvolution.ModelFacts.CentralLift
public import CFSG.ClassicalInvolution.RouteD.ExoticD4GenEich
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.LieType.SeitzGeneration.OrthManyMaster
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.MF15Sq
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LieType.SeitzGeneration.OrthNonsplitLow
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Models.OrthogonalPairs
  QuadraticMap Matrix CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.LieType.Universal.Spin
  CFSG.LieType.SeitzGeneration OrthBlk CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryMixing CFSG.RankThree.Classical
open CFSG.RankThree.Classical2 (orthDerived)
open scoped MatrixGroups

section Odd

variable {K : Type*} [Field K]

theorem odd_mem_mulSub (h2 : (2 : K) ≠ 0)
    {T : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) {N : ℕ} (hN : Odd N)
    (hTN : T ^ N = 1) :
    T ∈ mulSub (leftGrp (K := K)) rightGrp commute_leftGrp_rightGrp := by
  haveI : Invertible (2 : K) := invertibleOfNonzero h2
  have hdet : LinearEquiv.det T = 1 := by
    have h1 : (LinearEquiv.det T) ^ N = 1 := by
      rw [← map_pow, hTN, map_one]
    have hsq : (LinearEquiv.det T) ^ 2 = 1 := by
      have := TauCeti.QuadraticMap.orthogonalDet_sq
        (QuadraticMap.nondegenerate_polar_iff.mpr (nondegenerate_detQ (K := K))).1 ⟨T, hT⟩
      simpa using this
    obtain ⟨k, rfl⟩ := hN
    have : (LinearEquiv.det T) ^ (2 * k + 1) = LinearEquiv.det T := by
      rw [pow_succ, pow_mul, hsq, one_pow, one_mul]
    rw [← this, h1]
  have hSO : T ∈ TauCeti.QuadraticMap.specialOrthogonalGroup (detQ (K := K)) :=
    TauCeti.QuadraticMap.mem_specialOrthogonalGroup_iff.mpr ⟨hT, hdet⟩
  obtain ⟨a, b, hab⟩ := mem_bimulGrp.mp (specialOrthogonalGroup_le_bimulGrp h2 hSO)
  obtain ⟨hda, hdb⟩ := isUnit_det_of_bimul hab
  have hd0 : a.det ≠ 0 := hda.ne_zero
  have hiso : a.det * b.det = 1 := by
    have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hT 1
    rw [detQ_apply, detQ_apply, hab, Matrix.mul_one, Matrix.det_mul, Matrix.det_one] at h
    exact h
  have hA : ((a.det)⁻¹ • (a * a)).det = 1 := by
    rw [Matrix.det_smul, Matrix.det_mul]
    simp only [Fintype.card_fin]
    field_simp
  have hB : (a.det • (b * b)).det = 1 := by
    rw [Matrix.det_smul, Matrix.det_mul]
    simp only [Fintype.card_fin]
    have : a.det ^ 2 * (b.det * b.det) = (a.det * b.det) ^ 2 := by ring
    rw [this, hiso, one_pow]
  let A : SL(2, K) := ⟨(a.det)⁻¹ • (a * a), hA⟩
  let B : SL(2, K) := ⟨a.det • (b * b), hB⟩
  have hTT : T * T = lmulEquiv A * rmulEquiv B := by
    refine LinearEquiv.ext fun X => ?_
    have e1 : (lmulEquiv A) ((rmulEquiv B) X) = (A : Matrix (Fin 2) (Fin 2) K) * (X * B) :=
      rfl
    rw [LinearEquiv.mul_apply, hab, hab, LinearEquiv.mul_apply]
    change _ = (A : Matrix (Fin 2) (Fin 2) K) * (X * (B : Matrix (Fin 2) (Fin 2) K))
    simp only [A, B, Matrix.SpecialLinearGroup.coe_mk, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.mul_assoc]
    rw [mul_inv_cancel₀ hd0, one_smul]
  have hTTmem : T * T ∈ mulSub (leftGrp (K := K)) rightGrp commute_leftGrp_rightGrp :=
    mem_mulSub.mpr ⟨_, lmulEquiv_mem_leftGrp A, _, rmulEquiv_mem_rightGrp B, hTT⟩
  obtain ⟨k, rfl⟩ := hN
  have hT1 : T = (T * T) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hTN, one_mul]
  rw [hT1]
  exact Subgroup.pow_mem _ hTTmem _

end Odd

section Frame

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_La_mul_swapLa_of_odd (F : Frame Q) (h2 : (2 : K) ≠ 0) {N : ℕ} (hN : Odd N)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : g * F.La (-1) = F.La (-1) * g) (hfix : ∀ x ∈ F.perp, g x = x) (hgN : g ^ N = 1) :
    ∃ n ∈ F.La.range, ∃ m ∈ F.swap.La.range, g = n * m := by
  have hσO := Frame.transportEquiv_mem_orthogonalGroup h2 hg hc
  have hemb := Frame4.embGrp_transportEquiv_eq h2 hc hfix
  set σ := Frame.transportEquiv h2 hc with hσ
  have hσN : σ ^ N = 1 := by
    apply F.embGrp_injective
    rw [map_pow, hemb, hgN, map_one]
  have hmem := odd_mem_mulSub h2 hσO hN hσN
  obtain ⟨l, hl, r, hr, hlr⟩ := mem_mulSub.mp hmem
  refine ⟨F.embGrp l, ?_, F.embGrp r, ?_, ?_⟩
  · rw [Frame.La_range_eq_map]
    exact ⟨l, hl, rfl⟩
  · rw [Frame.swap_La_range_eq_map]
    exact ⟨r, hr, rfl⟩
  · rw [← map_mul, ← hlr, hemb]

end Frame

section Blocks

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem commute_La_neg_one_of_preserves (F : Frame Q) {g : V ≃ₗ[K] V}
    (hs : ∀ x ∈ F.span, g x ∈ F.span) (hp : ∀ x ∈ F.perp, g x ∈ F.perp) :
    g * F.La (-1) = F.La (-1) * g := by
  refine LinearEquiv.ext fun x => ?_
  have hr : x - F.incl (F.coords x) ∈ F.perp := by
    rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
  have h1 := hp _ hr
  have h2 : g (F.incl (F.coords x)) ∈ F.span := hs _ ⟨F.coords x, rfl⟩
  have h3 : F.incl (F.coords (g (F.incl (F.coords x)))) = g (F.incl (F.coords x)) :=
    ((Frame.mem_span_iff F).mp h2).symm
  have h4 : F.coords (g (x - F.incl (F.coords x))) = 0 := (Frame.mem_perp_iff F).mp h1
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Frame.La_neg_one_apply, Frame.La_neg_one_apply,
    map_sub, map_smul]
  have h5 : F.coords (g x) = F.coords (g (F.incl (F.coords x))) := by
    have := congrArg F.coords (show g x = g (F.incl (F.coords x)) + g (x - F.incl (F.coords x)) by
      rw [← map_add]; congr 1; abel)
    rw [this, map_add, h4, add_zero]
  rw [h5, h3]

end Blocks

section Product

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem preserves_perp_of_isometry [FiniteDimensional K V] (F : Frame Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs : ∀ x ∈ F.span, g x ∈ F.span) :
    ∀ x ∈ F.perp, g x ∈ F.perp := by
  intro x hx
  rw [Frame.mem_perp_iff_forall_incl] at hx ⊢
  intro Y
  have hsymm := CFSG.ClassicalInvolution.ModelFacts.OrthAut.symm_mem_of_mem g F.span hs
  obtain ⟨Z, hZ⟩ := hsymm (F.incl Y) ⟨Y, rfl⟩
  have hQg := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  have h1 : polar Q (g x) (F.incl Y) = polar Q x (g.symm (F.incl Y)) := by
    have : polar Q (g x) (g (g.symm (F.incl Y))) = polar Q x (g.symm (F.incl Y)) := by
      simp only [QuadraticMap.polar, ← map_add, hQg]
    simpa using this
  rw [h1, ← hZ]
  exact hx Z

end Product

section BlockProduct

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem mem_iSup_La_swapLa_of_odd [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {m : ℕ}
    (Fr : Fin m → Frame Q)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ (Fr i).span, ∀ y ∈ (Fr j).span, polar Q x y = 0)
    (hspan : ⨆ i, (Fr i).span = ⊤) {N : ℕ} (hN : Odd N) {f : V ≃ₗ[K] V}
    (hfO : f ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfN : f ^ N = 1)
    (hfs : ∀ i, ∀ x ∈ (Fr i).span, f x ∈ (Fr i).span) :
    f ∈ ⨆ i, ((Fr i).La.range ⊔ (Fr i).swap.La.range) := by
  classical
  have hperp : ∀ i, ∀ x ∈ (Fr i).perp, f x ∈ (Fr i).perp := fun i =>
    preserves_perp_of_isometry (Fr i) hfO (hfs i)
  have hc : ∀ i, f * (Fr i).La (-1) = (Fr i).La (-1) * f := fun i =>
    commute_La_neg_one_of_preserves (Fr i) (hfs i) (hperp i)
  let T : Fin m → V ≃ₗ[K] V := fun i => (Fr i).embGrp (Frame.transportEquiv h2 (hc i))
  have hTspan : ∀ i, ∀ x ∈ (Fr i).span, T i x = f x := by
    intro i x hx
    have hx' : x = (Fr i).incl ((Fr i).coords x) := (Frame.mem_span_iff (Fr i)).mp hx
    change (Fr i).embLin _ x = f x
    rw [Frame.embLin_apply_eq, ← hx', sub_self, add_zero]
    change (Fr i).incl ((Fr i).transport f ((Fr i).coords x)) = f x
    rw [Frame.incl_transport h2 (hc i), ← hx']
  have hTperp : ∀ i, ∀ x ∈ (Fr i).perp, T i x = x := by
    intro i x hx
    have h0 : (Fr i).coords x = 0 := (Frame.mem_perp_iff (Fr i)).mp hx
    change (Fr i).embLin _ x = x
    rw [Frame.embLin_apply_eq, h0, map_zero, map_zero, sub_zero, zero_add]
  have hTorth : ∀ i, T i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro i
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    have hσ := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (Frame.transportEquiv_mem_orthogonalGroup h2 hfO (hc i))
    change Q ((Fr i).embLin _ x) = Q x
    refine Frame.Q_embLin (Fr i) (fun X => ?_) x
    have := hσ X
    rwa [detQ_apply, detQ_apply] at this
  have hTc : ∀ i, T i * (Fr i).La (-1) = (Fr i).La (-1) * T i := by
    intro i
    refine commute_La_neg_one_of_preserves (Fr i) (fun x hx => ?_) (fun x hx => ?_)
    · rw [hTspan i x hx]
      exact hfs i x hx
    · rw [hTperp i x hx]
      exact hx
  have hTN : ∀ i, T i ^ N = 1 := by
    intro i
    refine LinearEquiv.ext fun x => ?_
    have hspow : ∀ k : ℕ, ∀ x ∈ (Fr i).span, (T i ^ k) x = (f ^ k) x := by
      intro k
      induction k with
      | zero => intro x hx; simp
      | succ k ih =>
        intro x hx
        rw [pow_succ, pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          hTspan i x hx, ih (f x) (hfs i x hx)]
    have hppow : ∀ k : ℕ, ∀ x ∈ (Fr i).perp, (T i ^ k) x = x := by
      intro k
      induction k with
      | zero => intro x hx; simp
      | succ k ih =>
        intro x hx
        rw [pow_succ, LinearEquiv.mul_apply, hTperp i x hx, ih x hx]
    have hs : (Fr i).incl ((Fr i).coords x) ∈ (Fr i).span := ⟨_, rfl⟩
    have hp : x - (Fr i).incl ((Fr i).coords x) ∈ (Fr i).perp := by
      rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
    have hx' : x = (Fr i).incl ((Fr i).coords x) + (x - (Fr i).incl ((Fr i).coords x)) := by
      abel
    calc (T i ^ N) x
        = (T i ^ N) ((Fr i).incl ((Fr i).coords x)) +
            (T i ^ N) (x - (Fr i).incl ((Fr i).coords x)) := by rw [← map_add, ← hx']
      _ = (f ^ N) ((Fr i).incl ((Fr i).coords x)) + (x - (Fr i).incl ((Fr i).coords x)) := by
        rw [hspow N _ hs, hppow N _ hp]
      _ = x := by
        rw [hfN]
        simpa using hx'.symm
  have hH : ∀ i, T i ∈ (Fr i).La.range ⊔ (Fr i).swap.La.range := by
    intro i
    obtain ⟨n, hn, m', hm, hnm⟩ :=
      exists_La_mul_swapLa_of_odd (Fr i) h2 hN (hTorth i) (hTc i) (hTperp i) (hTN i)
    rw [hnm]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hm)
  have hTfix : ∀ j k, j ≠ k → ∀ x ∈ (Fr k).span, T j x = x := by
    intro j k hjk x hx
    apply hTperp j x
    rw [Frame.mem_perp_iff_forall_incl]
    intro Y
    rw [polar_comm]
    exact horth j k hjk _ ⟨Y, rfl⟩ x hx
  have hlist : ∀ l : List (Fin m), l.Nodup → ∀ k, ∀ x ∈ (Fr k).span,
      ((l.map T).prod) x = if k ∈ l then f x else x := by
    intro l hl
    induction l with
    | nil => intro k x hx; simp
    | cons j l ih =>
      intro k x hx
      rw [List.nodup_cons] at hl
      rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih hl.2 k x hx]
      by_cases hkl : k ∈ l
      · have hjk : j ≠ k := fun h => hl.1 (h ▸ hkl)
        simp only [hkl, if_true, List.mem_cons, or_true]
        exact hTfix j k hjk (f x) (hfs k x hx)
      · by_cases hjk : j = k
        · subst hjk
          simp [hkl, hTspan j x hx]
        · simp [hkl, hjk, hTfix j k hjk x hx, Ne.symm hjk]
  have hprod : ((List.finRange m).map T).prod = f := by
    refine LinearEquiv.ext fun x => ?_
    have hx : x ∈ ⨆ i, (Fr i).span := by
      rw [hspan]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (fun i => (Fr i).span)
      (motive := fun x => (((List.finRange m).map T).prod) x = f x) hx
      (fun k y hy => ?_) (by simp) (fun a b ha hb => by rw [map_add, map_add, ha, hb])
    rw [hlist _ (List.nodup_finRange m) k y hy]
    simp
  rw [← hprod]
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
  exact (le_iSup (fun i => (Fr i).La.range ⊔ (Fr i).swap.La.range) i) (hH i)

end BlockProduct

section Planes

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.ModelFacts.MF15

theorem exists_frame_span_eq_of_aniso [Finite K] [FiniteDimensional K V] {P P' : Submodule K V}
    (hP : PolarNondegOn Q P) (hP' : PolarNondegOn Q P') (hd : Module.finrank K P = 2)
    (hd' : Module.finrank K P' = 2) (hn : ¬ SignPlus Q P) (hn' : ¬ SignPlus Q P')
    (horth : ∀ x ∈ P, ∀ y ∈ P', polar Q x y = 0) : ∃ Fr : Frame Q, Fr.span = P ⊔ P' := by
  classical
  have hU : PolarNondegOn Q (P ⊔ P') :=
    CFSG.ClassicalInvolution.ModelFacts.Orth15.polarNondegOn_sup hP hP' horth
  have hdisj : Disjoint P P' := by
    rw [Submodule.disjoint_def]
    intro x hxP hxP'
    exact hP x hxP fun y hy => by rw [polar_comm]; exact horth y hy x hxP'
  have hd4 : Module.finrank K ↥(P ⊔ P') = 4 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq P P'
    rw [hdisj.eq_bot, finrank_bot, add_zero, hd, hd'] at this
    omega
  obtain ⟨φ, hφ⟩ := exists_neg_similitude_of_aniso hP hP' hd hd' hn hn'
  let ψ : P →ₗ[K] V := P.subtype + P'.subtype ∘ₗ φ.toLinearMap
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have h1 : (p : V) = -((φ p : P') : V) := by
      have : (p : V) + ((φ p : P') : V) = 0 := hp
      exact eq_neg_of_add_eq_zero_left this
    have h2 : (p : V) ∈ P' := by
      rw [h1]; exact P'.neg_mem (φ p).2
    have := Submodule.disjoint_def.mp hdisj p p.2 h2
    exact Subtype.ext this
  have hsing : ∀ v ∈ LinearMap.range ψ, Q v = 0 := by
    rintro _ ⟨p, rfl⟩
    have hpol : polar Q (p : V) ((φ p : P') : V) = 0 := horth _ p.2 _ (φ p).2
    change Q ((p : V) + ((φ p : P') : V)) = 0
    rw [QuadraticMap.map_add Q, hpol, hφ p]
    ring
  have hT : Module.finrank K ↥(LinearMap.range ψ) = 2 := by
    rw [LinearMap.finrank_range_of_inj hψinj, hd]
  have hle : LinearMap.range ψ ≤ P ⊔ P' := by
    rintro _ ⟨p, rfl⟩
    exact Submodule.add_mem_sup p.2 (φ p).2
  have hs : SignPlus Q (P ⊔ P') := signPlus_iff.mpr ⟨_, hle, hsing, by rw [hd4, hT]⟩
  obtain ⟨fr, hfr⟩ := exists_frame_of_four hU hd4 hs
  exact ⟨fr, Submodule.eq_of_le_of_finrank_eq hfr (by rw [fr.finrank_span, hd4])⟩

end Planes

section Omega

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem omegaGrp_le_of_span_le {Φ Φ' : Frame Q} (hs : Φ'.span ≤ Φ.span) :
    omegaGrp Φ' ≤ omegaGrp Φ := by
  refine sup_le ?_ ?_
  · rintro _ ⟨A, rfl⟩
    refine Frame.sl2_apply_mem Φ'.La (omegaGrp Φ) (fun c => ?_) (fun c => ?_) A
    · rw [Frame.La_transvection_zero_one]
      exact eichler_mem_omegaGrp Φ (hs (Frame.e₂_mem_span Φ'))
        (Submodule.smul_mem _ _ (hs (Frame.e₁_mem_span Φ'))) Φ'.Q_e₂
        (by rw [polar_smul_right, Φ'.polar_e₂_e₁, smul_zero])
    · rw [Frame.La_transvection_one_zero]
      exact eichler_mem_omegaGrp Φ (hs (Frame.f₁_mem_span Φ'))
        (Submodule.smul_mem _ _ (hs (Frame.f₂_mem_span Φ'))) Φ'.Q_f₁
        (by rw [polar_smul_right, Φ'.polar_f₁_f₂, smul_zero])
  · rintro _ ⟨A, rfl⟩
    have hs' : Φ'.swap.span ≤ Φ.span := by rw [Frame.span_eq_swap_span]; exact hs
    refine Frame.sl2_apply_mem Φ'.swap.La (omegaGrp Φ) (fun c => ?_) (fun c => ?_) A
    · rw [Frame.La_transvection_zero_one]
      exact eichler_mem_omegaGrp Φ (hs' (Frame.e₂_mem_span Φ'.swap))
        (Submodule.smul_mem _ _ (hs' (Frame.e₁_mem_span Φ'.swap))) Φ'.swap.Q_e₂
        (by rw [polar_smul_right, Φ'.swap.polar_e₂_e₁, smul_zero])
    · rw [Frame.La_transvection_one_zero]
      exact eichler_mem_omegaGrp Φ (hs' (Frame.f₁_mem_span Φ'.swap))
        (Submodule.smul_mem _ _ (hs' (Frame.f₂_mem_span Φ'.swap))) Φ'.swap.Q_f₁
        (by rw [polar_smul_right, Φ'.swap.polar_f₁_f₂, smul_zero])

theorem omegaGrp_eq_of_span_eq {Φ Φ' : Frame Q} (hs : Φ'.span = Φ.span) :
    omegaGrp Φ' = omegaGrp Φ :=
  le_antisymm (omegaGrp_le_of_span_le hs.le) (omegaGrp_le_of_span_le hs.ge)

theorem span_map (Φ : Frame Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (Φ.map hg).span = Φ.span.map (g : V →ₗ[K] V) := by
  ext x
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨Φ.incl X, ⟨X, rfl⟩, (Frame.map_incl Φ hg X).symm⟩
  · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
    exact ⟨X, Frame.map_incl Φ hg X⟩

theorem map_swap (Φ : Frame Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : (Φ.map hg).swap = Φ.swap.map hg := rfl

theorem omegaGrp_map (Φ : Frame Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    omegaGrp (Φ.map hg) = (omegaGrp Φ).map (MulAut.conj g).toMonoidHom := by
  have h1 : (Φ.map hg).La.range = Φ.La.range.map (MulAut.conj g).toMonoidHom := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨Φ.La A, ⟨A, rfl⟩, by rw [Frame.map_La Φ hg]; rfl⟩
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      exact ⟨A, by rw [Frame.map_La Φ hg]; rfl⟩
  have h2 : (Φ.swap.map hg).La.range = Φ.swap.La.range.map (MulAut.conj g).toMonoidHom := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨Φ.swap.La A, ⟨A, rfl⟩, by rw [Frame.map_La Φ.swap hg]; rfl⟩
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      exact ⟨A, by rw [Frame.map_La Φ.swap hg]; rfl⟩
  unfold omegaGrp
  rw [map_swap, h1, h2, Subgroup.map_sup]

end Omega

section Dim

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polarNondegOn_bot' : PolarNondegOn Q (⊥ : Submodule K V) := by
  intro x hx _
  simpa using hx

theorem orth_iSup_left {ι : Type*} (S : ι → Submodule K V) (T : Submodule K V)
    (h : ∀ i, ∀ x ∈ S i, ∀ y ∈ T, polar Q x y = 0) :
    ∀ x ∈ ⨆ i, S i, ∀ y ∈ T, polar Q x y = 0 := by
  intro x hx y hy
  refine Submodule.iSup_induction S (motive := fun x => polar Q x y = 0) hx
    (fun i x hx => h i x hx y hy) (by simp)
    (fun a b ha hb => by rw [polar_add_left, ha, hb, add_zero])

theorem polarNondegOn_iSup_fin [FiniteDimensional K V] : ∀ {m : ℕ} (S : Fin m → Submodule K V),
    (∀ i, PolarNondegOn Q (S i)) → (∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, polar Q x y = 0) →
    PolarNondegOn Q (⨆ i, S i) ∧ Module.finrank K ↥(⨆ i, S i) = ∑ i, Module.finrank K ↥(S i) := by
  intro m
  induction m with
  | zero =>
    intro S _ _
    have h0 : (⨆ i : Fin 0, S i) = ⊥ := iSup_of_empty S
    rw [h0, finrank_bot, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨polarNondegOn_bot', rfl⟩
  | succ m ih =>
    intro S hreg horth
    have h1 : (⨆ i : Fin (m + 1), S i) = (⨆ i : Fin m, S i.castSucc) ⊔ S (Fin.last m) := by
      apply le_antisymm
      · refine iSup_le fun i => ?_
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact le_sup_right
        · exact le_sup_of_le_left (le_iSup (fun i : Fin m => S i.castSucc) j)
      · exact sup_le (iSup_le fun j => le_iSup S j.castSucc) (le_iSup S (Fin.last m))
    obtain ⟨hreg', hdim'⟩ := ih (fun i => S i.castSucc) (fun i => hreg _)
      (fun i j hij => horth _ _ (fun h => hij (Fin.castSucc_injective _ h)))
    have hlast : ∀ x ∈ ⨆ i : Fin m, S i.castSucc, ∀ y ∈ S (Fin.last m), polar Q x y = 0 :=
      orth_iSup_left _ _ (fun i x hx y hy => horth _ _ (Fin.castSucc_lt_last i).ne x hx y hy)
    rw [h1]
    refine ⟨CFSG.ClassicalInvolution.ModelFacts.Orth15.polarNondegOn_sup hreg' (hreg _) hlast, ?_⟩
    have hdisj : (⨆ i : Fin m, S i.castSucc) ⊓ S (Fin.last m) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxA, hxB⟩
      have : x = 0 := hreg (Fin.last m) x hxB fun y hy => hlast x hxA y hy
      simp [this]
    have := Submodule.finrank_sup_add_finrank_inf_eq (⨆ i : Fin m, S i.castSucc) (S (Fin.last m))
    rw [hdisj, finrank_bot, add_zero] at this
    rw [this, hdim', Fin.sum_univ_castSucc]

end Dim

section Pairing

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_frames_of_planes {ι : Type} [Fintype ι] {k : ℕ} (hcard : Fintype.card ι = 2 * k)
    (Pl : ι → Submodule K V) (hreg : ∀ i, PolarNondegOn Q (Pl i))
    (hdim : ∀ i, Module.finrank K ↥(Pl i) = 2) (haniso : ∀ i, ∀ s ∈ Pl i, Q s = 0 → s = 0)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ Pl i, ∀ y ∈ Pl j, polar Q x y = 0) (hspan : ⨆ i, Pl i = ⊤) :
    ∃ (Fr : Fin k → Frame Q) (e : Fin k × Bool ≃ ι),
      (∀ a, (Fr a).span = Pl (e (a, false)) ⊔ Pl (e (a, true))) ∧
      (∀ a b, a ≠ b → ∀ x ∈ (Fr a).span, ∀ y ∈ (Fr b).span, polar Q x y = 0) ∧
      ⨆ a, (Fr a).span = ⊤ := by
  classical
  let e : Fin k × Bool ≃ ι := Fintype.equivOfCardEq (by simp [hcard, mul_comm])
  have hne : ∀ a : Fin k, e (a, false) ≠ e (a, true) := fun a h => by
    have := e.injective h
    simp at this
  have hnp : ∀ i, ¬ CFSG.ClassicalInvolution.ModelFacts.MF15.SignPlus Q (Pl i) := by
    intro i hi
    obtain ⟨v, hv, hv0, hvQ⟩ := (CFSG.ClassicalInvolution.ModelFacts.MF15.signPlus_plane_iff
      (hdim i)).mp hi
    exact hv0 (haniso i v hv hvQ)
  have hex : ∀ a : Fin k, ∃ Fr : Frame Q, Fr.span = Pl (e (a, false)) ⊔ Pl (e (a, true)) :=
    fun a => exists_frame_span_eq_of_aniso (hreg _) (hreg _) (hdim _) (hdim _) (hnp _) (hnp _)
      (horth _ _ (hne a))
  choose Fr hFr using hex
  refine ⟨Fr, e, hFr, ?_, ?_⟩
  · intro a b hab x hx y hy
    rw [hFr] at hx hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    have hba : ∀ s t : Bool, e (a, s) ≠ e (b, t) := fun s t h => by
      have := e.injective h
      simp only [Prod.mk.injEq] at this
      exact hab this.1
    rw [polar_add_left, polar_add_right, polar_add_right, horth _ _ (hba false false) _ hx₁ _ hy₁,
      horth _ _ (hba false true) _ hx₁ _ hy₂, horth _ _ (hba true false) _ hx₂ _ hy₁,
      horth _ _ (hba true true) _ hx₂ _ hy₂]
    simp
  · rw [eq_top_iff, ← hspan]
    refine iSup_le fun i => ?_
    obtain ⟨⟨a, s⟩, rfl⟩ := e.surjective i
    refine le_iSup_of_le a ?_
    rw [hFr]
    cases s
    · exact le_sup_left
    · exact le_sup_right

end Pairing

section Planes

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def GoodPlanes (Q : QuadraticForm K V) (S : Set (V ≃ₗ[K] V)) {N : ℕ}
    (Pl : Fin N → Submodule K V) : Prop :=
  (∀ i, PolarNondegOn Q (Pl i)) ∧ (∀ i, Module.finrank K ↥(Pl i) = 2) ∧
    (∀ i, ∀ s ∈ Pl i, Q s = 0 → s = 0) ∧
    (∀ i j, i ≠ j → ∀ x ∈ Pl i, ∀ y ∈ Pl j, polar Q x y = 0) ∧ ⨆ i, Pl i = ⊤ ∧
    (∀ g ∈ S, ∀ i, ∀ x ∈ Pl i, g x ∈ Pl i)

theorem GoodPlanes.congr {S : Set (V ≃ₗ[K] V)} {N M : ℕ} (h : N = M)
    {Pl : Fin N → Submodule K V} (hP : GoodPlanes Q S Pl) :
    GoodPlanes Q S (fun i : Fin M => Pl (Fin.cast h.symm i)) := by
  subst h
  simpa using hP

theorem GoodPlanes.mono {S S' : Set (V ≃ₗ[K] V)} (h : S' ⊆ S) {N : ℕ}
    {Pl : Fin N → Submodule K V} (hP : GoodPlanes Q S Pl) : GoodPlanes Q S' Pl :=
  ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1, fun g hg => hP.2.2.2.2.2 g (h hg)⟩

end Planes

section Pieces

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_goodPlanes (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    (E : Subgroup (orthDerived Q)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) (hNS : OrthNoInvariantSingular Q E)
    {k : ℕ} (hk : Module.finrank K V = 4 * k) :
    ∃ Pl : Fin (2 * k) → Submodule K V,
      GoodPlanes Q {g | ∃ e ∈ E, g = ((e : orthDerived Q) : V ≃ₗ[K] V)} Pl := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Nontrivial V := nontrivial_of_card_sq hp.one_lt hcard
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  obtain ⟨n, P, hP, hPP, hPV, hPsp⟩ :=
    exists_piece_decomposition hQ hp hp2 hpl E hcomm hexp hcard hNS
  have hPdim : ∀ i, Module.finrank K ↥(P i) = 2 := fun i => by
    obtain ⟨M, -, -, -, hdim, -, -⟩ := (hP i).exists_line hK hp hp2 hpl
    rw [hdim, hord]
  have hPan : ∀ i, ∀ s ∈ P i, Q s = 0 → s = 0 := fun i =>
    (hP i).anisotropic_of_orderOf_two hK hp hp5 hpl hord
  have hPreg : ∀ i, PolarNondegOn Q (P i) := fun i => (hP i).regular
  have hV0reg : PolarNondegOn Q (planeFixSpace E) := polarNondegOn_planeFixSpace hK
  have hV0an : ∀ s ∈ planeFixSpace E, Q s = 0 → s = 0 := fun s hs hsQ =>
    eq_zero_of_singular_planeFixSpace hNS hs hsQ
  have hV0dim : Module.finrank K ↥(planeFixSpace E) ≤ 2 := finrank_planeFixSpace_le_two hNS
  have hPst : ∀ i, ∀ e ∈ E, ∀ x ∈ P i, ((e : orthDerived Q) : V ≃ₗ[K] V) x ∈ P i :=
    fun i e he x hx => (hP i).eStable e he x hx
  have hV0st : ∀ e ∈ E, ∀ x ∈ planeFixSpace E,
      ((e : orthDerived Q) : V ≃ₗ[K] V) x ∈ planeFixSpace E := by
    intro e he x hx
    have : ((e : orthDerived Q) : V ≃ₗ[K] V) x = x := hx _ ⟨e, he, rfl⟩
    rw [this]
    exact hx
  let Pl₀ : Fin (n + 1) → Submodule K V :=
    Fin.snoc (α := fun _ => Submodule K V) P (planeFixSpace E)
  have hPl₀reg : ∀ i, PolarNondegOn Q (Pl₀ i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Pl₀] using hV0reg
    · simpa [Pl₀] using hPreg j
  have hl : Pl₀ (Fin.last n) = planeFixSpace E := by simp [Pl₀]
  have hc : ∀ i : Fin n, Pl₀ i.castSucc = P i := fun i => by simp [Pl₀]
  have hPl₀orth : ∀ i j, i ≠ j → ∀ x ∈ Pl₀ i, ∀ y ∈ Pl₀ j, polar Q x y = 0 := by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · intro x hx y hy
      rw [hc] at hx hy
      exact hPP i' j' (fun h => hij (by rw [h])) x hx y hy
    · intro x hx y hy
      rw [hc] at hx
      rw [hl] at hy
      rw [polar_comm]
      exact hPV i' y hy x hx
    · intro x hx y hy
      rw [hl] at hx
      rw [hc] at hy
      exact hPV j' x hx y hy
    · exact absurd rfl hij
  have hPl₀span : ⨆ i, Pl₀ i = ⊤ := by
    rw [eq_top_iff]
    refine hPsp.trans (sup_le ?_ (iSup_le fun i => ?_))
    · exact le_iSup_of_le (Fin.last n) (by simp [Pl₀])
    · exact le_iSup_of_le i.castSucc (by simp [Pl₀])
  obtain ⟨-, hsum⟩ := polarNondegOn_iSup_fin Pl₀ hPl₀reg hPl₀orth
  rw [hPl₀span, finrank_top, hk, Fin.sum_univ_castSucc] at hsum
  have hsum' : 4 * k = 2 * n + Module.finrank K ↥(planeFixSpace E) := by
    have hfin : ∀ i : Fin n, Module.finrank K ↥(Pl₀ i.castSucc) = 2 := fun i => by
      rw [hc]; exact hPdim i
    have hfinl : Module.finrank K ↥(Pl₀ (Fin.last n)) = Module.finrank K ↥(planeFixSpace E) := by
      rw [hl]
    rw [Finset.sum_congr rfl (fun i _ => hfin i), hfinl, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hsum
    omega
  have hgood₀ : GoodPlanes Q {g | ∃ e ∈ E, g = ((e : orthDerived Q) : V ≃ₗ[K] V)} Pl₀ →
      Module.finrank K ↥(planeFixSpace E) = 2 →
      ∃ Pl : Fin (2 * k) → Submodule K V,
        GoodPlanes Q {g | ∃ e ∈ E, g = ((e : orthDerived Q) : V ≃ₗ[K] V)} Pl := fun hg h2 =>
    ⟨_, hg.congr (show n + 1 = 2 * k by omega)⟩
  rcases (show Module.finrank K ↥(planeFixSpace E) = 0 ∨ Module.finrank K ↥(planeFixSpace E) = 2 by
    omega) with h0 | h2
  ·
    have hbot : planeFixSpace E = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hPspan : ⨆ i, P i = ⊤ := by
      rw [eq_top_iff]
      refine hPsp.trans (sup_le ?_ le_rfl)
      rw [hbot]
      exact bot_le
    have hg : GoodPlanes Q {g | ∃ e ∈ E, g = ((e : orthDerived Q) : V ≃ₗ[K] V)} P :=
      ⟨hPreg, hPdim, hPan, fun i j hij => hPP i j hij, hPspan, by
        rintro g ⟨e, he, rfl⟩ i x hx
        exact hPst i e he x hx⟩
    exact ⟨_, hg.congr (show n = 2 * k by omega)⟩
  · refine hgood₀ ⟨hPl₀reg, ?_, ?_, hPl₀orth, hPl₀span, ?_⟩ h2
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hl]; exact h2
      · rw [hc]; exact hPdim j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hl]; exact hV0an
      · rw [hc]; exact hPan j
    · rintro g ⟨e, he, rfl⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hl]; exact hV0st e he
      · rw [hc]; exact hPst j e he

end Pieces

section Frames

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_frames_of_goodPlanes (h2 : (2 : K) ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Set (V ≃ₗ[K] V)} (hSO : ∀ g ∈ S, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hSp : ∀ g ∈ S, g ^ p = 1) {k : ℕ} {Pl : Fin (2 * k) → Submodule K V}
    (hGP : GoodPlanes Q S Pl) :
    ∃ Fr : Fin k → Frame Q,
      (∀ a b, a ≠ b → ∀ x ∈ (Fr a).span, ∀ y ∈ (Fr b).span, polar Q x y = 0) ∧
      ⨆ a, (Fr a).span = ⊤ ∧ ∀ g ∈ S, g ∈ ⨆ a, omegaGrp (Fr a) := by
  classical
  obtain ⟨hreg, hdim, haniso, horth, hspan, hst⟩ := hGP
  obtain ⟨Fr, e, hFr, hFrorth, hFrspan⟩ := exists_frames_of_planes (ι := Fin (2 * k))
    (k := k) (by simp) Pl hreg hdim haniso horth hspan
  refine ⟨Fr, hFrorth, hFrspan, fun g hg => ?_⟩
  have hxs : ∀ a, ∀ y ∈ (Fr a).span, g y ∈ (Fr a).span := by
    intro a y hy
    rw [hFr a] at hy ⊢
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add]
    exact Submodule.add_mem_sup (hst g hg _ y₁ hy₁) (hst g hg _ y₂ hy₂)
  exact mem_iSup_La_swapLa_of_odd h2 Fr hFrorth hFrspan (hp.odd_of_ne_two hp2) (hSO g hg)
    (hSp g hg) hxs

end Frames

section FramePairs

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem frame_span_eq_pairs (F : Frame Q) :
    F.span = Submodule.span K {F.e₁, F.f₁} ⊔ Submodule.span K {F.e₂, F.f₂} := by
  ext x
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨X, rfl⟩
    refine ⟨X 0 0 • F.e₁ + X 1 1 • F.f₁, ?_, (-X 0 1) • F.e₂ + X 1 0 • F.f₂, ?_, ?_⟩
    · exact Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩
    · exact Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩
    · rw [Frame.incl_apply]
      abel
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hz
    refine ⟨!![a, -c; d, b], ?_⟩
    rw [Frame.incl_apply]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, neg_neg]
    abel

@[expose] def pairVec (F : Frame Q) (b s : Bool) : V :=
  if b then (if s then F.e₂ else F.f₂) else (if s then F.e₁ else F.f₁)

theorem pairVec_mem_span (F : Frame Q) (b s : Bool) : pairVec F b s ∈ F.span := by
  cases b <;> cases s
  · exact Frame.f₁_mem_span F
  · exact Frame.e₁_mem_span F
  · exact Frame.f₂_mem_span F
  · exact Frame.e₂_mem_span F

theorem Q_pairVec (F : Frame Q) (b s : Bool) : Q (pairVec F b s) = 0 := by
  cases b <;> cases s <;> simp [pairVec, F.Q_e₁, F.Q_f₁, F.Q_e₂, F.Q_f₂]

theorem polar_pairVec_not (F : Frame Q) (b s : Bool) :
    polar Q (pairVec F b s) (pairVec F b (!s)) = 1 := by
  cases b <;> cases s <;>
    simp [pairVec, F.polar_e₁_f₁, F.polar_f₁_e₁, F.polar_e₂_f₂, F.polar_f₂_e₂]

theorem polar_pairVec_of_ne (F : Frame Q) {b b' : Bool} (h : b ≠ b') (s t : Bool) :
    polar Q (pairVec F b s) (pairVec F b' t) = 0 := by
  cases b <;> cases b' <;> first | exact absurd rfl h | skip
  all_goals cases s <;> cases t <;>
    simp [pairVec, F.polar_e₁_e₂, F.polar_e₁_f₂, F.polar_f₁_e₂, F.polar_f₁_f₂,
      F.polar_e₂_e₁, F.polar_f₂_e₁, F.polar_e₂_f₁, F.polar_f₂_f₁]

theorem span_pair_eq (F : Frame Q) (b : Bool) :
    Submodule.span K {pairVec F b true, pairVec F b false} =
      if b then Submodule.span K {F.e₂, F.f₂} else Submodule.span K {F.e₁, F.f₁} := by
  cases b <;> simp [pairVec]

end FramePairs

section HypFamily

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def frameFam {k n : ℕ} (Fr : Fin k → Frame Q) (ι : Fin k × Bool ≃ Fin n) :
    Fin n → Bool → V := fun j s => pairVec (Fr (ι.symm j).1) (ι.symm j).2 s

theorem isHypFam_frameFam {k n : ℕ} (Fr : Fin k → Frame Q) (ι : Fin k × Bool ≃ Fin n)
    (horth : ∀ a b, a ≠ b → ∀ x ∈ (Fr a).span, ∀ y ∈ (Fr b).span, polar Q x y = 0) :
    IsHypFam Q (frameFam Fr ι) := by
  refine ⟨fun j s => Q_pairVec (Fr _) _ _, fun j j' hjj' s t => ?_, fun j s =>
    polar_pairVec_not (Fr _) _ _⟩
  by_cases ha : (ι.symm j).1 = (ι.symm j').1
  · have hb : (ι.symm j).2 ≠ (ι.symm j').2 := by
      intro hb
      apply hjj'
      apply ι.symm.injective
      exact Prod.ext ha hb
    simp only [frameFam]
    rw [ha]
    exact polar_pairVec_of_ne (Fr _) hb s t
  · exact horth _ _ ha _ (pairVec_mem_span (Fr _) _ _) _ (pairVec_mem_span (Fr _) _ _)

end HypFamily

section HypPlane

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polarNondegOn_span_hyp {e f : V} (hef : polar Q e f = 1) (he : Q e = 0) (hf : Q f = 0) :
    PolarNondegOn Q (Submodule.span K {e, f}) ∧
      Module.finrank K ↥(Submodule.span K {e, f}) = 2 := by
  have hee : polar Q e e = 0 := polar_self_eq_zero he
  have hff : polar Q f f = 0 := polar_self_eq_zero hf
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  have hli : LinearIndependent K ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (fun v => polar Q v f) hab
    have h2 := congrArg (fun v => polar Q v e) hab
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_zero_left, hef, hff, hfe, hee,
      mul_one, mul_zero, add_zero, zero_add] at h1 h2
    exact ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · intro x hx hxy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    have h1 := hxy f (Submodule.subset_span (by simp))
    have h2 := hxy e (Submodule.subset_span (by simp))
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, hef, hff, hfe, hee, mul_one,
      mul_zero, add_zero, zero_add] at h1 h2
    rw [h1, h2]
    simp
  · have hr : Set.range ![e, f] = {e, f} := by
      ext x
      simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
    have := finrank_span_eq_card hli
    rw [hr] at this
    rw [this]
    simp

end HypPlane

section SpinFrame

variable {K : Type} [Field K]

theorem toFrame_not' {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}
    (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool) :
    F₀.toFrame hij s (!t) = (F₀.toFrame hij s t).swap := by
  cases t <;> rfl

theorem ne_of_pairing {k n : ℕ} (ι : Fin k × Bool ≃ Fin n) (a : Fin k) :
    ι (a, false) ≠ ι (a, true) := fun h => by simpa using ι.injective h

@[expose] noncomputable def spinFrameGroup (n : ℕ) (K : Type) [Field K] (hn : 3 ≤ n) {k : ℕ}
    (ι : Fin k × Bool ≃ Fin n) : Subgroup (spinGroup (quadPlus n K)) :=
  ⨆ a : Fin k, ((plusFrame n K hn).longSL2 (ne_of_pairing ι a) true true).range ⊔
    ((plusFrame n K hn).longSL2 (ne_of_pairing ι a) true false).range

theorem map_spinFrameGroup (n : ℕ) (hn : 3 ≤ n) {k : ℕ} (ι : Fin k × Bool ≃ Fin n) :
    (spinFrameGroup n K hn ι).map (spinAction (quadPlus n K)) =
      ⨆ a : Fin k, omegaGrp ((plusFrame n K hn).toFrame (ne_of_pairing ι a) true true) := by
  unfold spinFrameGroup
  rw [Subgroup.map_iSup]
  refine iSup_congr fun a => ?_
  rw [Subgroup.map_sup, map_longSL2_range, map_longSL2_range, omegaGrp]
  have e : (plusFrame n K hn).toFrame (ne_of_pairing ι a) true false =
      ((plusFrame n K hn).toFrame (ne_of_pairing ι a) true true).swap :=
    toFrame_not' _ _ true true
  rw [e]

end SpinFrame

section SpinMain

variable {K : Type} [Field K] [Finite K]

theorem card_map_of_disjoint_ker {A B : Type*} [Group A] [Group B] (φ : A →* B)
    {E : Subgroup A} (h : Disjoint E φ.ker) : Nat.card (E.map φ) = Nat.card E := by
  have hinj : Function.Injective (φ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : A) ∈ φ.ker := hx
    exact Subtype.ext (Subgroup.disjoint_def.mp h x.2 hx')
  have hrange : (φ.comp E.subtype).range = E.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

omit [Finite K] in
theorem map_span_pair {V : Type} [AddCommGroup V] [Module K V] (f : V →ₗ[K] V) (a b : V) :
    (Submodule.span K {a, b}).map f = Submodule.span K {f a, f b} := by
  rw [Submodule.map_span, Set.image_pair]

theorem exists_spin_conj_of_goodPlanes (hodd : Odd (Nat.card K)) {n : ℕ} (hn : 3 ≤ n) {k : ℕ}
    (hnk : n = 2 * k) (ι : Fin k × Bool ≃ Fin n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Ep : Subgroup (spinGroup (quadPlus n K))) (hexp : ∀ x ∈ Ep, x ^ p = 1)
    {Pl : Fin (2 * k) → Submodule K (Fin n ⊕ Fin n → K)}
    (hGP : GoodPlanes (quadPlus n K) {g | ∃ e ∈ Ep, g = spinAction (quadPlus n K) e} Pl) :
    ∃ x : spinGroup (quadPlus n K), ∀ e ∈ Ep, x * e * x⁻¹ ∈ spinFrameGroup n K hn ι := by
  classical
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  haveI : Invertible (2 : K) := invertibleOfNonzero h2
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hQnd' : (quadPlus n K).Nondegenerate := nondegenerate_quadPlus n K
  have hker2 : ∀ c ∈ (spinAction (quadPlus n K)).ker, c * c = 1 := by
    intro c hc
    rcases (mem_ker_spinAction_iff (quadPlus n K) hQnd' c).mp hc with rfl | rfl
    · exact one_mul 1
    · apply Subtype.ext
      simp
  obtain ⟨Fr, horth, hspan, hFE⟩ := exists_frames_of_goodPlanes h2 hp hp2
    (S := {g | ∃ e ∈ Ep, g = spinAction (quadPlus n K) e})
    (by
      rintro g ⟨e, he, rfl⟩
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => map_spinAction _ e w)
    (by
      rintro g ⟨e, he, rfl⟩
      rw [← map_pow, hexp e he, map_one]) hGP
  set v := frameFam Fr ι with hvdef
  have hv : IsHypFam (quadPlus n K) v := isHypFam_frameFam Fr ι horth
  have hv' : IsHypFam (quadPlus n K) (plusFrame n K hn).vec :=
    ⟨(plusFrame n K hn).map_vec, fun i j hij s t => (plusFrame n K hn).polar_vec_of_ne hij s t,
      (plusFrame n K hn).polar_vec_not⟩
  have hvι : ∀ a b s, v (ι (a, b)) s = pairVec (Fr a) b s := by
    intro a b s
    simp [hvdef, frameFam]
  set j₀ : Fin n := ι (⟨k - 1, by omega⟩, true) with hj₀
  set P : Submodule K (Fin n ⊕ Fin n → K) := Submodule.span K {v j₀ true, v j₀ false} with hPdef
  obtain ⟨hPreg, hPdim⟩ := polarNondegOn_span_hyp (Q := quadPlus n K) (e := v j₀ true)
    (f := v j₀ false) (by simpa using hv.2.2 j₀ true) (hv.1 j₀ true) (hv.1 j₀ false)
  have hP : ((quadPlus n K).restrict P).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_restrict hPreg)
  obtain ⟨x, h, hhP, hhfix, hxv⟩ := exists_spin_normalization hodd hQnd' hv hv' hP hPdim.ge
  set g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) := spinAction (quadPlus n K) x with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => map_spinAction _ x w
  have hpair : ∀ j : Fin n, (Submodule.span K {v j true, v j false}).map (g : _ →ₗ[K] _) =
      Submodule.span K {(plusFrame n K hn).vec j true, (plusFrame n K hn).vec j false} := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      have hmapP : P.map (h : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = P :=
        Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact hhP y hy)
          (by rw [LinearEquiv.finrank_map_eq])
      have e1 : Submodule.span K {v j₀ true, v j₀ false} = P := rfl
      rw [e1]
      calc P.map (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) =
          ((P.map (h : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))).map
            (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))) := by rw [hmapP]
        _ = _ := by
          rw [hPdef, map_span_pair, map_span_pair]
          simp only [LinearEquiv.coe_coe]
          rw [← hxv j₀ true, ← hxv j₀ false]
    · have hfix : ∀ s, h (v j s) = v j s := by
        intro s
        apply hhfix
        intro y hy
        obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
        rw [polar_add_left, polar_smul_left, polar_smul_left, hv.polar_eq, hv.polar_eq,
          if_neg (fun hh => hj hh.1.symm), if_neg (fun hh => hj hh.1.symm)]
        simp
      have hgv : ∀ s, g (v j s) = (plusFrame n K hn).vec j s := fun s => by
        rw [hg, hxv j s, hfix s]
      rw [map_span_pair]
      simp only [LinearEquiv.coe_coe, hgv]
  have hFrspan : ∀ a, (Fr a).span =
      Submodule.span K {v (ι (a, false)) true, v (ι (a, false)) false} ⊔
        Submodule.span K {v (ι (a, true)) true, v (ι (a, true)) false} := by
    intro a
    rw [frame_span_eq_pairs]
    simp only [hvι]
    rw [span_pair_eq (Fr a) false, span_pair_eq (Fr a) true]
    simp
  have hFr'span : ∀ a, ((plusFrame n K hn).toFrame (ne_of_pairing ι a) true true).span =
      Submodule.span K {(plusFrame n K hn).vec (ι (a, false)) true,
        (plusFrame n K hn).vec (ι (a, false)) false} ⊔
        Submodule.span K {(plusFrame n K hn).vec (ι (a, true)) true,
          (plusFrame n K hn).vec (ι (a, true)) false} :=
    fun a => frame_span_eq_pairs _
  have hspanmap : ∀ a, ((Fr a).map hgO).span =
      ((plusFrame n K hn).toFrame (ne_of_pairing ι a) true true).span := by
    intro a
    rw [span_map, hFrspan a, Submodule.map_sup, hpair, hpair, hFr'span a]
  have hmapΩ : ∀ a, (omegaGrp (Fr a)).map (MulAut.conj g).toMonoidHom =
      omegaGrp ((plusFrame n K hn).toFrame (ne_of_pairing ι a) true true) := fun a => by
    rw [← omegaGrp_map _ hgO, omegaGrp_eq_of_span_eq (hspanmap a)]
  refine ⟨x, fun e he => ?_⟩
  have hmem : spinAction (quadPlus n K) (x * e * x⁻¹) ∈
      (spinFrameGroup n K hn ι).map (spinAction (quadPlus n K)) := by
    rw [map_spinFrameGroup n hn ι, map_mul, map_mul, map_inv]
    have h0 : spinAction (quadPlus n K) e ∈ ⨆ a, omegaGrp (Fr a) := hFE _ ⟨e, he, rfl⟩
    have h2' : g * (spinAction (quadPlus n K) e) * g⁻¹ ∈
        (⨆ a, omegaGrp (Fr a)).map (MulAut.conj g).toMonoidHom := ⟨_, h0, rfl⟩
    rw [Subgroup.map_iSup] at h2'
    exact (iSup_mono (fun a => le_of_eq (hmapΩ a))) h2'
  obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hmem
  set y := x * e * x⁻¹ with hy
  have hy1 : y ^ p = 1 := by rw [hy, conj_pow, hexp e he]; group
  set z := y * b⁻¹ with hz
  have hzker : z ∈ (spinAction (quadPlus n K)).ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hbeq, mul_inv_cancel]
  have hzz := hker2 z hzker
  have hzc := ker_spinAction_le_center (quadPlus n K) hzker
  have hzb : Commute z b := (Subgroup.mem_center_iff.mp hzc b).symm
  have hyzb : y = z * b := by rw [hz]; group
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega : p ≠ 2)
  have hzp : z ^ p = z := by rw [hm, pow_succ, pow_mul, pow_two, hzz, one_pow, one_mul]
  have h3 : z * b ^ p = 1 := by
    have := hy1
    rw [hyzb, hzb.mul_pow, hzp] at this
    exact this
  have h4 : z = (b ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h3
  rw [hyzb, h4]
  exact mul_mem (inv_mem (pow_mem hb p)) hb

theorem exists_spin_conj_frameGroup (hodd : Odd (Nat.card K)) {n : ℕ} (hn : 3 ≤ n) {k : ℕ}
    (hnk : n = 2 * k) (ι : Fin k × Bool ≃ Fin n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpl : p ≠ ringChar K) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    (Ep : Subgroup (spinGroup (quadPlus n K))) (hexp : ∀ x ∈ Ep, x ^ p = 1)
    (hcard : Nat.card Ep = p ^ 2)
    (hNS : ∀ T : Submodule K (Fin n ⊕ Fin n → K),
      (∀ e ∈ Ep, ∀ v ∈ T, spinAction (quadPlus n K) e v ∈ T) →
      (∀ v ∈ T, quadPlus n K v = 0) → T = ⊥) :
    ∃ x : spinGroup (quadPlus n K), ∀ e ∈ Ep, x * e * x⁻¹ ∈ spinFrameGroup n K hn ι := by
  classical
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  haveI : Invertible (2 : K) := invertibleOfNonzero h2
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hQnd : (polarBilin (quadPlus n K)).Nondegenerate := nondegenerate_polarBilin_quadPlus n K
  have hQnd' : (quadPlus n K).Nondegenerate := nondegenerate_quadPlus n K
  haveI : Finite (spinGroup (quadPlus n K)) :=
    finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hrange : (spinAction (quadPlus n K)).range = orthDerived (quadPlus n K) :=
    range_spinAction_quadPlus_eq_commutator hn
  let sa : spinGroup (quadPlus n K) →* orthDerived (quadPlus n K) :=
    (spinAction (quadPlus n K)).codRestrict (orthDerived (quadPlus n K))
      (fun x => by rw [← hrange]; exact ⟨x, rfl⟩)
  have hker2 : ∀ c ∈ (spinAction (quadPlus n K)).ker, c * c = 1 := by
    intro c hc
    rcases (mem_ker_spinAction_iff (quadPlus n K) hQnd' c).mp hc with rfl | rfl
    · exact one_mul 1
    · apply Subtype.ext
      simp
  have hdisj : Disjoint Ep sa.ker := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxk
    have hxk' : x ∈ (spinAction (quadPlus n K)).ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hxk
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega : p ≠ 2)
    have hxx := hker2 x hxk'
    have : x ^ p = x := by rw [hm, pow_succ, pow_mul, pow_two, hxx, one_pow, one_mul]
    rw [← this]
    exact hexp x hxE
  set E : Subgroup (orthDerived (quadPlus n K)) := Ep.map sa with hE
  have hcardE : Nat.card E = p ^ 2 := by
    rw [hE, card_map_of_disjoint_ker sa hdisj, hcard]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hcomm' := IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := Ep) hcard
  have hcommEp : ∀ a ∈ Ep, ∀ b ∈ Ep, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm'.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcommEp a ha b hb]
  have hexpE : ∀ x ∈ E, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hexp a ha, map_one]
  have hNSE : OrthNoInvariantSingular (quadPlus n K) E := fun T hTi hTs =>
    hNS T (fun e he v hv => hTi (sa e) ⟨e, he, rfl⟩ v hv) hTs
  have hk : Module.finrank K (Fin n ⊕ Fin n → K) = 4 * k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨Pl, hGP⟩ := exists_goodPlanes hQnd hp hp5 hpl hord E hcommE hexpE hcardE hNSE hk
  exact exists_spin_conj_of_goodPlanes hodd hn hnk ι hp (by omega) Ep hexp
    (hGP.mono (by
      rintro g ⟨e, he, rfl⟩
      exact ⟨sa e, ⟨e, he, rfl⟩, rfl⟩))

end SpinMain

end CFSG.LieType.SeitzGeneration.ExcHigh

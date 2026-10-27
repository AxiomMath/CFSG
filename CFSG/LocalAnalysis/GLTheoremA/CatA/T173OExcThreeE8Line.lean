module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE8Lang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE8Frame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.LinearCovers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.StandardType CFSG.StandardType.TableBExcTwo CFSG.StandardType.TableBExcTwoTB
open CFSG.StandardType.TableBExcTwoFusion CFSG.StandardType.ExcFrameIso
  CFSG.StandardType.ExcFrames
open CFSG.SeitzReduction.E8Pilot CFSG.SeitzReduction.EPilot
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.PartOne.KE (twistedFixedPoints)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.LocalAnalysis.GLTheoremA.I142N CFSG.LocalAnalysis.GLTheoremA.FullCover

section FrameDiag


private theorem frameDiag_lineRep {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    ExcFrames.frameDiag (τ := .E8) ζ hζ (e8FrameLambda e8FrameLineRep) =
      rootDiagUnit .E8
        (TableBExc.E6Three.zetaVec ζ hζ (Pi.single (6 : Fin Tag.E8.rank) 2)) := by
  rw [ExcFrames.frameDiag, frameCoord_e8FrameLambda_lineRep]

end FrameDiag

section CertBase


variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
noncomputable def e8LineP : Subgroup (ModGL .E8 (e8LangField K)) :=
  rootSpan .E8 (e8LangField K) (parabolicRoots .E8 (e6Nodes .E8)) ⊓
    twistedFixedPoints (e8LangN K)
      (Units.map (entrywiseHom (iterateFrobenius (e8LangField K) 2 1)))

noncomputable def e8LineComp {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) :
    Subgroup ↥(adjointGroup .E8 K) :=
  ((e8LineP K).subgroupOf (langModel .E8 K (e8LangField K) (e8LangG0 hω))).map
    (langModelMulEquiv .E8 K (e8LangField K) (e8LangG0 hω)).symm.toMonoidHom

private theorem orderOf_units_map_ext {ω : (FiniteField.Extension K 2 2)ˣ}
    (hω : orderOf ω = 3) :
    orderOf (Units.map (algebraMap (FiniteField.Extension K 2 2) (e8LangField K)).toMonoidHom
      ω) = 3 := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, hω3, map_one]
  · intro h
    have h1 : Units.map (algebraMap (FiniteField.Extension K 2 2) (e8LangField K)).toMonoidHom ω =
        Units.map (algebraMap (FiniteField.Extension K 2 2) (e8LangField K)).toMonoidHom 1 := by
      simpa using h
    have h2 := Units.map_injective
      (algebraMap (FiniteField.Extension K 2 2) (e8LangField K)).injective h1
    rw [h2] at hω
    simp at hω

private theorem frameProd_inv {L : Type} [Field L] (P : SL2 L) :
    frameProd L frameE8 P⁻¹ = (frameProd L frameE8 P)⁻¹ := by
  set a : ↥(adjointGroup .E8 L) := frameProd L frameE8 P with ha
  set b : ↥(adjointGroup .E8 L) := frameProd L frameE8 P⁻¹ with hb
  have h := frameProd_mul (L := L) frameE8 P P⁻¹
  rw [mul_inv_cancel] at h
  have h1 : frameProd L frameE8 (1 : SL2 L) = 1 := by
    rw [frameProd]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact map_one _
  rw [h1] at h
  change 1 = a * b at h
  calc b = 1 * b := (one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * b) := by group
    _ = a⁻¹ * 1 := by rw [h]
    _ = a⁻¹ := mul_one _

private theorem frameProd_langP_conj_rootSL2 {ω : (FiniteField.Extension K 2 2)ˣ}
    (hω : orderOf ω = 3) (B : SL2 (FiniteField.Extension K 2 2)) :
    (langElt (K := K) frameE8 hω : ModGL .E8 (FiniteField.Extension K 2 2))⁻¹ *
      rootSL2 .E8 (FiniteField.Extension K 2 2) (frameE8Root 3) B *
      (langElt (K := K) frameE8 hω : ModGL .E8 (FiniteField.Extension K 2 2)) =
      rootSL2 .E8 (FiniteField.Extension K 2 2) (frameE8Root 3)
        ((langP (sq_add_self_add_one_eq_zero hω))⁻¹ * B *
          (langP (sq_add_self_add_one_eq_zero hω))) := by
  let K₂ := FiniteField.Extension K 2 2
  set P : SL2 K₂ := langP (sq_add_self_add_one_eq_zero hω) with hPdef
  set a : adjointGroup .E8 K₂ := frameProd K₂ frameE8 P⁻¹ with ha
  set b : adjointGroup .E8 K₂ := frameProd K₂ frameE8 P with hb
  have hP : b⁻¹ = a := by
    rw [ha, hb]
    exact (frameProd_inv P).symm
  have h3 : a * rho K₂ frameE8 3 B * a⁻¹ = rho K₂ frameE8 3 (P⁻¹ * B * P) := by
    change frameProd K₂ frameE8 P⁻¹ * rho K₂ frameE8 3 B *
      (frameProd K₂ frameE8 P⁻¹)⁻¹ = rho K₂ frameE8 3 (P⁻¹ * B * P)
    rw [frameProd_conj_rho (F := frameE8) 3 (A := P⁻¹) (B := B), inv_inv]
  change ((b : adjointGroup .E8 K₂) : ModGL .E8 K₂)⁻¹ *
    rootSL2 .E8 K₂ (frameE8Root 3) B * ((b : adjointGroup .E8 K₂) : ModGL .E8 K₂) =
    rootSL2 .E8 K₂ (frameE8Root 3) (P⁻¹ * B * P)
  rw [show ((b : adjointGroup .E8 K₂) : ModGL .E8 K₂)⁻¹ =
      ((a : adjointGroup .E8 K₂) : ModGL .E8 K₂) from by rw [← hP]; rfl]
  rw [show rootSL2 .E8 K₂ (frameE8Root 3) B =
      ((rho K₂ frameE8 3 B : adjointGroup .E8 K₂) : ModGL .E8 K₂) from rfl]
  rw [show rootSL2 .E8 K₂ (frameE8Root 3) (P⁻¹ * B * P) =
      ((rho K₂ frameE8 3 (P⁻¹ * B * P) : adjointGroup .E8 K₂) : ModGL .E8 K₂) from rfl]
  have hb : b = a⁻¹ := by rw [← hP, inv_inv]
  rw [show b = a⁻¹ from hb]
  change ((a * rho K₂ frameE8 3 B * a⁻¹ : adjointGroup .E8 K₂) : ModGL .E8 K₂) =
    ((rho K₂ frameE8 3 (P⁻¹ * B * P) : adjointGroup .E8 K₂) : ModGL .E8 K₂)
  rw [h3]

private theorem coe_langModel_rho_eq {ω : (FiniteField.Extension K 2 2)ˣ}
    (hω : orderOf ω = 3) (A : SL2 K) :
    ((langModelMulEquiv .E8 K (e8LangField K) (e8LangG0 hω) (rho K frameE8 3 A) :
        ModGL .E8 (e8LangField K))) =
      baseChangeGL (algebraMap (FiniteField.Extension K 2 2) (e8LangField K))
        (rootSL2 .E8 (FiniteField.Extension K 2 2) (frameE8Root 3)
          ((langP (sq_add_self_add_one_eq_zero hω))⁻¹ *
            Matrix.SpecialLinearGroup.map
              (algebraMap K (FiniteField.Extension K 2 2)) A *
            (langP (sq_add_self_add_one_eq_zero hω)))) := by
  let K₂ := FiniteField.Extension K 2 2
  let L := e8LangField K
  let ι : K →+* K₂ := algebraMap K K₂
  set P : SL2 K₂ := langP (sq_add_self_add_one_eq_zero hω) with hPdef
  set B : SL2 K₂ := Matrix.SpecialLinearGroup.map ι A with hBdef
  set j : K₂ →+* L := algebraMap K₂ L with hjdef
  change ((langModelMulEquiv .E8 K L (e8LangG0 hω) (rho K frameE8 3 A) : ModGL .E8 L)) =
    baseChangeGL j (rootSL2 .E8 K₂ (frameE8Root 3) (P⁻¹ * B * P))
  rw [coe_langModelMulEquiv]
  simp only [inv_inv]
  unfold e8LangG0
  have hmiddle : baseChangeGL (algebraMap K L)
      ((rho K frameE8 3 A : adjointGroup .E8 K) : ModGL .E8 K) =
      baseChangeGL j (rootSL2 .E8 K₂ (frameE8Root 3) B) := by
    rw [IsScalarTower.algebraMap_eq K K₂ L, ← baseChangeGL_baseChangeGL,
      ← TableBExcTwo.coe_adjointMap, adjointMap_rho, coe_rho]
    rfl
  rw [hmiddle]
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (baseChangeGL j)
  exact frameProd_langP_conj_rootSL2 hω B

private theorem frameE8Root_three_mem_parabolicRoots :
    frameE8Root 3 ∈ parabolicRoots .E8 (e6Nodes .E8) := by
  refine ⟨frameE8.isRoot 3, fun i hi => ?_⟩
  fin_cases i <;> simp_all [e6Nodes] <;> decide +kernel

theorem rho_three_mem_e8LineComp (hK : Nat.card K = 2)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) (A : SL2 K) :
    rho K frameE8 3 A ∈ e8LineComp hω := by
  let K₂ := FiniteField.Extension K 2 2
  let L := e8LangField K
  have hle := langModel_le_twModel (τ := .E8) (K := K) (L := L)
    (Fr := iterateFrobenius L 2 1)
    (fun c => by rw [iterateFrobenius_def, hK, pow_one]) (e8LangG0_mem hω)
    (frob_e8LangG0 hK hω)
  have hroot : ((langModelMulEquiv .E8 K L (e8LangG0 hω) (rho K frameE8 3 A) :
      ModGL .E8 L)) ∈ rootSpan .E8 L (parabolicRoots .E8 (e6Nodes .E8)) := by
    rw [coe_langModel_rho_eq hω A]
    have hsub : ({frameE8Root 3, -frameE8Root 3} : Set (Fin Tag.E8.rank → ℤ)) ⊆
        parabolicRoots .E8 (e6Nodes .E8) := by
      intro α hα
      rcases hα with rfl | rfl
      · exact frameE8Root_three_mem_parabolicRoots
      · exact neg_mem_parabolicRoots frameE8Root_three_mem_parabolicRoots
    exact rootSpan_mono hsub (map_baseChangeGL_rootSpan_le _ _
      (Subgroup.mem_map_of_mem _
        (rootSL2_mem_rootSpan_pair (frameE8.isRoot 3) _)))
  have htw : ((langModelMulEquiv .E8 K L (e8LangG0 hω) (rho K frameE8 3 A) :
      ModGL .E8 L)) ∈ twistedFixedPoints (e8LangN K)
      (Units.map (entrywiseHom (iterateFrobenius L 2 1))) :=
    (mem_twModel.1
      (hle (langModelMulEquiv .E8 K L (e8LangG0 hω) (rho K frameE8 3 A)).2)).2
  refine Subgroup.mem_map.2
    ⟨langModelMulEquiv .E8 K L (e8LangG0 hω) (rho K frameE8 3 A), ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨hroot, htw⟩
  · exact (langModelMulEquiv .E8 K L (e8LangG0 hω)).symm_apply_apply _

theorem e8LineComp_le_centralizer (hK : Nat.card K = 2)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) :
    e8LineComp hω ≤ Subgroup.centralizer
      ({tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep)} :
        Set ↥(adjointGroup .E8 K)) := by
  let K₂ := FiniteField.Extension K 2 2
  let L := e8LangField K
  let ζ : Lˣ := Units.map (algebraMap K₂ L).toMonoidHom ω
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hζ3 : ζ ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
  have hζo : orderOf ζ = 3 := orderOf_units_map_ext hω
  let a : ModGL .E8 L :=
    rootDiagUnit .E8 (TableBExc.E6Three.zetaVec ζ hζ3 (Pi.single 6 2))
  have hφd : ((langModelMulEquiv .E8 K L (e8LangG0 hω)
      (tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep)) : ModGL .E8 L)) = a := by
    rw [coe_langModelMulEquiv_tE hK hω hω3, frameDiag_lineRep]
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
  have hpP : (p : ModGL .E8 L) ∈ e8LineP K := hp
  have hpRoot : (p : ModGL .E8 L) ∈
      rootSpan .E8 L (parabolicRoots .E8 (e6Nodes .E8)) :=
    (Subgroup.mem_inf.1 hpP).1
  have hfam : (p : ModGL .E8 L) ∈ familyCentralizer .E8 L
      (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ3 (Pi.single 6 2)) := by
    refine (rootSpan_mono (e6Roots_subset_familyKernel_lineRep hζo hζ3)).trans ?_ hpRoot
    exact le_sup_right.trans (familyGroup_le_familyCentralizer _)
  have hconj := (mem_familyCentralizer.1 hfam).2 ()
  have hpa : a * (p : ModGL .E8 L) = (p : ModGL .E8 L) * a := by
    calc a * (p : ModGL .E8 L) = (a * (p : ModGL .E8 L) * a⁻¹) * a := by group
      _ = (p : ModGL .E8 L) * a := by rw [hconj]
  have hcomm : Commute (p : ModGL .E8 L) a := hpa.symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  apply (langModelMulEquiv .E8 K L (e8LangG0 hω)).injective
  apply Subtype.ext
  simp only [map_mul, Subgroup.coe_mul]
  have hφx : (langModelMulEquiv .E8 K L (e8LangG0 hω))
      ((langModelMulEquiv .E8 K L (e8LangG0 hω)).symm.toMonoidHom p) = p :=
    (langModelMulEquiv .E8 K L (e8LangG0 hω)).apply_symm_apply p
  rw [hφx, hφd]
  exact hcomm.symm

private theorem commute_langImage_lineRep (hK : Nat.card K = 2)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3)
    {c : ↥(adjointGroup .E8 K)} {a : ModGL .E8 (e8LangField K)}
    (hφd : ((langModelMulEquiv .E8 K (e8LangField K) (e8LangG0 hω)
      (tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep)) :
        ModGL .E8 (e8LangField K))) = a)
    (hc : c ∈ Subgroup.centralizer
      ({tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep)} : Set ↥(adjointGroup .E8 K))) :
    Commute ((langModelMulEquiv .E8 K (e8LangField K) (e8LangG0 hω)) c :
      ModGL .E8 (e8LangField K)) a := by
  have hcd : tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep) * c =
      c * tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep) :=
    Subgroup.mem_centralizer_iff.mp hc _ rfl
  have h := congrArg (fun z : ↥(adjointGroup .E8 K) =>
    (((langModelMulEquiv .E8 K (e8LangField K) (e8LangG0 hω)) z :
      ModGL .E8 (e8LangField K)))) hcd
  simp only [map_mul, Subgroup.coe_mul] at h
  rw [hφd] at h
  exact h.symm

private theorem mem_normalizer_e8LineComp_of_lang {ω : (FiniteField.Extension K 2 2)ˣ}
    (hω : orderOf ω = 3) {c : ↥(adjointGroup .E8 K)}
    (hNP : ((langModelMulEquiv .E8 K (e8LangField K) (e8LangG0 hω)) c :
        ModGL .E8 (e8LangField K)) ∈
      Subgroup.normalizer (e8LineP K : Set (ModGL .E8 (e8LangField K)))) :
    c ∈ Subgroup.normalizer (e8LineComp hω : Set ↥(adjointGroup .E8 K)) := by
  let L := e8LangField K
  let φ := langModelMulEquiv .E8 K L (e8LangG0 hω)
  have hQ : (φ c : ↥(langModel .E8 K L (e8LangG0 hω))) ∈ Subgroup.normalizer
      ((e8LineP K).subgroupOf (langModel .E8 K L (e8LangG0 hω)) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hNP (x : ModGL .E8 L)
  have hnorm := Subgroup.map_equiv_normalizer_eq
    ((e8LineP K).subgroupOf (langModel .E8 K L (e8LangG0 hω))) φ.symm
  rw [e8LineComp, ← hnorm, Subgroup.mem_map_equiv]
  exact hQ

theorem centralizer_le_normalizer_e8LineComp (hK : Nat.card K = 2)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) :
    Subgroup.centralizer
        ({tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep)} :
          Set ↥(adjointGroup .E8 K)) ≤
      Subgroup.normalizer (e8LineComp hω : Set ↥(adjointGroup .E8 K)) := by
  let K₂ := FiniteField.Extension K 2 2
  let L := e8LangField K
  let ζ : Lˣ := Units.map (algebraMap K₂ L).toMonoidHom ω
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hζ3 : ζ ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
  have hζo : orderOf ζ = 3 := orderOf_units_map_ext hω
  let a : ModGL .E8 L :=
    rootDiagUnit .E8 (TableBExc.E6Three.zetaVec ζ hζ3 (Pi.single 6 2))
  let φ := langModelMulEquiv .E8 K L (e8LangG0 hω)
  have hφd : ((φ (tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep)) : ModGL .E8 L)) = a := by
    rw [coe_langModelMulEquiv_tE hK hω hω3, frameDiag_lineRep]
  intro c hc
  have hc'comm : Commute ((φ c : ModGL .E8 L)) a :=
    commute_langImage_lineRep hK hω hφd hc
  have hc'adj : (φ c : ModGL .E8 L) ∈ adjointGroup .E8 L :=
    langModel_le_adjointGroup (τ := .E8) (K := K) (L := L) (e8LangG0_mem hω) (φ c).2
  have hfam : (φ c : ModGL .E8 L) ∈ familyCentralizer .E8 L
      (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ3 (Pi.single 6 2)) := by
    refine mem_familyCentralizer.2 ⟨hc'adj, fun () => ?_⟩
    change a * (φ c : ModGL .E8 L) * a⁻¹ = (φ c : ModGL .E8 L)
    calc a * (φ c : ModGL .E8 L) * a⁻¹ = ((φ c : ModGL .E8 L) * a) * a⁻¹ := by
          rw [hc'comm.eq.symm]
      _ = (φ c : ModGL .E8 L) := by group
  have hNroot : (φ c : ModGL .E8 L) ∈ Subgroup.normalizer
      (rootSpan .E8 L (parabolicRoots .E8 (e6Nodes .E8)) : Set _) :=
    familyCentralizer_le_normalizer_rootSpan_of_subset _
      (e6Roots_subset_familyKernel_lineRep hζo hζ3)
      (familyStabilizer_mapsTo_e6Roots_lineRep hζo hζ3)
      (commute_familyKernel_diff_e6Roots_lineRep hζo hζ3) hfam
  have hle := langModel_le_twModel (τ := .E8) (K := K) (L := L)
    (Fr := iterateFrobenius L 2 1)
    (fun c => by rw [iterateFrobenius_def, hK, pow_one]) (e8LangG0_mem hω)
    (frob_e8LangG0 hK hω)
  have htw : (φ c : ModGL .E8 L) ∈ twistedFixedPoints (e8LangN K)
      (Units.map (entrywiseHom (iterateFrobenius L 2 1))) :=
    (mem_twModel.1 (hle (φ c).2)).2
  have hNP : (φ c : ModGL .E8 L) ∈ Subgroup.normalizer (e8LineP K : Set _) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNroot, Subgroup.le_normalizer htw⟩
  exact mem_normalizer_e8LineComp_of_lang hω hNP

section CertE6


theorem finite_isQuasisimple_e8LineP :
    Finite ↥(e8LineP K) ∧ CFSG.IsQuasisimple ↥(e8LineP K) := by
  haveI : IsAlgClosure K (e8LangField K) := isAlgClosure_e8LangField K
  haveI : IsAlgClosed (e8LangField K) := IsAlgClosure.isAlgClosed K
  obtain ⟨h, hw⟩ := exists_e8LangN_mem_monomial (K := K)
  exact e6Layer_finite_quasisimple .E8 (L := e8LangField K) (ℓ := 2) (f := 1) le_rfl
    h (fun α hα => by
      rw [hw]
      exact neg_mem_parabolicRoots hα)

theorem e8LineP_le_langModel (hK : Nat.card K = 2)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) :
    e8LineP K ≤ langModel .E8 K (e8LangField K) (e8LangG0 hω) := by
  haveI : IsAlgClosure K (e8LangField K) := isAlgClosure_e8LangField K
  haveI := (finite_isQuasisimple_e8LineP (K := K)).1
  refine le_langModel_E8_of_le_twModel K (e8LangField K)
    (Fr := iterateFrobenius (e8LangField K) 2 1)
    (fun c => by rw [iterateFrobenius_def, hK, pow_one]) (e8LangG0_mem hω)
    (frob_e8LangG0 hK hω) ?_
  exact fun x hx => ⟨rootSpan_le_adjointGroup' _ hx.1, hx.2⟩

theorem finite_isQuasisimple_e8LineComp (hK : Nat.card K = 2)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) :
    Finite ↥(e8LineComp hω) ∧ CFSG.Open.IsQuasisimple ↥(e8LineComp hω) := by
  let L := e8LangField K
  let φ := langModelMulEquiv .E8 K L (e8LangG0 hω)
  let Q := (e8LineP K).subgroupOf (langModel .E8 K L (e8LangG0 hω))
  have hle := e8LineP_le_langModel hK hω
  have e1 : Q ≃* e8LineP K := Subgroup.subgroupOfEquivOfLe hle
  have e2 : Q ≃* e8LineComp hω :=
    Subgroup.equivMapOfInjective Q φ.symm.toMonoidHom φ.symm.injective
  have hfin : Finite ↥(e8LineP K) := (finite_isQuasisimple_e8LineP (K := K)).1
  have hqs : CFSG.IsQuasisimple ↥(e8LineP K) :=
    (finite_isQuasisimple_e8LineP (K := K)).2
  refine ⟨Finite.of_equiv _ (e1.symm.trans e2).toEquiv, ?_⟩
  exact isQuasisimple_of_mulEquiv_open (e1.symm.trans e2)
    (isQuasisimple_open_of_foundations hqs)

theorem isComponentOf_e8LineComp (hK : Nat.card K = 2)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) :
    IsComponentOf (e8LineComp hω) (Subgroup.centralizer
      ({tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep)} :
        Set ↥(adjointGroup .E8 K))) := by
  have hle := e8LineComp_le_centralizer hK hω
  have hq := (finite_isQuasisimple_e8LineComp hK hω).2
  refine ⟨hle, IsSubnormal.step hle ?_ (IsSubnormal.refl _), hq⟩
  exact Subgroup.normal_subgroupOf_iff hle |>.2 fun x y hx hy =>
    (Subgroup.mem_normalizer_iff.1
      (centralizer_le_normalizer_e8LineComp hK hω hy) x).1 hx

theorem rho_three_mem_stdLayer_lineRep (hK : Nat.card K = 2) (A : SL2 K) :
    rho K frameE8 3 A ∈
      stdLayer (tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep)) := by
  have h3 : 3 ∣ Nat.card ((FiniteField.Extension K 2 2)ˣ) := by
    rw [Nat.card_units, natCard_ext hK]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card'
    (G := (FiniteField.Extension K 2 2)ˣ) 3 h3
  exact le_GLALayer (isComponentOf_e8LineComp hK hω) (rho_three_mem_e8LineComp hK hω A)

end CertE6

section CertF


private theorem e8FrameV_tC_mem_lineRep (hK : Nat.card K = 2) (c : ZMod 3) :
    tC K frameE8 3 (Multiplicative.ofAdd c) ∈
      (e8FrameV K ⊓ stdLayer (tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep))) := by
  refine ⟨?_, ?_⟩
  · change tC K frameE8 3 (Multiplicative.ofAdd c) ∈ e8FrameV K
    rw [mem_e8FrameV_iff]
    exact ⟨Pi.single (M := fun _ => ZMod 3) 3 c, by simp,
      (tE_single frameE8 3 c).symm⟩
  · rw [tC_apply, tGen]
    exact (stdLayer (tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep))).pow_mem
      (rho_three_mem_stdLayer_lineRep hK (uSL 1 * vSL 1)) c.val

private theorem e8FrameV_tE_mem_lineRep (hK : Nat.card K = 2) (w : Fin 8 → ZMod 3)
    (hw0 : w 0 = 0) (hw3 : w 3 = 0) :
    tE K frameE8 (Multiplicative.ofAdd w) ∈
      (e8FrameV K ⊓ Subgroup.normalizer
        (Subgroup.zpowers (rho K frameE8 3 (uSL 1)) : Set ↥(adjointGroup .E8 K))) := by
  refine ⟨?_, ?_⟩
  · change tE K frameE8 (Multiplicative.ofAdd w) ∈ e8FrameV K
    rw [mem_e8FrameV_iff]
    exact ⟨w, hw0, rfl⟩
  · have hbcomm : Commute (rho K frameE8 3 (uSL 1))
        (tE K frameE8 (Multiplicative.ofAdd w)) := by
      rw [tE_apply, tD, MonoidHom.noncommPiCoprod_apply]
      refine Finset.noncommProd_commute _ _ _ (rho K frameE8 3 (uSL 1)) ?_
      intro i _
      by_cases hi : i = 3
      · subst hi
        rw [hw3]
        simp
      · have htc : tC K frameE8 i (Multiplicative.ofAdd (w i)) =
            rho K frameE8 i ((uSL 1 * vSL 1) ^ (w i).val) :=
          tC_apply_rho (K := K) (F := frameE8) i _
        rw [htc]
        exact (commute_rho (K := K) frameE8 (i := i) (j := 3) hi
          ((uSL 1 * vSL 1) ^ (w i).val) (uSL 1)).symm
    refine Subgroup.centralizer_le_normalizer
      (Subgroup.zpowers (rho K frameE8 3 (uSL 1)) : Set ↥(adjointGroup .E8 K)) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (hbcomm.zpow_left n).eq

private theorem e8FrameV_le_sup_lineRep (hK : Nat.card K = 2) :
    e8FrameV K ≤
      (e8FrameV K ⊓ stdLayer (tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep))) ⊔
      (e8FrameV K ⊓ Subgroup.normalizer
        (Subgroup.zpowers (rho K frameE8 3 (uSL 1)) : Set ↥(adjointGroup .E8 K))) := by
  intro x hx
  rw [mem_e8FrameV_iff] at hx
  obtain ⟨v, hv0, rfl⟩ := hx
  set c := v 3 with hc
  let e : Fin 8 → ZMod 3 := Pi.single (M := fun _ => ZMod 3) 3 c
  set w : Fin 8 → ZMod 3 := v - e with hw
  have hw0 : w 0 = 0 := by simp [hw, e, hv0]
  have hw3 : w 3 = 0 := by simp [hw, e, hc]
  have hv : v = e + w := by
    funext i
    simp [hw]
  have hxeq : tE K frameE8 (Multiplicative.ofAdd v) =
      tC K frameE8 3 (Multiplicative.ofAdd c) *
        tE K frameE8 (Multiplicative.ofAdd w) := by
    conv_lhs => rw [hv]
    rw [ofAdd_add, map_mul, show e = Pi.single (M := fun _ => ZMod 3) 3 c from rfl,
      tE_single]
  rw [hxeq]
  exact Subgroup.mul_mem_sup (e8FrameV_tC_mem_lineRep hK c)
    (e8FrameV_tE_mem_lineRep hK w hw0 hw3)

theorem stdExtendsN_lineRep (hK : Nat.card K = 2)
    (hKD : stdLayer (tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep)) ≤ e7Levi K) :
    StdExtendsN 3 (e8FrameV K)
      (tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep)) := by
  let d := tE K frameE8 (Multiplicative.ofAdd e8FrameLineRep)
  let T : Subgroup ↥(adjointGroup .E8 K) := Subgroup.zpowers (rho K frameE8 3 (uSL 1))
  have hgen_ne : rho K frameE8 3 (uSL 1) ≠ 1 := fun h =>
    TableBF4Two.uSL_one_ne_one (rho_injective frameE8 3 (h.trans (map_one _).symm))
  have hsq : rho K frameE8 3 (uSL 1) ^ 2 = 1 := by
    rw [← map_pow, TableBF4Two.uSL_one_sq CharTwo.two_eq_zero, map_one]
  have hTne : T ≠ ⊥ := by
    change Subgroup.zpowers (rho K frameE8 3 (uSL 1)) ≠ ⊥
    intro h
    exact hgen_ne (Subgroup.zpowers_eq_bot.mp h)
  have hT2 : IsPGroup 2 T := by
    refine IsPGroup.of_card (n := 1) ?_
    change Nat.card (Subgroup.zpowers (rho K frameE8 3 (uSL 1))) = 2 ^ 1
    rw [Nat.card_zpowers, orderOf_eq_prime hsq hgen_ne]
    norm_num
  have hTK : T ≤ stdLayer d :=
    Subgroup.zpowers_le.2 (rho_three_mem_stdLayer_lineRep hK (uSL 1))
  have hdecomp : e8FrameV K = (e8FrameV K ⊓ stdLayer d) ⊔
      (e8FrameV K ⊓ Subgroup.normalizer (T : Set ↥(adjointGroup .E8 K))) :=
    le_antisymm (e8FrameV_le_sup_lineRep hK) (sup_le inf_le_left inf_le_left)
  refine ⟨⟨T, hTne, hT2, hTK, hdecomp⟩, tGen K frameE8 0, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := Subgroup.mem_centralizer_iff.mp
      (e7Levi_le_centralizer_tGen_zero (e8FrameV_le_e7Levi ha))
      (tGen K frameE8 0) rfl
    exact h.symm
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h := Subgroup.mem_centralizer_iff.mp
      (e7Levi_le_centralizer_tGen_zero (hKD hk)) (tGen K frameE8 0) rfl
    exact h.symm
  · exact tGen_pow_three frameE8 0
  · exact tGen_zero_notMem_e8FrameV

end CertF

end CertBase

end CFSG.LocalAnalysis.GLTheoremA.T173O

end

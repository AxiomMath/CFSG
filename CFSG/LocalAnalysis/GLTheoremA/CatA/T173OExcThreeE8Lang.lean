module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE8Data
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveOrbit
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyNormalizer
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Data
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE8
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Root
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LieType.Chevalley.D4TripleA2Lemmas
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.StandardType CFSG.StandardType.TableBExcTwo CFSG.StandardType.TableBExcTwoTB
open CFSG.StandardType.TableBExcTwoFusion CFSG.StandardType.ExcFrameIso CFSG.StandardType.ExcFrames
open CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.Torality CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.RankThree.CentralCover
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Matrix

section Lang

variable (K : Type) [Field K] [Finite K] [CharP K 2]

abbrev e8LangField : Type := AlgebraicClosure (FiniteField.Extension K 2 2)

theorem isAlgClosure_e8LangField : IsAlgClosure K (e8LangField K) := by
  haveI : Algebra.IsAlgebraic K (FiniteField.Extension K 2 2) := Algebra.IsAlgebraic.of_finite K _
  infer_instance

variable {K}

section Cert


@[expose] noncomputable def e8LangG0 {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) :
    ModGL .E8 (e8LangField K) :=
  baseChangeGL (algebraMap (FiniteField.Extension K 2 2) (e8LangField K))
    ((langElt (K := K) frameE8 hω : adjointGroup .E8 (FiniteField.Extension K 2 2)) :
      ModGL .E8 (FiniteField.Extension K 2 2))

variable (K) in
@[expose] noncomputable def e8LangN : ModGL .E8 (e8LangField K) :=
  (frameProd (e8LangField K) frameE8 (nSL 1) : adjointGroup .E8 (e8LangField K))

theorem e8LangG0_mem {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) :
    e8LangG0 hω ∈ adjointGroup .E8 (e8LangField K) := by
  unfold e8LangG0
  exact TableBExcTwo.baseChangeGL_mem_adjointGroup _ (langElt frameE8 hω).2

theorem e8LangN_mem_adjointGroup : e8LangN K ∈ adjointGroup .E8 (e8LangField K) :=
  (frameProd (e8LangField K) frameE8 (nSL 1)).2

theorem exists_e8LangN_mem_monomial :
    ∃ h : e8LangN K ∈ monomialSubgroup .E8 (e8LangField K),
      ∀ v : Fin Tag.E8.rank → ℤ, weylQuotientHom .E8 (e8LangField K) ⟨_, h⟩ • v = -v := by
  obtain ⟨h, hw⟩ := exists_frameProd_nSL_mem_monomial (L := e8LangField K) frameE8
  exact ⟨h, fun v => (congrArg (· • v) hw).trans (frameE8_reflections v)⟩

theorem frob_e8LangG0 (hK : Nat.card K = 2) {ω : (FiniteField.Extension K 2 2)ˣ}
    (hω : orderOf ω = 3) :
    Units.map (entrywiseHom (iterateFrobenius (e8LangField K) 2 1)) (e8LangG0 hω) =
      e8LangG0 hω * e8LangN K := by
  let K₂ := FiniteField.Extension K 2 2
  let L := e8LangField K
  let ι : K₂ →+* L := algebraMap K₂ L
  let F : L →+* L := iterateFrobenius L 2 1
  let T : K₂ →+* K₂ := frobHom K
  let g₂ : ModGL .E8 K₂ := (langElt (K := K) frameE8 hω : ModGL .E8 K₂)
  let n₂ : ModGL .E8 K₂ := (frameProd K₂ frameE8 (nSL 1) : ModGL .E8 K₂)
  have hσT : F.comp ι = ι.comp T := by
    ext a
    calc (F.comp ι) a = iterateFrobenius L 2 1 (ι a) := rfl
      _ = (ι a) ^ 2 := by
          rw [iterateFrobenius_def]
          norm_num
      _ = ι ((frobHom K) a) := by
          rw [frobHom_apply, frob_eq_sq hK, map_pow]
      _ = (ι.comp T) a := rfl
  have hx : Units.map (entrywiseHom T) g₂ = g₂ * n₂ := by
    rw [units_map_entrywiseHom_eq_baseChangeGL]
    have h := congrArg (fun x : adjointGroup .E8 K₂ => (x : ModGL .E8 K₂))
      (adjointMap_frob_langElt (K := K) hK frameE8 hω)
    rw [TableBExcTwo.coe_adjointMap] at h
    simpa [g₂, n₂] using h
  have hcomm := units_map_entrywiseHom_baseChangeGL_comm (τ := .E8) ι F T hσT g₂
  calc Units.map (entrywiseHom F) (e8LangG0 hω)
      = Units.map (entrywiseHom F) (baseChangeGL ι g₂) := rfl
    _ = baseChangeGL ι (Units.map (entrywiseHom T) g₂) := hcomm
    _ = baseChangeGL ι (g₂ * n₂) := by rw [hx]
    _ = baseChangeGL ι g₂ * baseChangeGL ι n₂ := map_mul _ _ _
    _ = e8LangG0 hω * e8LangN K := by
          have hmapnSL : Matrix.SpecialLinearGroup.map ι (nSL 1) = nSL 1 := by
            rw [nSL_one, CFSG.LieType.Chevalley.map_WSL, nSL_one]
          have hn : baseChangeGL ι n₂ = (frameProd L frameE8 (nSL 1) : ModGL .E8 L) := by
            rw [← TableBExcTwo.coe_adjointMap, adjointMap_frameProd, hmapnSL]
          rw [e8LangG0, e8LangN, hn]

private theorem baseChangeGL_frameDiag {R S : Type} [Field R] [Field S] (f : R →+* S)
    {ζ : Rˣ} (hζ : ζ ^ 3 = 1) (s : Fin Tag.E8.rank → ZMod 3) :
    baseChangeGL f (frameDiag ζ hζ s) =
      frameDiag (Units.map f.toMonoidHom ζ) (by rw [← map_pow, hζ, map_one]) s := by
  rw [frameDiag, frameDiag, CFSG.LieType.Chevalley.baseChangeGL_rootDiagUnit]
  congr 1
  funext i
  simp [TableBExc.E6Three.zetaVec, zmodPowHom, map_pow]

theorem coe_langModelMulEquiv_tE (hK : Nat.card K = 2)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) (hω3 : ω ^ 3 = 1)
    (v : Fin 8 → ZMod 3) :
    ((langModelMulEquiv .E8 K (e8LangField K) (e8LangG0 hω)
        (tE K frameE8 (Multiplicative.ofAdd v)) :
        langModel .E8 K (e8LangField K) (e8LangG0 hω)) : ModGL .E8 (e8LangField K)) =
      frameDiag
        (Units.map (algebraMap (FiniteField.Extension K 2 2) (e8LangField K)).toMonoidHom ω)
        (by rw [← map_pow, hω3, map_one]) (e8FrameLambda v) := by
  let K₂ := FiniteField.Extension K 2 2
  let L := e8LangField K
  let ι : K₂ →+* L := algebraMap K₂ L
  let g₂ : adjointGroup .E8 K₂ := langElt (K := K) frameE8 hω
  let g₀ : ModGL .E8 L := e8LangG0 (K := K) hω
  have hg₀ : g₀ = baseChangeGL ι (g₂ : ModGL .E8 K₂) := rfl
  have hfull : ∀ a : Fin Tag.E8.rank → K₂ˣ, rootDiagUnit .E8 a ∈ torusGroup .E8 K₂ :=
    fun a => rootDiagUnit_mem_torusGroup_E8 a
  have hsym : ∀ i, Tag.E8.symmetrizer i i = 1 := fun i => by simp [Tag.symmetrizer]
  have hbc : baseChangeGL (algebraMap K L) (tE K frameE8 (Multiplicative.ofAdd v) :
      ModGL .E8 K) =
      g₀ * baseChangeGL ι (frameDiag ω hω3 (e8FrameLambda v)) * g₀⁻¹ := by
    rw [IsScalarTower.algebraMap_eq K K₂ L, ← CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL,
      ← TableBExcTwo.coe_adjointMap, adjointMap_tE_eq hsym frameE8 hω hω3 hfull v,
      frameCoordHom_frameE8_eq]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rfl
  have hdiag : baseChangeGL ι (frameDiag ω hω3 (e8FrameLambda v)) =
      frameDiag (Units.map ι.toMonoidHom ω) (by rw [← map_pow, hω3, map_one])
        (e8FrameLambda v) := baseChangeGL_frameDiag ι hω3 _
  have hcoe : ((langModelMulEquiv .E8 K L (e8LangG0 hω)
        (tE K frameE8 (Multiplicative.ofAdd v)) :
        langModel .E8 K L (e8LangG0 hω)) : ModGL .E8 L) =
      g₀⁻¹ * baseChangeGL (algebraMap K L)
        (tE K frameE8 (Multiplicative.ofAdd v) : ModGL .E8 K) * g₀⁻¹⁻¹ :=
    coe_langModelMulEquiv .E8 K L (e8LangG0 hω) _
  calc ((langModelMulEquiv .E8 K L (e8LangG0 hω)
        (tE K frameE8 (Multiplicative.ofAdd v)) :
        langModel .E8 K L (e8LangG0 hω)) : ModGL .E8 L)
      = g₀⁻¹ * baseChangeGL (algebraMap K L)
          (tE K frameE8 (Multiplicative.ofAdd v) : ModGL .E8 K) * g₀⁻¹⁻¹ := hcoe
    _ = g₀⁻¹ * (g₀ * baseChangeGL ι (frameDiag ω hω3 (e8FrameLambda v)) * g₀⁻¹) *
          g₀⁻¹⁻¹ := by rw [hbc]
    _ = frameDiag (Units.map ι.toMonoidHom ω) (by rw [← map_pow, hω3, map_one])
          (e8FrameLambda v) := by
          rw [hdiag]
          group

end Cert

end Lang

section Kernel

variable {L : Type} [Field L]

private theorem mem_parabolicRoots_e6Nodes_E8_iff {α : Fin Tag.E8.rank → ℤ}
    (hα : IsRoot .E8 α) :
    α ∈ parabolicRoots .E8 (e6Nodes .E8) ↔ α 6 = 0 ∧ α 7 = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hm : (6 : Fin Tag.E8.rank) ∉ e6Nodes .E8 := by
        simp only [e6Nodes, Set.mem_setOf_eq, not_le]
        decide
      simpa using h.2 6 hm
    · have hm : (7 : Fin Tag.E8.rank) ∉ e6Nodes .E8 := by
        simp only [e6Nodes, Set.mem_setOf_eq, not_le]
        decide
      simpa using h.2 7 hm
  · rintro ⟨h6, h7⟩
    refine ⟨hα, fun i hi => ?_⟩
    have hrank : Tag.E8.rank = 8 := rfl
    have hge : 6 ≤ i.val := by
      by_contra h
      apply hi
      simp [e6Nodes]
      omega
    have hival : i.val = 6 ∨ i.val = 7 := by
      have hlt : i.val < 8 := by omega
      omega
    rcases hival with h | h
    · have hi' : i = (6 : Fin Tag.E8.rank) := Fin.ext h
      rw [hi']; exact h6
    · have hi' : i = (7 : Fin Tag.E8.rank) := Fin.ext h
      rw [hi']; exact h7

theorem rootChar_zetaVec_lineRep_eq_one_iff {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (α : Fin Tag.E8.rank → ℤ) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ (Pi.single (6 : Fin Tag.E8.rank) 2)) α = 1 ↔
      α 6 % 3 = 0 := by
  rw [NoOffE8Five.rootChar_zetaVec]
  have hsum : (∑ j, ((α j : ℤ) : ZMod 3) *
      (Pi.single (6 : Fin Tag.E8.rank) 2 : Fin Tag.E8.rank → ZMod 3) j) =
      ((α 6 : ℤ) : ZMod 3) * 2 := by
    rw [Finset.sum_eq_single 6]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum]
  constructor
  · intro h
    have h1 : (Multiplicative.ofAdd (((α 6 : ℤ) : ZMod 3) * 2) :
        Multiplicative (ZMod 3)) = 1 := by
      apply zmodPowHom_injective hζo hζ
      rw [h, map_one]
    have h2 : ((α 6 : ℤ) : ZMod 3) * 2 = 0 := by
      simpa using congrArg Multiplicative.toAdd h1
    have h3 : ((α 6 : ℤ) : ZMod 3) = 0 := by
      have h2' : 2 * ((α 6 : ℤ) : ZMod 3) = 0 := by rw [mul_comm]; exact h2
      exact (mul_eq_zero.mp h2').resolve_left (by decide)
    have hdvd : (3 : ℤ) ∣ α 6 := (ZMod.intCast_zmod_eq_zero_iff_dvd (α 6) 3).1 h3
    rwa [Int.dvd_iff_emod_eq_zero] at hdvd
  · intro h6
    have h3 : ((α 6 : ℤ) : ZMod 3) = 0 := by
      rw [← Int.dvd_iff_emod_eq_zero] at h6
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast h6)
    rw [h3, zero_mul]
    simp

private theorem familyKernel_lineRep_iff {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (γ : Fin Tag.E8.rank → ℤ) (hγ : IsRoot .E8 γ) :
    γ ∈ familyKernel (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ
        (Pi.single (6 : Fin Tag.E8.rank) 2)) ↔ γ 6 % 3 = 0 := by
  rw [familyKernel]
  constructor
  · rintro ⟨-, h1⟩
    exact (rootChar_zetaVec_lineRep_eq_one_iff hζo hζ γ).1 (h1 ())
  · intro h6
    exact ⟨hγ, fun _ => (rootChar_zetaVec_lineRep_eq_one_iff hζo hζ γ).2 h6⟩

theorem e6Roots_subset_familyKernel_lineRep {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    parabolicRoots .E8 (e6Nodes .E8) ⊆ familyKernel
      (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ (Pi.single (6 : Fin Tag.E8.rank) 2)) := by
  intro α hα
  refine ⟨hα.1, fun _ => (rootChar_zetaVec_lineRep_eq_one_iff hζo hζ α).2 ?_⟩
  have h6 : α 6 = 0 := (mem_parabolicRoots_e6Nodes_E8_iff hα.1).1 hα |>.1
  rw [h6]
  norm_num

private theorem familyStabilizer_smul_mem_familyKernel_iff {ζ : Lˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {w : WeylGroup .E8}
    (hw : w ∈ familyStabilizer (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ
      (Pi.single (6 : Fin Tag.E8.rank) 2))) (γ : Fin Tag.E8.rank → ℤ) :
    w • γ ∈ familyKernel (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ
        (Pi.single (6 : Fin Tag.E8.rank) 2)) ↔
      γ ∈ familyKernel (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ
        (Pi.single (6 : Fin Tag.E8.rank) 2)) := by
  have h := image_familyKernel hw
  constructor
  · intro hmem
    rw [← h] at hmem
    obtain ⟨δ, hδ, hδγ⟩ := hmem
    have heq : δ = γ := by
      have := congrArg (fun x => w⁻¹ • x) hδγ
      simpa [smul_inv_smul] using this
    simpa [heq] using hδ
  · intro hγ
    rw [← h]
    exact ⟨γ, hγ, rfl⟩

section CardFilter


private theorem card_filter_orth_smul {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {w : WeylGroup .E8} (hw : w ∈ familyStabilizer (fun _ : Unit =>
      TableBExc.E6Three.zetaVec ζ hζ (Pi.single (6 : Fin Tag.E8.rank) 2)))
    (α : Fin Tag.E8.rank → ℤ) :
    ((rootFinset .E8).filter fun β => β 6 % 3 = 0 ∧ iform α β = 0).card =
      ((rootFinset .E8).filter fun β => β 6 % 3 = 0 ∧ iform (w • α) β = 0).card := by
  have hS : ∀ β ∈ rootFinset .E8, IsRoot .E8 β := fun β hβ => mem_rootFinset.1 hβ
  have hmemS : ∀ β, β ∈ rootFinset .E8 → w • β ∈ rootFinset .E8 := fun β hβ =>
    mem_rootFinset.2 (IsRoot.smul (hS β hβ) w)
  have hmemS' : ∀ β, β ∈ rootFinset .E8 → w⁻¹ • β ∈ rootFinset .E8 := fun β hβ =>
    mem_rootFinset.2 (IsRoot.smul (hS β hβ) w⁻¹)
  have hcoords : ∀ β, β ∈ rootFinset .E8 → ((w • β) 6 % 3 = 0 ↔ β 6 % 3 = 0) := by
    intro β hβ
    have h1 := familyStabilizer_smul_mem_familyKernel_iff hζo hζ hw β
    rw [← familyKernel_lineRep_iff hζo hζ (w • β) (IsRoot.smul (hS β hβ) w),
      ← familyKernel_lineRep_iff hζo hζ β (hS β hβ), h1]
  have hcoords' : ∀ β, β ∈ rootFinset .E8 → ((w⁻¹ • β) 6 % 3 = 0 ↔ β 6 % 3 = 0) := by
    intro β hβ
    have hw' : w⁻¹ ∈ familyStabilizer (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ
        (Pi.single (6 : Fin Tag.E8.rank) 2)) := familyStabilizer_inv hw
    have h1 := familyStabilizer_smul_mem_familyKernel_iff hζo hζ hw' β
    rw [← familyKernel_lineRep_iff hζo hζ (w⁻¹ • β) (IsRoot.smul (hS β hβ) w⁻¹),
      ← familyKernel_lineRep_iff hζo hζ β (hS β hβ), h1]
  refine Finset.card_nbij' (fun β => w • β) (fun γ => w⁻¹ • γ) ?_ ?_ ?_ ?_
  · intro β hβ
    obtain ⟨hβ1, hβ2, hβ3⟩ := Finset.mem_filter.1 hβ
    exact Finset.mem_filter.2 ⟨hmemS β hβ1, (hcoords β hβ1).2 hβ2, by
      rw [iform_smul_smul w α β]
      exact hβ3⟩
  · intro γ hγ
    obtain ⟨hγ1, hγ2, hγ3⟩ := Finset.mem_filter.1 hγ
    exact Finset.mem_filter.2 ⟨hmemS' γ hγ1, (hcoords' γ hγ1).2 hγ2, by
      rw [← iform_smul_smul w α (w⁻¹ • γ), smul_inv_smul]
      exact hγ3⟩
  · intro β _; simp [smul_inv_smul]
  · intro γ _; simp [inv_smul_smul]

theorem familyStabilizer_mapsTo_e6Roots_lineRep {ζ : Lˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) :
    ∀ w ∈ familyStabilizer
        (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ (Pi.single (6 : Fin Tag.E8.rank) 2)),
      ∀ α ∈ parabolicRoots .E8 (e6Nodes .E8), w • α ∈ parabolicRoots .E8 (e6Nodes .E8) := by
  intro w hw α hα
  have hαroot : IsRoot .E8 α := hα.1
  have hαfam : α ∈ familyKernel (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ
      (Pi.single (6 : Fin Tag.E8.rank) 2)) :=
    e6Roots_subset_familyKernel_lineRep hζo hζ hα
  have hα6 : α 6 % 3 = 0 := (familyKernel_lineRep_iff hζo hζ α hαroot).1 hαfam
  have hαE6 : α 6 = 0 ∧ α 7 = 0 := (mem_parabolicRoots_e6Nodes_E8_iff hαroot).1 hα
  have hmemα : α ∈ e8Finset := by
    rw [← rootFinset_E8_eq]
    exact mem_rootFinset.2 hαroot
  have hcount : ((rootFinset .E8).filter fun β => β 6 % 3 = 0 ∧ iform α β = 0).card = 36 := by
    have h := (e8LineKernel_count α hmemα hα6).mp hαE6
    simpa [rootFinset_E8_eq] using h
  have hcountw : ((rootFinset .E8).filter fun β => β 6 % 3 = 0 ∧
      iform (w • α) β = 0).card = 36 := by
    rw [← card_filter_orth_smul hζo hζ hw α]
    exact hcount
  have hwroot : IsRoot .E8 (w • α) := IsRoot.smul hαroot w
  have hwfam : w • α ∈ familyKernel (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ
      (Pi.single (6 : Fin Tag.E8.rank) 2)) :=
    (familyStabilizer_smul_mem_familyKernel_iff hζo hζ hw α).2 hαfam
  have hw6 : (w • α) 6 % 3 = 0 := (familyKernel_lineRep_iff hζo hζ (w • α) hwroot).1 hwfam
  have hmemw : w • α ∈ e8Finset := by
    rw [← rootFinset_E8_eq]
    exact mem_rootFinset.2 hwroot
  have hwcount : ((e8Finset).filter fun β => β 6 % 3 = 0 ∧
      iform (w • α) β = 0).card = 36 := by
    simpa [rootFinset_E8_eq] using hcountw
  exact (mem_parabolicRoots_e6Nodes_E8_iff hwroot).2
    ((e8LineKernel_count (w • α) hmemw hw6).mpr hwcount)

end CardFilter

section Commute


theorem commute_familyKernel_diff_e6Roots_lineRep {ζ : Lˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) :
    ∀ α ∈ familyKernel
        (fun _ : Unit => TableBExc.E6Three.zetaVec ζ hζ (Pi.single (6 : Fin Tag.E8.rank) 2)) \
          parabolicRoots .E8 (e6Nodes .E8),
      ∀ β ∈ parabolicRoots .E8 (e6Nodes .E8), ∀ x ∈ rootSubgroup .E8 L α,
        ∀ y ∈ rootSubgroup .E8 L β, Commute x y := by
  rintro α hα β hβ x hx y hy
  have hαroot : IsRoot .E8 α := hα.1.1
  have hα6 : α 6 % 3 = 0 := (familyKernel_lineRep_iff hζo hζ α hαroot).1 hα.1
  have hβroot : IsRoot .E8 β := hβ.1
  have hβE6 : β 6 = 0 ∧ β 7 = 0 := (mem_parabolicRoots_e6Nodes_E8_iff hβroot).1 hβ
  have hαnotE6 : ¬(α 6 = 0 ∧ α 7 = 0) := fun h => hα.2
    ((mem_parabolicRoots_e6Nodes_E8_iff hαroot).2 h)
  have hne : α ≠ β := fun h => hαnotE6 (h ▸ hβE6)
  have hmemα : α ∈ e8Finset := by
    rw [← rootFinset_E8_eq]
    exact mem_rootFinset.2 hαroot
  have hmemβ : β ∈ e8Finset := by
    rw [← rootFinset_E8_eq]
    exact mem_rootFinset.2 hβroot
  have horth : α ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ β) = 0 :=
    e8LineKernel_orth α hmemα hα6 hαnotE6 β hmemβ hβE6.1 hβE6.2
  exact rootSubgroup_commute_of_rootForm_nonneg (Or.inr (Or.inr (Or.inr rfl)))
    hαroot hβroot hne horth.ge hx hy

end Commute

end Kernel

end CFSG.LocalAnalysis.GLTheoremA.T173O

end

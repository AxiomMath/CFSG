module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.LocalAnalysis.GLTheoremA.CatB.L2CentField
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterUnitary
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.KD.CharPAux.Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix
public import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2UniFix
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2UniSolv
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.Adapters.CatalogueFieldBridges.Unitary
public import CFSG.Adapters.Certificate43Check
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911ATL
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.Adapters.CatalogueFieldBridges.UnitarySU
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitaryPSUEquiv)
open CFSG.RankThree.PartTwo.KFacts (psuConj psuField psuPrimeFormEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr)
open CFSG.StandardType (ggAutFixedSubgroup)
open CFSG.Assembly (LargeEvenProj LargeEvenSUGroup)

local notation "fixS" => CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub

theorem fixU3_catalog_of_iso {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n) {K₀ : Type} [Field K₀]
    (hK₀ : Nat.card K₀ = (2 ^ n) ^ 2)
    (e : S ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) K₀ (2 ^ n))) :
    catalogIs S (S10.isU3n n) := by
  have h₀ : UnitaryFieldData 2 n K₀ := CFSG.StandardType.unitaryFieldData_of_card (by omega) hK₀
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have hv : (TauCeti.LieTypeIndex.twistedA (3 - 1) q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    refine ⟨by norm_num, fun _ => ?_⟩
    rw [TauCeti.PrimePower.card_def]
    show 3 ≤ 2 ^ n
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨g⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.primeFormP_one_mulEquiv_twistedA (q := q) h₀ le_rfl hv
  refine ⟨TauCeti.CFSGIndex.lie ⟨.twistedA (3 - 1) q, hv⟩, ⟨rfl, rfl⟩, ⟨?_⟩⟩
  exact e.trans ((unitaryPSUEquiv h₀ (by norm_num)).symm.trans ((psuPrimeFormEquiv h₀).trans g))

theorem fixU3_lieModel {R : Type} [Group R] {k : ℕ} (hcat : catalogIs R (S10.isU3n k)) :
    CFSG.Blueprint.LieModel R .PSU 3 2 k := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex hcat
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | r
    all_goals first | exact hP.elim | skip
    have hm := lieModel_twistedA' 2 q hv e
    have hm' := CFSG.Models.LieModel.toBlueprint (by decide) hm
    rw [hP.1, hP.2] at hm'
    exact hm'
  | _ => exact hP.elim

theorem fixU3_comp_iso {R : Type} [Group R] [Finite R] {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) (θ : R ≃* unitaryPSU h 3) {a : MulAut R} (ha3 : a ^ 3 = 1)
    (hD : MulAut.congr θ a ∉ (psuConj h).range) {n : ℕ} (hmn : m = 3 * n)
    {S : Subgroup R} (hS : GLAPComponent 3 (fixS a) S) :
    2 ≤ n ∧ ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀), Nat.card K₀ = (2 ^ n) ^ 2 ∧
      Nonempty (PSimple 3 S ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) K₀ (2 ^ n))) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hβ3 : MulAut.congr θ a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hfix : fixS (MulAut.congr θ a) = (fixS a).map θ.toMonoidHom :=
    CFSG.HardMathSupport.Solomon.Coordinator.fixSub_congr θ a
  let ψ₀ : fixS a ≃* fixS (MulAut.congr θ a) :=
    (θ.subgroupMap (fixS a)).trans (MulEquiv.subgroupCongr hfix.symm)
  have hcontra : Group.IsSolvable (fixS a) → False := fun hs => by
    haveI := hs
    exact CFSG.HardMathSupport.Dickson.KD.false_of_glaPComponent_of_solvable hS inferInstance
  have hn1 : 1 ≤ n := by have := h.one_le; omega
  have hq : 2 < 2 ^ m := by
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨σ, hσ, H, hβH⟩ :=
    CFSG.RankThree.PartTwo.KFacts.unitary_order_three_field_descent hq _ hβ3 hD
  have hgg : fixS (MulAut.congr θ a) = ggAutFixedSubgroup (MulAut.congr θ a) :=
    Subgroup.ext fun _ => Iff.rfl
  obtain ⟨E⟩ : Nonempty (↥(ggAutFixedSubgroup (MulAut.congr θ a)) ≃*
      ↥(ggAutFixedSubgroup (psuField h σ))) :=
    CFSG.StandardType.gffa2_fixedEquiv_of_congr (psuConj h H) (psuField h σ) _ (fun x => by
      rw [hβH]
      simp [MulAut.mul_apply])
  let E₁ : fixS a ≃* ggAutFixedSubgroup (psuField h σ) :=
    ψ₀.trans ((MulEquiv.subgroupCongr hgg).trans E)
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · exfalso
    obtain rfl : n = 1 := by omega
    obtain rfl : m = 3 := by omega
    have hsolv := CFSG.StandardType.gffa2_unitary_solvable h hσ
    haveI := hsolv
    exact hcontra (Group.isSolvable_of_surjective (f := E₁.symm.toMonoidHom) E₁.symm.surjective)
  obtain ⟨K₀, hK₀f, hK₀fin, hK₀, ⟨T₀⟩⟩ :=
    CFSG.StandardType.gffa2_unitary_derived_equiv h hσ hmn hn2
  obtain ⟨E'⟩ := CFSG.StandardType.gffa2_commutator_equiv E₁
  let T := E'.trans T₀
  obtain ⟨hs, -⟩ := CFSG.StandardType.gffa2_unitary_simple_nonab hn2 hK₀
  have hSimpD : IsSimpleGroup ↥⁅fixS a, fixS a⁆ := (MulEquiv.isSimpleGroup_congr T).2 hs
  have hperf : ⁅S, S⁆ = S := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hS
  have hSC : S ≤ fixS a := hS.1
  have hSD : S ≤ ⁅fixS a, fixS a⁆ := by
    rw [← hperf]
    exact Subgroup.commutator_mono hSC hSC
  have hDC : ⁅fixS a, fixS a⁆ ≤ fixS a := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact (fixS a).mul_mem ((fixS a).mul_mem ((fixS a).mul_mem hx hy) ((fixS a).inv_mem hx))
      ((fixS a).inv_mem hy)
  have hsnD : IsSubnormal S ⁅fixS a, fixS a⁆ := by
    have := hS.2.1.inf ⁅fixS a, fixS a⁆
    rwa [inf_eq_left.2 hSD, inf_eq_right.2 hDC] at this
  rcases CFSG.LocalAnalysis.GLTheoremB.eq_bot_or_eq_of_isSubnormal_of_simple hSimpD hsnD with
    hb | hSeq
  · exact (l2c_ne_bot_of_comp hS hb).elim
  have hq3 := isQuasisimple_pQuot_of_glaPComponent hp hS
  let τS : ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) K₀ (2 ^ n)) :=
    (MulEquiv.subgroupCongr hSeq).trans T
  haveI hSimpS : IsSimpleGroup ↥S := (MulEquiv.isSimpleGroup_congr τS).2 hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥S) with hO' | hO'
  · let eQ : PQuot 3 S ≃* ↥S :=
      (QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot
    have hsPQ : IsSimpleGroup (PQuot 3 S) := (MulEquiv.isSimpleGroup_congr eQ).2 hSimpS
    obtain ⟨φ⟩ := l2c_pSimple_iso hq3 hsPQ
    exact ⟨hn2, K₀, hK₀f, hK₀fin, hK₀, ⟨φ.trans (eQ.trans τS)⟩⟩
  · exact (l2c_core_ne_top hq3 hO').elim

section Certified


theorem fixU3_not_mem_psuConj_range {X : Type} [Group X] [Finite X] {Y J : Subgroup X} {x : X}
    {m : ℕ} (hL : GLAPComponent 3 Y J) (hND : NonInnDiag 3 x J)
    (hLM : CFSG.Blueprint.LieModel (PSimple 3 J) .PSU 3 2 m) {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) (θ : PSimple 3 J ≃* unitaryPSU h 3) (hx3 : x ^ 3 = 1) :
    MulAut.congr θ (chevAut 3 J ⟨x, hND.1⟩) ∉ (psuConj h).range := by
  rintro ⟨A, hA⟩
  apply hND.2
  have hq := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr
    (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL)
  have hβ3 : MulAut.congr θ (chevAut 3 J ⟨x, hND.1⟩) ^ 3 = 1 := by
    rw [← map_pow, chevAut_pow_eq_one 3 J hND.1 hx3, map_one]
  have hA3 : psuConj h A ^ 3 = 1 := by rw [hA]; exact hβ3
  refine T171Sh.innDiagOn_of_lieModel hND.1 hq hLM
    (by rintro ⟨h, -⟩; exact StatedLieTag.noConfusion h) (by decide) ?_
  rw [OutCyc.indAut_eq_inv_chevAut]
  refine Subgroup.inv_mem _ ?_
  rw [← mem_innAutDerived_congr θ, ← hA, ← mem_innAutDerived_congr (psuPrimeFormEquiv h),
    CFSG.RankThree.PartTwo.KFacts.congr_psuConj]
  refine KD264Lie.mem_innAutDerived_of_mem_primeFormD h Nat.prime_three (by norm_num)
    ⟨_, rfl⟩ ?_
  rw [← CFSG.RankThree.PartTwo.KFacts.congr_psuConj, ← map_pow, hA3, map_one]


theorem t158FixU3_holds : T158FixU3 := by
  intro X _ _ Y J x n hL hx3 hFG hcat M hM
  have hp : Nat.Prime 3 := Nat.prime_three
  have hND : NonInnDiag 3 x J :=
    hFG.elim (fun hF => MI.field_nonInnDiag_any hL hF) (fun hG => hG.1)
  have hxN : x ∈ Subgroup.normalizer (J : Set X) := hND.1
  have hap : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx3
  have hLM := fixU3_lieModel hcat
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (2 ^ (3 * n)) ^ 2 ∧
        Nonempty (PSimple 3 J ≃* StatedProj (StatedSU 3 (2 ^ (3 * n)) K)) := by
    rcases hLM with ⟨-, -, hmod⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hmod
    all_goals exact absurd h0 (by norm_num)
  letI := hKf
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have h1 := Finite.one_lt_card (α := K)
      simp at hK
      omega
    · exact hpos
  have h : UnitaryFieldData 2 (3 * n) K :=
    CFSG.StandardType.unitaryFieldData_of_card (by omega) hK
  let θ : PSimple 3 J ≃* unitaryPSU h 3 := e.trans (unitaryPSUEquiv h (by norm_num)).symm
  have hD := fixU3_not_mem_psuConj_range hL hND hLM h θ hx3
  have ha3 : chevAut 3 J ⟨x, hxN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 J hxN hx3
  have hS : GLAPComponent 3 (fixS (chevAut 3 J ⟨x, hxN⟩)) (chevTransfer 3 J M) := by
    rw [CFSG.HardMathSupport.Dickson.Sec6.fixSub_eq_fixSubgroup_up34]
    exact glaPComponent_chevTransfer hp hxN hap hM
  obtain ⟨hn2, K₀, hK₀f, hK₀fin, hK₀, ⟨ψ⟩⟩ := fixU3_comp_iso h θ ha3 hD rfl hS
  obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp hxN hap hM
  exact fixU3_catalog_of_iso hn2 hK₀ (g.trans ψ)

end Certified

end CFSG.LocalAnalysis.GLTheoremA.T158

end

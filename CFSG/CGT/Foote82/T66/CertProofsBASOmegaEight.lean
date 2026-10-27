module

public import CFSG.CGT.Foote82.T66.CitedBAS
public import Certificates.Certificate3002
public import Certificates.Certificate919009
public import CFSG.CGT.Harada80.OmegaReflect
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeMain
import CFSG.CGT.Foote82.T66.OmegaMinusMatrix
import CFSG.ClassicalGroups.Orthogonal.NormalizerOmega
import CFSG.RankThree.Literature.FSmithOrthogonal
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
public import CFSG.CGT.Foote82.T66.MC1Steps
public import CFSG.CGT.Foote82.T66.Steps
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUpLit.BHS7.BlockComm
public import CFSG.CGT.PushingUpLit.BHS7.SevenThree
public import CFSG.CGT.PushingUpLit.BHS7.VFacts
public import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Fischer.Classification.Defs
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNatural
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSplit
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.TwoGroupExtension
public import CFSG.Holt.Centralizer
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SLModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SpModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCFoote
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.Walter.JRFacts
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank
import CFSG.Fischer.Uniq.CompTau
import CFSG.LargeExtraspecial.OrthoF2
import CFSG.LargeExtraspecial.S2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82.OmegaEight

open CFSG.EvenSmallLie.OmegaEightMinus CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.ComponentClassification.J2Cover
open CFSG.CGT.Harada80 CFSG.ClassicalGroups.Orthogonal
open scoped Matrix

local notation "V8" => (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2)
local notation "O8" => TauCeti.QuadraticMap.orthogonalGroup (quadQ 3)

section Checks

theorem qLinkCheck_holds : qLinkCheck () = true := Certificates.certificate919009.1

theorem reflLinkCheck_holds : reflLinkCheck () = true := Certificates.certificate919009.2.1

theorem transMemCheck_holds : transMemCheck () = true :=
  Certificates.certificate919009.2.2.1

theorem eichCheck_holds : eichCheck () = true := Certificates.certificate919009.2.2.2.1

theorem typeCheck_holds : typeCheck () = true := Certificates.certificate919009.2.2.2.2.1

theorem reflRepCheck_holds : reflRepCheck () = true :=
  Certificates.certificate919009.2.2.2.2.2

theorem qLink_spec {c : ℕ} (hc : c < 256) :
    (CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0 ↔ qNat c = true) ∧
      ∃ j < 136, qNat (nsArr[j]! ^^^ c) = true := by
  have h := qLinkCheck_holds
  rw [qLinkCheck, List.all_eq_true] at h
  have h' := h c (List.mem_range.2 hc)
  rw [Bool.and_eq_true, List.any_eq_true] at h'
  obtain ⟨h1, j, hj, h2⟩ := h'
  have h1' := beq_iff_eq.mp h1
  refine ⟨?_, j, List.mem_range.1 hj, h2⟩
  rw [← h1']
  exact decide_eq_true_iff.symm

theorem reflLink_spec {j : ℕ} (hj : j < 136) {x : ℕ} (hx : x < 256) :
    reflCode 3 nsArr[j]! x = transNat nsArr[j]! x := by
  have h := reflLinkCheck_holds
  rw [reflLinkCheck, List.all_eq_true] at h
  have h' := h j (List.mem_range.2 hj)
  rw [List.all_eq_true] at h'
  exact beq_iff_eq.mp (h' x (List.mem_range.2 hx))

theorem transMem_spec {j : ℕ} (hj : j < 136) :
    siftA 136 (rawLevels 136 autS (autBase.map Fin.val).toArray) (autBase.map Fin.val).toArray 0
      (transArr nsArr[j]!) = true := by
  have h := transMemCheck_holds
  rw [transMemCheck, autLevels, List.all_eq_true] at h
  exact h j (List.mem_range.2 hj)

theorem eich_spec {i : ℕ} (hi : i < 10) :
    (eichRefl.getD i []).length % 2 = 0 ∧ (∀ c ∈ eichRefl.getD i [], c < 256 ∧ qNat c = true) ∧
      eqA 136 genArrs[i]! (prodArr (eichRefl.getD i [])) = true := by
  have h := eichCheck_holds
  rw [eichCheck, Bool.and_eq_true, List.all_eq_true] at h
  have h' := h.1 i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩

theorem gen10_spec : eqA 136 genArrs[10]! (transArr 64) = true := by
  have h := eichCheck_holds
  rw [eichCheck, Bool.and_eq_true] at h
  exact h.2

private def yA (k : ℕ) : Array ℕ := mainArrs.getD (witTypes.getD k 0) #[]

private def gA (k : ℕ) : Array ℕ := omegaW (witWords.getD k [])

private def zA (k : ℕ) : Array ℕ := compA 136 (yA k) (conjArr (gA k) (yA k))

private theorem type_spec {k : ℕ} (hk : k < 4) :
    isInvA 136 (gA k) (invCand 136 (gA k)) = true ∧
      eqA 136 (CFSG.EvenSmallLie.OmegaEightMinus.powArr (zA k) 12) (idA 136) = true ∧
      eqA 136 (CFSG.EvenSmallLie.OmegaEightMinus.powArr (zA k) 2) (idA 136) = false ∧
      eqA 136 (CFSG.EvenSmallLie.OmegaEightMinus.powArr (zA k) 3) (idA 136) = false := by
  have h := typeCheck_holds
  rw [typeCheck, List.all_eq_true] at h
  have h' := h k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h'
  exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

theorem reflRep_spec : eqA 136 (mainArrs.getD 3 #[]) (transArr 64) = true := by
  have h := reflRepCheck_holds
  rwa [reflRepCheck] at h

end Checks

theorem two_pow_eight : (2 : ℕ) ^ (3 + (3 + 2)) = 256 := by norm_num

theorem code_lt256 (v : V8) : code v < 256 := two_pow_eight ▸ code_lt v

theorem code_vec {c : ℕ} (hc : c < 256) : code (vec 3 c) = c :=
  vec_inj (code_lt _) (two_pow_eight ▸ hc) (vec_code _)

theorem xor_lt256 {a b : ℕ} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 :=
  Nat.xor_lt_two_pow (n := 8) ha hb

theorem transNat_lt256 {c x : ℕ} (hc : c < 256) (hx : x < 256) : transNat c x < 256 := by
  unfold transNat
  split
  · exact xor_lt256 hx hc
  · exact hx

theorem finrank_V8 : Module.finrank (ZMod 2) V8 = 8 :=
  CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus 3

section Model

theorem quadQ_vec_eq_one_iff {c : ℕ} (hc : c < 256) :
    quadQ 3 (vec 3 c) = 1 ↔ qNat c = true := by
  rw [← (qLink_spec hc).1, coe_quadQ]
  constructor
  · intro h
    rw [h]
    exact one_ne_zero
  · exact zmod_two_eq_one_of_ne_zero

theorem nsArr_spec (j : Fin 136) : nsArr[(j : ℕ)]! < 256 ∧ qNat nsArr[(j : ℕ)]! = true ∧
    nsIdx[nsArr[(j : ℕ)]!]! = j :=
  ns_ok.2.2.1 j j.2

theorem quadQ_ptVec (j : Fin 136) : quadQ 3 (vec 3 nsArr[(j : ℕ)]!) = 1 :=
  (quadQ_vec_eq_one_iff (nsArr_spec j).1).2 (nsArr_spec j).2.1

theorem qNat_code {v : V8} (hv : quadQ 3 v = 1) : qNat (code v) = true :=
  (quadQ_vec_eq_one_iff (code_lt256 v)).1 (by rw [vec_code]; exact hv)

noncomputable def ptEquiv : Fin 136 ≃ {v : V8 // quadQ 3 v = 1} where
  toFun j := ⟨vec 3 nsArr[(j : ℕ)]!, quadQ_ptVec j⟩
  invFun v := ⟨nsIdx[code v.1]!, (ns_ok.2.2.2 _ (code_lt256 _) (qNat_code v.2)).1⟩
  left_inv j := Fin.ext (by
    show nsIdx[code (vec 3 nsArr[(j : ℕ)]!)]! = j
    rw [code_vec (nsArr_spec j).1]
    exact (nsArr_spec j).2.2)
  right_inv v := Subtype.ext (by
    show vec 3 nsArr[nsIdx[code v.1]!]! = v.1
    rw [(ns_ok.2.2.2 _ (code_lt256 _) (qNat_code v.2)).2]
    exact vec_code v.1)

theorem ptEquiv_val (j : Fin 136) :
    ((ptEquiv j : {v : V8 // quadQ 3 v = 1}) : V8) = vec 3 nsArr[(j : ℕ)]! := by
  unfold ptEquiv
  rfl

noncomputable def nsPerm (g : ↥O8) : Equiv.Perm {v : V8 // quadQ 3 v = 1} where
  toFun v := ⟨(g : V8 ≃ₗ[ZMod 2] V8) v.1, by rw [map_of_mem g.2, v.2]⟩
  invFun v := ⟨(g : V8 ≃ₗ[ZMod 2] V8).symm v.1, by
    rw [← map_of_mem g.2, LinearEquiv.apply_symm_apply, v.2]⟩
  left_inv v := Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  right_inv v := Subtype.ext (LinearEquiv.apply_symm_apply _ _)

noncomputable def piO : ↥O8 →* Equiv.Perm (Fin 136) where
  toFun g := ptEquiv.trans ((nsPerm g).trans ptEquiv.symm)
  map_one' := Equiv.ext fun j => by
    show ptEquiv.symm (nsPerm 1 (ptEquiv j)) = j
    have : nsPerm 1 (ptEquiv j) = ptEquiv j := Subtype.ext rfl
    rw [this, Equiv.symm_apply_apply]
  map_mul' g h := Equiv.ext fun j => by
    show ptEquiv.symm (nsPerm (g * h) (ptEquiv j)) =
      ptEquiv.symm (nsPerm g (ptEquiv (ptEquiv.symm (nsPerm h (ptEquiv j)))))
    rw [Equiv.apply_symm_apply]
    rfl

theorem vec_piO (g : ↥O8) (j : Fin 136) :
    vec 3 nsArr[((piO g j : Fin 136) : ℕ)]! = (g : V8 ≃ₗ[ZMod 2] V8) (vec 3 nsArr[(j : ℕ)]!) :=
  congrArg Subtype.val (ptEquiv.apply_symm_apply (nsPerm g (ptEquiv j)))

theorem piO_val_eq {g : ↥O8} {x : Fin 136} {t : ℕ} (ht : t < 136)
    (h : vec 3 nsArr[t]! = (g : V8 ≃ₗ[ZMod 2] V8) (vec 3 nsArr[(x : ℕ)]!)) :
    ((piO g x : Fin 136) : ℕ) = t := by
  have h2 := vec_piO g x
  have e : ptEquiv (piO g x) = ptEquiv ⟨t, ht⟩ := Subtype.ext (h2.trans h.symm)
  exact congrArg Fin.val (ptEquiv.injective e)

theorem apply_eq_of_piO_eq_one {g : ↥O8} (hg : piO g = 1) {v : V8} (hv : quadQ 3 v = 1) :
    (g : V8 ≃ₗ[ZMod 2] V8) v = v := by
  have h := vec_piO g (ptEquiv.symm ⟨v, hv⟩)
  rw [hg, Equiv.Perm.one_apply] at h
  have hv' : vec 3 nsArr[((ptEquiv.symm ⟨v, hv⟩ : Fin 136) : ℕ)]! = v :=
    congrArg Subtype.val (ptEquiv.apply_symm_apply ⟨v, hv⟩)
  rw [hv'] at h
  exact h.symm

theorem piO_injective : Function.Injective piO := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  show (g : V8 ≃ₗ[ZMod 2] V8) v = v
  obtain ⟨j, hj, hq⟩ := (qLink_spec (code_lt256 v)).2
  have hsplit : v = vec 3 nsArr[j]! + vec 3 (nsArr[j]! ^^^ code v) := by
    rw [← vec_xor, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, vec_code]
  have h1 : quadQ 3 (vec 3 nsArr[j]!) = 1 := quadQ_ptVec ⟨j, hj⟩
  have h2 : quadQ 3 (vec 3 (nsArr[j]! ^^^ code v)) = 1 :=
    (quadQ_vec_eq_one_iff (xor_lt256 (nsArr_spec ⟨j, hj⟩).1 (code_lt256 v))).2 hq
  rw [hsplit, map_add, apply_eq_of_piO_eq_one hg h1, apply_eq_of_piO_eq_one hg h2]

noncomputable def reflO (c : ℕ) : ↥O8 :=
  ⟨reflect (quadQ 3) (vec 3 c), reflect_mem_orthogonalGroup _ _⟩

theorem rep_transArr {c : ℕ} (hc : c < 256) (hq : qNat c = true) :
    Rep 136 (transArr c) (piO (reflO c)) := by
  intro x
  rw [transArr, getElem!_ofFn_nat _ x.2]
  have hcq : CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0 := (qLink_spec hc).1.2 hq
  obtain ⟨hidx, harr⟩ := ns_ok.2.2.2 c hc hq
  have hx := (nsArr_spec x).1
  have hl := reflLink_spec hidx hx
  rw [harr] at hl
  have hy := transNat_lt256 hc hx
  have hvy : vec 3 (transNat c nsArr[(x : ℕ)]!) =
      reflect (quadQ 3) (vec 3 c) (vec 3 nsArr[(x : ℕ)]!) := by
    rw [reflect_vec hcq, hl]
  have hqy : qNat (transNat c nsArr[(x : ℕ)]!) = true := (quadQ_vec_eq_one_iff hy).1 (by
    rw [hvy, map_of_mem (reflect_mem_orthogonalGroup _ _), quadQ_ptVec x])
  obtain ⟨hidy, harry⟩ := ns_ok.2.2.2 _ hy hqy
  exact (piO_val_eq hidy (by rw [harry]; exact hvy)).symm

noncomputable def rprod (cs : List ℕ) : ↥O8 := (cs.map reflO).prod

theorem rprod_cons (c : ℕ) (cs : List ℕ) : rprod (c :: cs) = reflO c * rprod cs := by
  rw [rprod, rprod, List.map_cons, List.prod_cons]

theorem prodArr_nil : prodArr [] = idA 136 := List.foldr_nil

theorem prodArr_cons (c : ℕ) (cs : List ℕ) :
    prodArr (c :: cs) = compA 136 (transArr c) (prodArr cs) := List.foldr_cons

theorem rep_prodArr : ∀ cs : List ℕ, (∀ c ∈ cs, c < 256 ∧ qNat c = true) →
    Rep 136 (prodArr cs) (piO (rprod cs))
  | [], _ => by
    rw [rprod, List.map_nil, List.prod_nil, map_one, prodArr_nil]
    exact rep_idA
  | c :: cs, h => by
    rw [rprod_cons, map_mul, prodArr_cons]
    have hc := h c List.mem_cons_self
    exact rep_compA (rep_transArr hc.1 hc.2)
      (rep_prodArr cs fun d hd => h d (List.mem_cons_of_mem c hd))

theorem rprod_mem_commutator : ∀ cs : List ℕ, cs.length % 2 = 0 →
    (∀ c ∈ cs, quadQ 3 (vec 3 c) = 1) → ((rprod cs : ↥O8) : V8 ≃ₗ[ZMod 2] V8) ∈ ⁅O8, O8⁆
  | [], _, _ => by
    rw [rprod, List.map_nil, List.prod_nil]
    exact Subgroup.one_mem _
  | [_], h, _ => absurd h (by simp)
  | a :: b :: cs, h, hq => by
    have e : ((rprod (a :: b :: cs) : ↥O8) : V8 ≃ₗ[ZMod 2] V8) =
        (reflect (quadQ 3) (vec 3 a) * reflect (quadQ 3) (vec 3 b)) *
          ((rprod cs : ↥O8) : V8 ≃ₗ[ZMod 2] V8) := by
      rw [rprod_cons, rprod_cons, Subgroup.coe_mul, Subgroup.coe_mul, mul_assoc]
      rfl
    rw [e]
    refine Subgroup.mul_mem _ (CFSG.RankThree.Literature.FSmith.reflect_mul_reflect_mem_commutator
      (nondegenerate_quadQ 3) (by rw [finrank_V8]; norm_num) (hq a List.mem_cons_self)
      (hq b (List.mem_cons_of_mem a List.mem_cons_self))) (rprod_mem_commutator cs ?_ ?_)
    · simp only [List.length_cons] at h
      omega
    · exact fun c hc => hq c (List.mem_cons_of_mem a (List.mem_cons_of_mem b hc))

theorem gen_eq_piO {i : ℕ} (hi : i < 10) :
    ∃ G : ↥O8, (G : V8 ≃ₗ[ZMod 2] V8) ∈ ⁅O8, O8⁆ ∧ piO G = gen i := by
  obtain ⟨hl, hc, he⟩ := eich_spec hi
  refine ⟨rprod (eichRefl.getD i []), rprod_mem_commutator _ hl fun c h =>
    (quadQ_vec_eq_one_iff (hc c h).1).2 (hc c h).2, ?_⟩
  exact (eq_of_eqA (rep_gen (by omega)) (rep_prodArr _ hc) he).symm

theorem omegaT_le {x : Equiv.Perm (Fin 136)} (hx : x ∈ omegaT) :
    ∃ G : ↥O8, (G : V8 ≃ₗ[ZMod 2] V8) ∈ ⁅O8, O8⁆ ∧ piO G = x := by
  have hle : omegaT ≤ (⁅O8, O8⁆.subgroupOf O8).map piO := by
    rw [omegaT_eq, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨G, hG, hGe⟩ := gen_eq_piO hi
    exact ⟨G, hG, hGe⟩
  obtain ⟨G, hG, hGe⟩ := hle hx
  exact ⟨G, hG, hGe⟩

theorem autT_le {x : Equiv.Perm (Fin 136)} (hx : x ∈ autT) : ∃ H : ↥O8, piO H = x := by
  have hle : autT ≤ piO.range := by
    rw [autT_eq, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    by_cases h10 : i < 10
    · obtain ⟨G, -, hGe⟩ := gen_eq_piO h10
      exact ⟨G, hGe⟩
    · obtain rfl : i = 10 := by omega
      exact ⟨reflO 64, (eq_of_eqA (rep_gen (by norm_num)) (rep_transArr (by norm_num) rfl)
        gen10_spec).symm⟩
  exact hle hx

theorem piO_mem_autT (g : ↥O8) : piO g ∈ autT := by
  let H : Subgroup (V8 ≃ₗ[ZMod 2] V8) := (autT.comap piO).map (Subgroup.subtype O8)
  have hrefl : Set.range (reflect (quadQ 3)) ⊆ H := by
    rintro _ ⟨v, rfl⟩
    by_cases hv : quadQ 3 v = 0
    · rw [reflect_of_map_eq_zero hv]
      exact H.one_mem
    · have hv1 : quadQ 3 v = 1 := zmod_two_eq_one_of_ne_zero hv
      have hc := code_lt256 v
      have hq := qNat_code hv1
      refine ⟨reflO (code v), ?_, by
        show reflect (quadQ 3) (vec 3 (code v)) = reflect (quadQ 3) v
        rw [vec_code]⟩
      obtain ⟨hidx, harr⟩ := ns_ok.2.2.2 _ hc hq
      have hs := transMem_spec hidx
      rw [harr] at hs
      show piO (reflO (code v)) ∈ autQ.originalSubgroup
      exact (ofArrays_mem_iff (by norm_num) autChain_ok.1 (rep_transArr hc hq)).1 hs
  have hO : (g : V8 ≃ₗ[ZMod 2] V8) ∈ Subgroup.closure (Set.range (reflect (quadQ 3))) := by
    rw [← orthogonalGroup_eq_closure_reflect (nondegenerate_quadQ 3) (by rw [finrank_V8]; norm_num)
      (Or.inl (by rw [finrank_V8]; norm_num))]
    exact g.2
  obtain ⟨g', hg', hg'e⟩ := (Subgroup.closure_le H).2 hrefl hO
  have : g' = g := Subtype.ext hg'e
  rw [← this]
  exact hg'

theorem mainPerm_three : mainPerm 3 = piO (reflO 64) :=
  eq_of_eqA (mainPerm_spec (by norm_num)).1 (rep_transArr (by norm_num) rfl) reflRep_spec

end Model

theorem even_gt_two {G : Type*} [Group G] {z : G} (h12 : z ^ 12 = 1) (h2 : z ^ 2 ≠ 1)
    (h3 : z ^ 3 ≠ 1) : 2 < orderOf z ∧ Even (orderOf z) := by
  have hd : orderOf z ∣ 12 := orderOf_dvd_of_pow_eq_one h12
  have hn2 : ¬ orderOf z ∣ 2 := fun h => h2 (orderOf_dvd_iff_pow_eq_one.mp h)
  have hn3 : ¬ orderOf z ∣ 3 := fun h => h3 (orderOf_dvd_iff_pow_eq_one.mp h)
  have hle : orderOf z ≤ 12 := Nat.le_of_dvd (by norm_num) hd
  generalize orderOf z = n at hd hn2 hn3 hle ⊢
  interval_cases n <;> first | omega | exact ⟨by norm_num, by decide⟩

theorem witWords_letters : witWords.all (lettersOK 18) = true := by decide

theorem witTypes_lt {k : ℕ} (hk : k < 4) : witTypes.getD k 0 < 5 := by
  interval_cases k <;> decide

theorem wit_order {k : ℕ}
    (hk : k < 4) :
    2 < orderOf (mainPerm (witTypes.getD k 0) * (permOfArr 136 (omegaW (witWords.getD k [])) *
        mainPerm (witTypes.getD k 0) * (permOfArr 136 (omegaW (witWords.getD k [])))⁻¹)) ∧
      Even (orderOf (mainPerm (witTypes.getD k 0) *
        (permOfArr 136 (omegaW (witWords.getD k [])) * mainPerm (witTypes.getD k 0) *
          (permOfArr 136 (omegaW (witWords.getD k [])))⁻¹))) := by
  obtain ⟨hinv, h12, h2, h3⟩ := type_spec hk
  obtain ⟨hgR, -⟩ := omegaW_spec (CFSG.EvenSmallLie.OmegaEight.letters_of_all witWords_letters k)
  have hgiR := rep_inv_of_isInvA hgR hinv
  have hyR := (mainPerm_spec (witTypes_lt hk)).1
  have hzR := rep_compA hyR (rep_conjArr hgR hgiR hyR)
  refine even_gt_two (eq_of_eqA (rep_powArr hzR 12) rep_idA h12) (fun h => ?_) (fun h => ?_)
  · have := (eqA_iff (rep_powArr hzR 2) rep_idA).2 h
    rw [show compA 136 (mainArrs.getD (witTypes.getD k 0) #[])
      (conjArr (omegaW (witWords.getD k [])) (mainArrs.getD (witTypes.getD k 0) #[])) = zA k
      from rfl, h2] at this
    exact Bool.false_ne_true this
  · have := (eqA_iff (rep_powArr hzR 3) rep_idA).2 h
    rw [show compA 136 (mainArrs.getD (witTypes.getD k 0) #[])
      (conjArr (omegaW (witWords.getD k [])) (mainArrs.getD (witTypes.getD k 0) #[])) = zA k
      from rfl, h3] at this
    exact Bool.false_ne_true this

theorem core (D : ↥O8)
    (hDD : D * D = 1)
    (hodd : ∀ G : ↥O8, (G : V8 ≃ₗ[ZMod 2] V8) ∈ ⁅O8, O8⁆ →
      orderOf (D * (G * D * G⁻¹)) ≤ 2 ∨ Odd (orderOf (D * (G * D * G⁻¹)))) :
    ∃ c : V8, ∀ v : V8, (D : V8 ≃ₗ[ZMod 2] V8) v - v ∈ Submodule.span (ZMod 2) {c} := by
  by_cases hD1 : D = 1
  · refine ⟨0, fun v => ?_⟩
    rw [hD1]
    show v - v ∈ _
    rw [sub_self]
    exact Submodule.zero_mem _
  have hord : orderOf D = 2 := orderOf_eq_prime (by rw [sq, hDD]) hD1
  have hπord : orderOf (piO D) = 2 := by rw [orderOf_injective piO piO_injective D, hord]
  obtain ⟨i, hi, h, hh, hx, -⟩ := exists_conj_main (piO_mem_autT D) hπord
  have hcases : i = 3 ∨ ∃ k < 4, witTypes.getD k 0 = i := by
    interval_cases i
    · exact Or.inr ⟨0, by norm_num, rfl⟩
    · exact Or.inr ⟨1, by norm_num, rfl⟩
    · exact Or.inr ⟨2, by norm_num, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨3, by norm_num, rfl⟩
  rcases hcases with rfl | ⟨k, hk, rfl⟩
  ·
    obtain ⟨H, rfl⟩ := autT_le hh
    have hDe : D = H * reflO 64 * H⁻¹ :=
      piO_injective (by rw [map_mul, map_mul, map_inv, ← mainPerm_three, ← hx])
    refine ⟨(H : V8 ≃ₗ[ZMod 2] V8) (vec 3 64), fun v => ?_⟩
    have hq64 : quadQ 3 (vec 3 64) = 1 := (quadQ_vec_eq_one_iff (by norm_num)).2 rfl
    have e : (D : V8 ≃ₗ[ZMod 2] V8) v = (H : V8 ≃ₗ[ZMod 2] V8)
        (reflect (quadQ 3) (vec 3 64) ((H : V8 ≃ₗ[ZMod 2] V8).symm v)) := by
      rw [hDe]
      rfl
    rw [e, reflect_apply_of_map_eq_one hq64, map_add, map_smul, LinearEquiv.apply_symm_apply,
      add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  ·
    exfalso
    have hgT := (omegaW_spec (CFSG.EvenSmallLie.OmegaEight.letters_of_all witWords_letters k)).2
    have hg' := (conj_mem_omegaT hh).1 hgT
    obtain ⟨G, hG, hGe⟩ := omegaT_le hg'
    have hπ : piO (D * (G * D * G⁻¹)) = h * (mainPerm (witTypes.getD k 0) *
        (permOfArr 136 (omegaW (witWords.getD k [])) * mainPerm (witTypes.getD k 0) *
          (permOfArr 136 (omegaW (witWords.getD k [])))⁻¹)) * h⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, hGe, hx]
      group
    have hordeq : orderOf (D * (G * D * G⁻¹)) = orderOf (mainPerm (witTypes.getD k 0) *
        (permOfArr 136 (omegaW (witWords.getD k [])) * mainPerm (witTypes.getD k 0) *
          (permOfArr 136 (omegaW (witWords.getD k [])))⁻¹)) := by
      rw [← orderOf_injective piO piO_injective, hπ]
      exact MulEquiv.orderOf_eq (MulAut.conj h) _
    obtain ⟨h2, he⟩ := wit_order hk
    rw [← hordeq] at h2 he
    rcases hodd G hG with h1 | h1
    · omega
    · exact (Nat.not_even_iff_odd.2 h1) he

theorem finrank_range_le_one
    (D : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) (hDD : D * D = 1)
    (hN : ∀ y ∈ CFSG.RankThree.PartTwo.omegaMinusTwo 3,
      D * y * D⁻¹ ∈ CFSG.RankThree.PartTwo.omegaMinusTwo 3)
    (hodd : ∀ G ∈ CFSG.RankThree.PartTwo.omegaMinusTwo 3,
      orderOf (D * (G * D * G⁻¹)) ≤ 2 ∨ Odd (orderOf (D * (G * D * G⁻¹)))) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin
      ((D : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) - 1))) ≤ 1 := by
  set e := toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) with he
  have hN' : ∀ x ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (3 + 1) (ZMod 2) 1 1),
      D * x * D⁻¹ ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (3 + 1) (ZMod 2) 1 1) := by
    rw [← CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.omegaMinusTwo_eq_statedOmega 3]
    exact hN
  have hiso : ∀ v, CFSG.Open.StatedQuadMinus (3 + 1) (ZMod 2) 1 1
      ((D : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
        CFSG.Open.StatedQuadMinus (3 + 1) (ZMod 2) 1 1 v := fun v =>
    isometry_of_normalizes_statedOmega
      (CFSG.LieType.Universal.Spin.coe_quadMinus (3 + 1) (ZMod 2) 1 1) (nondegenerate_quadQ 3)
      (by simp) hN' v
  have hDO : e D ∈ O8 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
    rw [he, toLinEquiv_apply]
    have h := hiso v
    rwa [← CFSG.LieType.Universal.Spin.coe_quadMinus (3 + 1) (ZMod 2) 1 1] at h
  let D' : ↥O8 := ⟨e D, hDO⟩
  have hD'D' : D' * D' = 1 := Subtype.ext (by
    show e D * e D = 1
    rw [← map_mul, hDD, map_one])
  have hodd' : ∀ G : ↥O8, (G : V8 ≃ₗ[ZMod 2] V8) ∈ ⁅O8, O8⁆ →
      orderOf (D' * (G * D' * G⁻¹)) ≤ 2 ∨ Odd (orderOf (D' * (G * D' * G⁻¹))) := by
    intro G hG
    have hGm : e.symm (G : V8 ≃ₗ[ZMod 2] V8) ∈ CFSG.RankThree.PartTwo.omegaMinusTwo 3 := by
      rw [omegaMinusTwo_eq_comap, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply]
      exact hG
    have hcoe : ((D' * (G * D' * G⁻¹) : ↥O8) : V8 ≃ₗ[ZMod 2] V8) =
        e (D * (e.symm (G : V8 ≃ₗ[ZMod 2] V8) * D * (e.symm (G : V8 ≃ₗ[ZMod 2] V8))⁻¹)) := by
      rw [map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have hordeq : orderOf (D' * (G * D' * G⁻¹)) =
        orderOf (D * (e.symm (G : V8 ≃ₗ[ZMod 2] V8) * D * (e.symm (G : V8 ≃ₗ[ZMod 2] V8))⁻¹)) := by
      rw [← Subgroup.orderOf_coe, hcoe, MulEquiv.orderOf_eq]
    rw [hordeq]
    exact hodd _ hGm
  obtain ⟨c, hc⟩ := core D' hD'D' hodd'
  have hle : LinearMap.range (Matrix.mulVecLin
      ((D : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) - 1)) ≤
        Submodule.span (ZMod 2) {c} := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
    have h := hc v
    rwa [show ((D' : ↥O8) : V8 ≃ₗ[ZMod 2] V8) v =
      (D : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) *ᵥ v from
        toLinEquiv_apply D v] at h
  calc Module.finrank (ZMod 2) ↥(LinearMap.range (Matrix.mulVecLin
        ((D : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) - 1)))
      ≤ Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) ({c} : Set V8)) :=
        Submodule.finrank_mono hle
    _ ≤ 1 := by
      by_cases hc0 : c = 0
      · subst hc0
        rw [Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
        exact Nat.zero_le _
      · rw [finrank_span_singleton hc0]

end CFSG.CGT.Foote82.OmegaEight

namespace CFSG.CGT.Foote82

theorem basOmegaEight_holds :
    BASOmegaEight := by
  intro V _ _ _ L hL _ _ d hd hd2 hodd
  obtain ⟨D, hDD, hN, hoddD, hrank⟩ := OmegaMinusMat.exists_matrix_data hL hd hd2 hodd
  have h := OmegaEight.finrank_range_le_one D hDD hN hoddD
  omega

end CFSG.CGT.Foote82

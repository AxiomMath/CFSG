module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabJ3Shape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNThreeShape
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.HN
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4O2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Z

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.HardMathSupport.Dickson.I271 (ShapeRkAt)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (PConstrainedShape)

theorem noU42Comp_of_not_dvd {Q : Type} [Group Q] [Finite Q] {k : Q}
    (h : ¬ 25920 ∣ Nat.card (Subgroup.centralizer ({k} : Set Q))) : NoU42Comp 3 k := by
  intro I hI hc
  apply h
  rw [← hc]
  have h2 : Nat.card (PSimple 3 I) ∣ Nat.card (PQuot 3 I) := Subgroup.card_quotient_dvd_card _
  have h3 : Nat.card (PQuot 3 I) ∣ Nat.card I := Subgroup.card_quotient_dvd_card _
  exact h2.trans (h3.trans (Subgroup.card_dvd_of_le hI.1))

theorem noU42Comp_of_pConstrained {Q : Type} [Group Q] [Finite Q] {k : Q}
    (h : PConstrainedShape 3 (Subgroup.centralizer ({k} : Set Q))) : NoU42Comp 3 k :=
  fun _ hI => (KDSpor.false_of_glaPComponent_of_pConstrained Nat.prime_three h hI).elim

theorem noU42Comp_of_shapeRkAt {Q : Type} [Group Q] [Finite Q] {k : Q}
    {Rk : ∀ (T : Type) [Group T], Prop}
    (h : ShapeRkAt 3 (fun T _ => Nat.card T ≠ 25920) Rk k) : NoU42Comp 3 k := by
  intro I hI
  rcases h with hc | ⟨J, -, huniq, hg, -⟩
  · exact (KDSpor.false_of_glaPComponent_of_pConstrained Nat.prime_three hc hI).elim
  · rw [huniq I hI]
    exact hg

theorem noU42Comp_conj {Q : Type} [Group Q] [Finite Q] {c : Q} (h : NoU42Comp 3 c) (g : Q) :
    NoU42Comp 3 (g * c * g⁻¹) :=
  noU42Comp_of_mulEquiv Nat.prime_three (MulAut.conj g) h

theorem card_centralizer_sub {G : Type} [Group G] (P : Subgroup G) (k : ↥P) :
    Nat.card (Subgroup.centralizer ({k} : Set ↥P)) =
      Nat.card ↥(Subgroup.centralizer ({(k : G)} : Set G) ⊓ P) := by
  rw [← CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype' P k,
    Subgroup.card_map_of_injective P.subtype_injective]


section J3

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Schreier

theorem noU42Comp_j3P (k : ↥j3P) (hk : orderOf k = 3) : NoU42Comp 3 k := by
  have hs3 : orderOf (k : Equiv.Perm (Fin 6156)) = 3 := by
    rw [← Subgroup.orderOf_coe] at hk
    exact hk
  obtain ⟨k₀, hk₀, c, hc, e, he, hkeq⟩ := j3t_fusion k.2 hs3
  let K₀ : ↥j3P := ⟨k₀, hk₀⟩
  let y : ↥j3P := K₀⁻¹ * k * K₀
  have hy : (y : Equiv.Perm (Fin 6156)) = c ^ e := by
    show k₀⁻¹ * (k : Equiv.Perm (Fin 6156)) * k₀ = c ^ e
    rw [hkeq]
    group
  have hY : NoU42Comp 3 y := by
    refine noU42Comp_of_not_dvd ?_
    rw [card_centralizer_sub, hy]
    rcases hc with rfl | rfl
    · rw [CFSG.Quasithin.Kleidman.centralizer_pow_eq (c := j3tXA)
        (j3tReps_spec (c := 0) (by norm_num)).2 he,
        CFSG.AGLEmbeddingD2.Wilson.Census228Spor.card_centralizer_XA]
      norm_num
    · rw [CFSG.Quasithin.Kleidman.centralizer_pow_eq (c := j3tXB)
        (j3tReps_spec (c := 1) (by norm_num)).2 he,
        CFSG.AGLEmbeddingD2.Wilson.Census228Spor.card_centralizer_XB]
      norm_num
  have h := noU42Comp_conj hY K₀
  have hk' : K₀ * y * K₀⁻¹ = k := by
    simp only [y]
    group
  rwa [hk'] at h

theorem row_j3 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : I1431SporRow .J3 := by
  have e : NativeSporadic.Carrier .J3 ≃* ↥j3P :=
    CFSG.RankThree.PartTwo.Sec21.Item228CensusProof.j3CarrierEquiv
  have hc : Nat.card ↥j3P = 50232960 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  haveI : IsSimpleGroup ↥j3P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J3.isSimpleGroup_J3 e.symm
  exact row_of_model (s := .J3) (Q := ↥j3P) hOut (e.symm.trans (hbr .J3).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    noU42Comp_j3P

end J3

section HN

open CFSG.Sporadic.HNSchreier CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement

set_option maxRecDepth 4000 in
theorem noU42Comp_s1 : NoU42Comp 3 (sJ 0) := by
  haveI : Finite ↥JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  obtain ⟨-, -, hcomm⟩ := CJ_s1_structure
  have hder := commutator_CJ_s1
  haveI hsimple : IsSimpleGroup ↥L1J := by
    have := alt3_simple
    exact MulEquiv.isSimpleGroup (alt3.equivMapOfInjective iotaA iotaA_injective).symm
  have hcard : Nat.card ↥L1J = 181440 := by
    rw [show (L1J : Subgroup JH) = alt3.map iotaA from rfl,
      Subgroup.card_map_of_injective iotaA_injective, card_alt3]
  have hLC : L1J ≤ Subgroup.centralizer ({sJ 0} : Set ↥JH) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx)
  have hnp : ¬ (Nat.card ↥L1J).Prime := by
    rw [hcard]
    norm_num
  have hnab : ∃ a b : ↥L1J, a * b ≠ b * a := exists_noncomm_of_simple_card (G := ↥L1J) hnp
  have h3 : 3 ∣ Nat.card ↥L1J := by
    rw [hcard]
    norm_num
  have hk : Nat.card ↥(Subgroup.centralizer ({sJ 0} : Set ↥JH)) = Nat.card ↥L1J * 3 ^ 1 := by
    rw [show Subgroup.centralizer ({sJ 0} : Set ↥JH) = CJ (sJ 0) from rfl, card_CJ_s1, hcard]
    norm_num
  refine noU42Comp_of_shapeRkAt (Rk := fun _ _ => True) ?_
  refine shapeRkAt_of_data (Good := fun T _ => Nat.card T ≠ 25920) (Rk := fun _ _ => True)
    Nat.prime_three (fun T T' _ _ e h hc => h ((Nat.card_congr e.toEquiv).trans hc))
    (fun _ _ _ _ _ h => h) (sJ 0) L1J hLC ?_ hsimple hnab h3 hk (by rw [hcard]; norm_num) trivial
  intro g hg l hl
  have h1 : ⁅g, l⁆ ∈ ⁅CJ (sJ 0), CJ (sJ 0)⁆ := Subgroup.commutator_mem_commutator hg (hLC hl)
  rw [hder] at h1
  have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
    rw [commutatorElement_def]; group
  rw [h3]
  exact L1J.mul_mem h1 hl

theorem noU42Comp_JH (k : ↥JH) (hk : orderOf k = 3) : NoU42Comp 3 k := by
  haveI : Finite ↥JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  rcases (order_three_classes k).1 hk with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    rw [← hg]
    exact noU42Comp_conj noU42Comp_s1 g
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    rw [← hg]
    exact noU42Comp_conj
      (noU42Comp_of_pConstrained (pConstrainedShape_of_hn3bRChecks hn3bR_checks)) g

set_option maxRecDepth 100000 in
theorem row_hn (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    I1431SporRow .HN := by
  haveI : Finite ↥JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  haveI hHN : IsSimpleGroup NativeSporadic.HN := CFSG.Sporadic.HN.isSimpleGroup_HN
  haveI : IsSimpleGroup ↥JH := @MulEquiv.isSimpleGroup _ _ _ _ hHN hnEquivJ.symm
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have hp : ¬ (Nat.card ↥JH).Prime := by rw [card_JH]; norm_num
  have hnc : ∃ x y : ↥JH, x * y ≠ y * x :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (S := ↥JH) hp
  have hb : ↥JH ≃* (TauCeti.CFSGIndex.sporadic .HN).Group := hnEquivJ.symm.trans e
  refine row_of_model (s := .HN) (Q := ↥JH) hOut ?_ ?_ ?_
  · exact hb
  · exact hnc
  · exact noU42Comp_JH

end HN

end CFSG.LocalAnalysis.GLTheoremA.I1431Z

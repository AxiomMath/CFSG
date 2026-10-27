module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.I1416QJ3

open CFSG.HardMathSupport.Dickson.I271
open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.CosetTable
  CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.Asc83Table CFSG.RankThree.PartTwo CFSG.AGLEmbeddingD2.Wilson
  CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
open CFSG.LocalAnalysis.GLTheoremA.I1416Rows CFSG.LocalAnalysis.GLTheoremA.I1416QRows
open scoped commutatorElement


theorem qcompOK_j3A (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) (y : ↥j3P)
    (hy : Subgroup.centralizer ({(y : Equiv.Perm (Fin 6156))} : Set (Equiv.Perm (Fin 6156))) =
      Subgroup.centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156)))) : QCompOK 3 y := by
  obtain ⟨eD⟩ := Census228Spor.nonempty_mulEquiv_D_alt6
  have hDC : closure (Set.range j3tD) ≤
      centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :=
    le_inf Census228Spor.closure_j3tD_le_centralizer tabJ3_D_le
  haveI hs : IsSimpleGroup ↥(closure (Set.range j3tD)) :=
    @MulEquiv.isSimpleGroup _ _ _ _
      (alternatingGroup.isSimpleGroup (by simp)) eD
  haveI : Finite ↥(closure (Set.range j3tD)) :=
    Nat.finite_of_card_ne_zero (by rw [j3t_derived.2]; norm_num)
  have hnab : ∃ a b : ↥(closure (Set.range j3tD)), a * b ≠ b * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
      (by rw [j3t_derived.2]; norm_num)
  have hsh : ShapeRkAt 3 QTypeThree (fun _ _ => True) y := by
    refine shapeRkAt_of_subgroup_data Nat.prime_three qtypeThree_of_equiv
      (fun _ _ _ _ _ h => h) j3P y (closure (Set.range j3tD)) (by rw [hy]; exact hDC)
      ?_ hs hnab (by rw [j3t_derived.2]; norm_num) (k := 1) ?_ (qtypeOK_A6 hb eD) trivial
    · intro g hg l hl
      rw [hy] at hg
      have h1 : ⁅g, l⁆ ∈ ⁅centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P,
          centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P⁆ :=
        Subgroup.commutator_mem_commutator hg (hDC hl)
      have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact (closure (Set.range j3tD)).mul_mem (j3t_derived.1 h1) hl
    · rw [hy, Census228Spor.card_centralizer_XA, j3t_derived.2]
      norm_num
  exact qcompOK_of_shapeRkAt Nat.prime_three hsh fun _ _ h => h

theorem qcompOK_j3B (y : ↥j3P)
    (hy : Subgroup.centralizer ({(y : Equiv.Perm (Fin 6156))} : Set (Equiv.Perm (Fin 6156))) =
      Subgroup.centralizer ({j3tXB} : Set (Equiv.Perm (Fin 6156)))) : QCompOK 3 y := by
  refine qcompOK_of_pConstrained Nat.prime_three
    (pConstrainedShape_of_map_injective j3P.subtype j3P.subtype_injective ?_)
  rw [map_centralizer_subtype', hy]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ↥(centralizer ({j3tXB} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P) :=
    IsPGroup.of_card (n := 5) (by rw [Census228Spor.card_centralizer_XB]; norm_num)
  exact ⟨_, le_rfl, fun g hg q hq => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hq)
    (Subgroup.inv_mem _ hg), hp, inf_le_left⟩

theorem qcompOK_j3P (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) (k : ↥j3P) (hk : orderOf k = 3) : QCompOK 3 k := by
  have hs3 : orderOf (k : Equiv.Perm (Fin 6156)) = 3 := by
    rw [Subgroup.orderOf_coe, hk]
  obtain ⟨k₀, hk₀, c, hc, e, he, hkeq⟩ := j3t_fusion k.2 hs3
  let K₀ : ↥j3P := ⟨k₀, hk₀⟩
  let y : ↥j3P := K₀⁻¹ * k * K₀
  have hy : (y : Equiv.Perm (Fin 6156)) = c ^ e := by
    show k₀⁻¹ * (k : Equiv.Perm (Fin 6156)) * k₀ = c ^ e
    rw [hkeq]
    group
  have hok : QCompOK 3 y := by
    rcases hc with rfl | rfl
    · refine qcompOK_j3A hb y ?_
      rw [hy]
      exact CFSG.Quasithin.Kleidman.centralizer_pow_eq (j3tReps_spec (c := 0) (by norm_num)).2 he
    · refine qcompOK_j3B y ?_
      rw [hy]
      exact CFSG.Quasithin.Kleidman.centralizer_pow_eq (j3tReps_spec (c := 1) (by norm_num)).2 he
  have hconj := QCompOK.of_mulEquiv Nat.prime_three (MulAut.conj K₀) hok
  have hk' : (MulAut.conj K₀) y = k := by
    rw [MulAut.conj_apply]
    simp only [y]
    group
  rw [hk'] at hconj
  exact hconj

theorem qrow_J3_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416QRow .J3 3 := by
  have e : NativeSporadic.Carrier .J3 ≃* ↥j3P :=
    CFSG.RankThree.PartTwo.Sec21.Item228CensusProof.j3CarrierEquiv
  have hc : Nat.card (NativeSporadic.Carrier .J3) = 50232960 := CFSG.Sporadic.J3.card_J3
  haveI : Finite (NativeSporadic.Carrier .J3) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (NativeSporadic.Carrier .J3) := CFSG.Sporadic.J3.isSimpleGroup_J3
  haveI : Finite ↥j3P := Finite.of_equiv _ e.toEquiv
  haveI : IsSimpleGroup ↥j3P := @MulEquiv.isSimpleGroup _ _ _ _ inferInstance e.symm
  have hc' : Nat.card ↥j3P = 50232960 := (Nat.card_congr e.toEquiv).symm.trans hc
  exact qrow_of_model hOut (e.symm.trans (hbr .J3).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc']; norm_num))
    (qcompOK_j3P hb)

end CFSG.HardMathSupport.Dickson.I271.I1416QJ3

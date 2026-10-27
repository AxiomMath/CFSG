module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4G3
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4F2
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4G2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4G

open Polynomial CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open Matrix

theorem fpf_layer (A : ↥(StatedSp 2 F8)) (hA3 : A ^ 3 = 1) (hP : Pm (mat A) = 0) :
    ∃ N : Subgroup ↥(StatedSp 2 F8),
      N ≤ Subgroup.centralizer ({A} : Set ↥(StatedSp 2 F8)) ∧
      (∀ g ∈ Subgroup.centralizer ({A} : Set ↥(StatedSp 2 F8)),
        ∀ h ∈ Subgroup.centralizer ({A} : Set ↥(StatedSp 2 F8)), ⁅g, h⁆ ∈ N) ∧
      Nonempty (↥N ≃* ↥(StatedSL 2 F8)) := by
  have hC := centralizer_le_spSupported A hA3 hP
  have hsd := (blocks_of_Pm A hA3 hP).selfDual ⟨h0 F8, h0_mem_primaryFactors A hP⟩
    (h0_ne_X_sub_one F8) (reciprocal_h0 F8)
  obtain ⟨d, hdeg, -, -, -, -, -, -, -, hE, -, Hf, hsymm, hsep, -, -, φ, -⟩ := hsd.exists_half
  have hdeg' : (h0 F8).natDegree = 2 * d := hdeg
  rw [natDegree_h0] at hdeg'
  have hd : d = 1 := by omega
  subst hd
  haveI : Fact (Irreducible (h0 F8)) := ⟨irreducible_h0_F8⟩
  obtain ⟨eSU⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hsymm hsep
    (finrank_primaryComponent_h0 A hP)
  haveI := hE.finite
  have hcardfix : Nat.card hE.fixedField = Nat.card F8 := by
    rw [hE.card_fixedField]
    norm_num [card_F8]
  haveI : Fintype ↥hE.fixedField := Fintype.ofFinite _
  haveI : Fintype F8 := Fintype.ofFinite _
  let ψ : ↥hE.fixedField ≃+* F8 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardfix])
  let eSL : ↥(sesqSpecialUnitaryGroup Hf) ≃* ↥(StatedSL 2 F8) :=
    eSU.trans ((slRingEquiv ψ).trans (slStatedEquiv F8))
  let f : ↥(sesqUnitaryGroup Hf) →* StatedSp 2 F8 :=
    (spSupported A {h0 F8}).subtype.comp (φ.symm.toMonoidHom)
  have hf : Function.Injective f := Subtype.val_injective.comp φ.symm.injective
  let K1 : Subgroup ↥(sesqUnitaryGroup Hf) :=
    (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)
  refine ⟨K1.map f, ?_, ?_, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact spSupported_le_centralizer A {h0 F8} (φ.symm u).2
  · intro g hg h hh
    have hg' : g ∈ spSupported A {h0 F8} := hC hg
    have hh' : h ∈ spSupported A {h0 F8} := hC hh
    let g' : ↥(spSupported A {h0 F8}) := ⟨g, hg'⟩
    let h' : ↥(spSupported A {h0 F8}) := ⟨h, hh'⟩
    refine Subgroup.mem_map.2 ⟨φ ⁅g', h'⁆, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.2 (mem_sesqSpecialUnitaryGroup.2 ⟨(φ ⁅g', h'⁆).2, ?_⟩)
      rw [map_commutatorElement φ g' h']
      exact det_commutatorElement_eq_one (φ g').1 (φ h').1
    · show (spSupported A {h0 F8}).subtype (φ.symm (φ ⁅g', h'⁆)) = ⁅g, h⁆
      rw [MulEquiv.symm_apply_apply]
      rfl
  · exact ⟨(Subgroup.equivMapOfInjective K1 f hf).symm.trans
      ((Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).trans eSL)⟩

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4G

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4G

theorem kdLieRowSp4EightFPFLayer_holds : LevelLieSp4F.KDLieRowSp4EightFPFLayer :=
  fun A hA3 hP => fpf_layer A hA3 hP

theorem kdLieRowSp4Eight_holds : KDLieRowSp4Eight :=
  LevelLieSp4F.kdLieRowSp4Eight_of_FPFLayer kdLieRowSp4EightFPFLayer_holds

end CFSG.LocalAnalysis.GLTheoremA

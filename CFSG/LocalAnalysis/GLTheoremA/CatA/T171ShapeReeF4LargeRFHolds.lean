module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeReeF4LargeRFInner
import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.PartOne.RF4

section Certificates

theorem rf_holds : LargeReeCentralizerActsInner := by
  intro m hv S _ _ ⟨eS⟩ p hp hp3 x hx N hNle _hN2 huniq hNcomp c hc
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hR := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
  obtain ⟨K, hfield, hfinite, hchar, hKcard, ⟨eK⟩⟩ :=
    CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma hm1 hR
  letI := hfield
  letI := hfinite
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := hchar
  let e : S ≃* ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K m) := eS.trans eK
  letI : Finite ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K m) := Subtype.finite
  have hX : orderOf (e x) = p :=
    (orderOf_injective e.toMonoidHom e.injective x).trans hx
  have hc' : e c ∈ Subgroup.centralizer ({e x} : Set ↥(ReeTag.F4.reeGamma K m)) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    simpa using congrArg e hc
  have hNle' : N.map e.toMonoidHom ≤
      Subgroup.centralizer ({e x} : Set ↥(ReeTag.F4.reeGamma K m)) := by
    intro g hg
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hg
    have hnC : n * x = x * n := Subgroup.mem_centralizer_singleton_iff.1 (hNle hn)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg e hnC
  have huniq' : ∀ D : Subgroup ↥(ReeTag.F4.reeGamma K m),
      CFSG.RankThree.PartOne.IsComponentOf
        (Subgroup.centralizer ({e x} : Set ↥(ReeTag.F4.reeGamma K m))) D →
        D = N.map e.toMonoidHom := by
    intro D hD
    have hD' : CFSG.RankThree.PartOne.IsComponentOf
        (Subgroup.centralizer ({x} : Set S)) (D.map e.symm.toMonoidHom) := by
      have h := CFSG.RankThree.PartOne.isComponentOf_map_mulEquiv e.symm hD
      rwa [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e.symm (e x),
      e.symm_apply_apply] at h
    have h1 : D.map e.symm.toMonoidHom = N := huniq _ hD'
    have hsymm : (D.map e.symm.toMonoidHom).map e.toMonoidHom = D := by
      rw [Subgroup.map_map]
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
        ext t
        simp
      rw [hcomp, Subgroup.map_id]
    calc D = (D.map e.symm.toMonoidHom).map e.toMonoidHom := hsymm.symm
      _ = N.map e.toMonoidHom := by rw [h1]
  have hNcomp' : N.map e.toMonoidHom ≠ ⊥ → CFSG.RankThree.PartOne.IsComponentOf
      (Subgroup.centralizer ({e x} : Set ↥(ReeTag.F4.reeGamma K m))) (N.map e.toMonoidHom) := by
    intro hne
    have hNne : N ≠ ⊥ := by
      rintro rfl
      exact hne (by simp)
    have h := CFSG.RankThree.PartOne.isComponentOf_map_mulEquiv e (hNcomp hNne)
    rwa [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x] at h
  obtain ⟨n', hn', hact⟩ :=
    inner_of_reeGamma hm1 hKcard hp hp3 (e x) hX (N.map e.toMonoidHom) hNle' huniq' hNcomp'
      (e c) hc'
  obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.mp hn'
  have hsn : e.symm n' = n := by
    simpa [← hne] using e.symm_apply_apply n
  refine ⟨e.symm n', hsn ▸ hn, fun y hy => ?_⟩
  apply e.injective
  have hy' : e y ∈ N.map e.toMonoidHom := Subgroup.mem_map_of_mem _ hy
  have h := hact (e y) hy'
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  simpa using h

theorem reeF4CompInner_holds : ReeF4CompInner :=
  reeF4CompInner_of_RF rf_holds

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

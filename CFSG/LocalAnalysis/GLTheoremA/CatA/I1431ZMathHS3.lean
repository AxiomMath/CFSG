module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Z

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open Subgroup CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.Co3Cent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.Sporadic.Schreier.Co3


theorem noU42Comp_co3P (k : ↥co3P) (hk : orderOf k = 3) : NoU42Comp 3 k := by
  have hs3 : orderOf (k : Equiv.Perm (Fin 276)) = 3 := by
    rw [← Subgroup.orderOf_coe] at hk
    exact hk
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := exists_conj_classes k.2 hs3
  let H : ↥co3P := ⟨h, hh⟩
  let y : ↥co3P := H⁻¹ * k * H
  have hy : (y : Equiv.Perm (Fin 276)) = c ^ e := by
    show h⁻¹ * (k : Equiv.Perm (Fin 276)) * h = c ^ e
    rw [← hcon]
    group
  have hY : NoU42Comp 3 y := by
    rcases hc with rfl | rfl | rfl
    · obtain ⟨hX3, -, -, hcard, hle, hnorm, hcent⟩ := caseA_spec
      refine noU42Comp_of_pConstrained ?_
      refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
      rw [map_centralizer_subtype', hy, CFSG.Quasithin.Kleidman.centralizer_pow_eq hX3 he]
      exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
        (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent
    · obtain ⟨hX3, -, -, hcard, hle, hnorm, hcent⟩ := caseB_spec
      refine noU42Comp_of_pConstrained ?_
      refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
      rw [map_centralizer_subtype', hy, CFSG.Quasithin.Kleidman.centralizer_pow_eq hX3 he]
      exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
        (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent
    · obtain ⟨⟨hC, hCcard⟩, -⟩ := caseC_spec
      refine noU42Comp_of_not_dvd ?_
      rw [card_centralizer_sub, hy, CFSG.Quasithin.Kleidman.centralizer_pow_eq yPerm_pow he, ← hC,
        hCcard]
      norm_num
  have h' := noU42Comp_conj hY H
  have hk' : H * y * H⁻¹ = k := by
    simp only [y]
    group
  rwa [hk'] at h'

theorem row_co3 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : I1431SporRow .Co3 := by
  have e : NativeSporadic.Carrier .Co3 ≃* ↥co3P := co3PermEquiv
  have hc : Nat.card ↥co3P = 495766656000 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Co3.card_Co3
  haveI : IsSimpleGroup ↥co3P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co3.isSimpleGroup_Co3 e.symm
  exact row_of_model (s := .Co3) (Q := ↥co3P) hOut (e.symm.trans (hbr .Co3).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    noU42Comp_co3P

end CFSG.LocalAnalysis.GLTheoremA.I1431Z

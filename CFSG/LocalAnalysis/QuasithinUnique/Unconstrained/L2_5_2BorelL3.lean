module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin

public section

namespace CFSG.QuasithinUnique.Borel252

open CFSG.Open CFSG.QuasithinUnique.Fin257 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a

namespace L3

variable {F : Type} [Field F]

theorem overgroupData_L3 :
    OvergroupData (projectiveSL 3 F) (projUnitriangular 3 F)
      ((upperTriangular 3 F).map (proj 3 F)) ((Q3 F 0).map (proj 3 F))
      ((Q3 F 1).map (proj 3 F)) :=
  OvergroupData.of_cover (proj_surjective 3 F) (V := unitriangular 3 F)
    (B := upperTriangular 3 F) (Q := Q3 F)
    (by rw [ker_proj]; exact scalars_le_upperTriangular 3 F) covBy_Q3
    (fun A hVA hAt => contained_in_Q3 hVA hAt)
    (by
      rintro _ ⟨b, hb, rfl⟩
      refine mem_normalizer_of_conj _ ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩
        exact ⟨b * u * b⁻¹, LinearFlag.conj_mem_unitriangular hb hu, by simp⟩
      · rintro _ ⟨u, hu, rfl⟩
        refine ⟨b⁻¹ * u * b⁻¹⁻¹, LinearFlag.conj_mem_unitriangular ((upperTriangular 3 F).inv_mem hb) hu, ?_⟩
        simp)

variable [CharP F 2]

theorem borelData_L3 [Finite F] :
    BorelData (projectiveSL 3 F) (projUnitriangular 3 F) Fin257.L3.V1 Fin257.L3.V2 where
  center_trivial := Fin257.L3.center_trivial_M
  sylow := Fin257.L3.isSylowTwoOf_U
  le₁ := Fin257.L3.V1_le_U
  le₂ := Fin257.L3.V2_le_U
  sup := Fin257.L3.U_eq_sup
  cent₁ := Fin257.L3.cent_V1
  cent₂ := Fin257.L3.cent_V2
  lt₁ := Fin257.L3.lt_normalizer_V1
  lt₂ := Fin257.L3.lt_normalizer_V2
  lt_top₁ := Fin257.L3.normalizer_V1_lt_top
  lt_top₂ := Fin257.L3.normalizer_V2_lt_top
  core₁ := Fin257.L3.core_V1
  core₂ := Fin257.L3.core_V2
  only := fun _ h1 h2 =>
    only_of_overgroupData overgroupData_L3 Fin257.L3.lt_normalizer_V1
      Fin257.L3.normalizer_V1_lt_top Fin257.L3.lt_normalizer_V2 Fin257.L3.normalizer_V2_lt_top
      (ne_normalizer_of_sup Fin257.L3.U_eq_sup Fin257.L3.lt_normalizer_V1) h1 h2

end L3

end CFSG.QuasithinUnique.Borel252

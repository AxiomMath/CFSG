module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainPieceTablesSp6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainKinds
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank
open Matrix

local instance f4PilotMainGraphTorusModelNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section SpAut

variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem graphTorus_exists_eq_conj_statedSpMap (δ : MulAut (StatedSp 3 k)) :
    ∃ (s : StatedSp 3 k) (ρ : k ≃+* k), ∀ g, δ g = s * statedSpMap (ρ : k →+* k) 3 g * s⁻¹ := by
  obtain ⟨A, ρ, hA⟩ := (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.automorphism_generation
    (K := k) (r := 3) le_rfl).2 (MulAut.congr (spProjEquiv 3 k) δ)
  obtain ⟨s, hs⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_conjAut_eq_statedSp A
  have hδ : δ =
      MulAut.conj s * CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp 3 k ρ := by
    apply (MulAut.congr (spProjEquiv 3 k)).injective
    rw [hA, hs, map_mul, mulAutCongr_spProjEquiv_conj, mulAutCongr_spProjEquiv_fieldSp]
  refine ⟨s, ρ, fun g => ?_⟩
  rw [hδ, MulAut.mul_apply, MulAut.conj_apply, fieldSp_eq_statedSpMap]

end SpAut

section Congr

variable {F K : Type} [Field F] [Field K]

theorem statedSpCongr_sp6Diag (ε : F ≃+* K) (t : Fin 3 → Fˣ) :
    statedSpCongr ε 3 (sp6Diag F t) = sp6Diag K (fun i => Units.map (ε : F →* K) (t i)) := by
  apply CFSG.LieType.Universal.Symplectic.SpExtras.mat_injective
  rw [mat_sp6Diag]
  change (((statedSpMap (ε : F →+* K) 3 (sp6Diag F t) : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = _
  rw [coe_statedSpMap, coe_map_GL]
  change (CFSG.LieType.Universal.Symplectic.SpExtras.mat 3 F (sp6Diag F t)).map ε = _
  rw [mat_sp6Diag, Matrix.diagonal_map (map_zero ε)]
  congr 1
  funext r
  rcases r with i | i
  · simp [sp6Weight]
  · simp [sp6Weight, map_inv₀]

theorem map_statedSpCongr_sp6Torus (ε : F ≃+* K) {M M' : Type} [Group M] [Group M']
    (φF : M →* (Fin 3 → Fˣ)) (φK : M' →* (Fin 3 → Kˣ)) (u : M →* M')
    (hu : Function.Surjective u) (h : ∀ m i, Units.map (ε : F →* K) (φF m i) = φK (u m) i) :
    ((⊤ : Subgroup M).map ((sp6Diag F).comp φF)).map (statedSpCongr ε 3).toMonoidHom =
      (⊤ : Subgroup M').map ((sp6Diag K).comp φK) := by
  rw [Subgroup.map_map]
  have e1 : (statedSpCongr ε 3).toMonoidHom.comp ((sp6Diag F).comp φF) =
      ((sp6Diag K).comp φK).comp u := by
    ext1 m
    change statedSpCongr ε 3 (sp6Diag F (φF m)) = sp6Diag K (φK (u m))
    rw [statedSpCongr_sp6Diag]
    congr 1
    funext i
    exact h m i
  rw [e1, ← Subgroup.map_map, Subgroup.map_top_of_surjective u hu]

@[expose] noncomputable def graphTorusUnitsMap₂ (ε : F ≃+* K) : Fˣ × Fˣ →* Kˣ × Kˣ :=
  MonoidHom.prodMap (Units.map (ε : F →* K)) (Units.map (ε : F →* K))

theorem graphTorusUnitsMap₂_surjective (ε : F ≃+* K) :
    Function.Surjective (graphTorusUnitsMap₂ ε) := by
  rintro ⟨a, b⟩
  refine ⟨(Units.map (ε.symm : K →* F) a, Units.map (ε.symm : K →* F) b), ?_⟩
  ext <;> simp [graphTorusUnitsMap₂]

theorem units_map_surjective (ε : F ≃+* K) : Function.Surjective (Units.map (ε : F →* K)) := by
  intro a
  refine ⟨Units.map (ε.symm : K →* F) a, ?_⟩
  ext
  simp

theorem map_statedSpCongr_sp6TorusA (ε : F ≃+* K) :
    (sp6TorusA (⊤ : Subgroup Fˣ)).map (statedSpCongr ε 3).toMonoidHom =
      sp6TorusA (⊤ : Subgroup Kˣ) :=
  map_statedSpCongr_sp6Torus ε (sp6ParamA F) (sp6ParamA K) (Units.map (ε : F →* K))
    (units_map_surjective ε) fun m i => by
      rw [sp6ParamA_eq, sp6ParamA_eq]
      by_cases hi : i = 0
      · subst hi
        simp
      · simp [hi]

theorem map_statedSpCongr_sp6TorusM2 (ε : F ≃+* K) :
    (sp6TorusM2 (⊤ : Subgroup Fˣ)).map (statedSpCongr ε 3).toMonoidHom =
      sp6TorusM2 (⊤ : Subgroup Kˣ) := by
  have h := map_statedSpCongr_sp6Torus ε (sp6ParamM2 F) (sp6ParamM2 K) (graphTorusUnitsMap₂ ε)
    (graphTorusUnitsMap₂_surjective ε) fun m i => by
      rw [sp6ParamM2_eq, sp6ParamM2_eq]
      fin_cases i <;> simp [graphTorusUnitsMap₂]
  simp only [sp6TorusM2, Subgroup.top_prod_top]
  exact h

theorem map_statedSpCongr_sp6TorusM3 (ε : F ≃+* K) :
    (sp6TorusM3 (⊤ : Subgroup Fˣ)).map (statedSpCongr ε 3).toMonoidHom =
      sp6TorusM3 (⊤ : Subgroup Kˣ) := by
  have h := map_statedSpCongr_sp6Torus ε (sp6ParamM3 F) (sp6ParamM3 K) (graphTorusUnitsMap₂ ε)
    (graphTorusUnitsMap₂_surjective ε) fun m i => by
      rw [sp6ParamM3_eq, sp6ParamM3_eq]
      fin_cases i <;> simp [graphTorusUnitsMap₂]
  simp only [sp6TorusM3, Subgroup.top_prod_top]
  exact h

end Congr

section Levi


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F]

@[expose] noncomputable def levi6Hom (e : L ≃* adjointGroup .F4 K) (ε : F ≃+* K) :
    StatedSp 3 F →* G :=
  L.subtype.comp (e.symm.toMonoidHom.comp ((C3Levi K).subtype.comp
    ((c3LeviEquiv K).toMonoidHom.comp (statedSpCongr ε 3).toMonoidHom)))

theorem levi6Hom_injective (e : L ≃* adjointGroup .F4 K) (ε : F ≃+* K) :
    Function.Injective (levi6Hom e ε) :=
  L.subtype_injective.comp (e.symm.injective.comp ((C3Levi K).subtype_injective.comp
    ((c3LeviEquiv K).injective.comp (statedSpCongr ε 3).injective)))

theorem map_levi6Hom (e : L ≃* adjointGroup .F4 K) (ε : F ≃+* K) (H : Subgroup (StatedSp 3 F)) :
    H.map (levi6Hom e ε) = ((((H.map (statedSpCongr ε 3).toMonoidHom).map
      (c3LeviEquiv K).toMonoidHom).map (C3Levi K).subtype).map e.symm.toMonoidHom).map
        L.subtype := by
  simp only [levi6Hom, Subgroup.map_map]

theorem range_levi6Hom (e : L ≃* adjointGroup .F4 K) (ε : F ≃+* K) :
    (levi6Hom e ε).range = neighbourLeviG e .X := by
  rw [MonoidHom.range_eq_map, map_levi6Hom,
    Subgroup.map_top_of_surjective (statedSpCongr ε 3).toMonoidHom (statedSpCongr ε 3).surjective,
    Subgroup.map_top_of_surjective (c3LeviEquiv K).toMonoidHom (c3LeviEquiv K).surjective,
    ← MonoidHom.range_eq_map, range_subtype]
  rfl

omit
  [Finite K] [CharP K 2] in
theorem map_inf_C3Levi_eq (e : L ≃* adjointGroup .F4 K) (T : Subgroup (ModGL .F4 K)) :
    ((T.subgroupOf (adjointGroup .F4 K) ⊓ C3Levi K).map e.symm.toMonoidHom).map L.subtype =
      modelToG e T ⊓ neighbourLeviG e .X := by
  rw [Subgroup.map_inf_eq _ _ _ e.symm.injective, Subgroup.map_inf_eq _ _ _ L.subtype_injective]
  rfl

theorem map_levi6Hom_sp6TorusA (e : L ≃* adjointGroup .F4 K) (ε : F ≃+* K) :
    (sp6TorusA (⊤ : Subgroup Fˣ)).map (levi6Hom e ε) =
      leviTorusG e {1, 2} ⊓ neighbourLeviG e .X := by
  rw [map_levi6Hom, map_statedSpCongr_sp6TorusA, map_c3LeviEquiv_sp6TorusA, map_inf_C3Levi_eq]
  rfl

theorem map_levi6Hom_sp6TorusM2 (e : L ≃* adjointGroup .F4 K) (ε : F ≃+* K) :
    (sp6TorusM2 (⊤ : Subgroup Fˣ)).map (levi6Hom e ε) = leviTorusG e {1} ⊓ neighbourLeviG e .X := by
  rw [map_levi6Hom, map_statedSpCongr_sp6TorusM2, map_c3LeviEquiv_sp6TorusM2, map_inf_C3Levi_eq]
  rfl

theorem map_levi6Hom_sp6TorusM3 (e : L ≃* adjointGroup .F4 K) (ε : F ≃+* K) :
    (sp6TorusM3 (⊤ : Subgroup Fˣ)).map (levi6Hom e ε) = leviTorusG e {2} ⊓ neighbourLeviG e .X := by
  rw [map_levi6Hom, map_statedSpCongr_sp6TorusM3, map_c3LeviEquiv_sp6TorusM3, map_inf_C3Levi_eq]
  rfl

end Levi

end CFSG.SeitzReduction.F4Pilot

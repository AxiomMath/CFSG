module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {F : Type} [Field F] [Finite F]

theorem exists_sl2_hom_of_le_map {Γ : Type} [Group Γ] {P : Subgroup Γ}
    (ρ : ↥P →* GL (Fin 2) F) {W : Subgroup Γ}
    (h : (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range ≤
      (W.subgroupOf P).map ρ) :
    ∃ W₁ : Subgroup Γ, W₁ ≤ W ∧
      ∃ φ : ↥W₁ →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective φ := by
  let toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F := SpecialLinearGroup.toGL
  let S : Subgroup ↥P := W.subgroupOf P ⊓ toGL.range.comap ρ
  have hW₁ : S.map P.subtype ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hx.1
  let eS : ↥S ≃* ↥(S.map P.subtype) := S.equivMapOfInjective P.subtype P.subtype_injective
  let f : ↥S →* ↥toGL.range :=
    MonoidHom.codRestrict (ρ.comp S.subtype) toGL.range (fun x => Subgroup.mem_comap.mp x.2.2)
  let eGL : ↥toGL.range ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm
  let φ : ↥(S.map P.subtype) →* Matrix.SpecialLinearGroup (Fin 2) F :=
    (eGL.toMonoidHom.comp f).comp eS.symm.toMonoidHom
  have hφ : Function.Surjective φ := by
    intro s
    obtain ⟨x, hxW, hxρ⟩ := Subgroup.mem_map.mp (h ⟨s, rfl⟩)
    have hxS : x ∈ S := ⟨hxW, Subgroup.mem_comap.mpr ⟨s, hxρ.symm⟩⟩
    have hfx : f ⟨x, hxS⟩ = MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective s := by
      refine Subtype.ext ?_
      rw [MonoidHom.ofInjective_apply]
      simpa [f] using hxρ
    refine ⟨eS ⟨x, hxS⟩, ?_⟩
    show eGL (f (eS.symm (eS ⟨x, hxS⟩))) = s
    rw [MulEquiv.symm_apply_apply, hfx]
    simpa [eGL] using
      MulEquiv.symm_apply_apply (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective) s
  exact ⟨S.map P.subtype, hW₁, φ, hφ⟩

private lemma oddIdxRest_surj_of_le_P1 (hmax : GL2NonsplitMax F) {W : Subgroup (SL3 F)}
    (hWP : W ≤ P1)
    (hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W)
    (hW : ¬ Group.IsSolvable W) :
    ∃ W₁ : Subgroup (SL3 F), W₁ ≤ W ∧
      ∃ φ : ↥W₁ →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective φ := by
  have hNt := le_map_rho1 hNW
  rcases hmax _ hNt with h' | h'
  · exact absurd (isSolvable_of_map_rho1_le hWP h'.le) hW
  · exact exists_sl2_hom_of_le_map rho1 h'

theorem index_cases_SL3_surj (hq : Nat.card F % 3 = 2) (h5 : 5 ≤ Nat.card F)
    (hmax : GL2NonsplitMax F) {W : Subgroup (SL3 F)}
    (hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W)
    (hW : ¬ Group.IsSolvable W) :
    ∃ W₁ : Subgroup (SL3 F), W₁ ≤ W ∧
      ∃ φ : ↥W₁ →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective φ := by
  have hroot := OrdinaryProofs.L3Leaves.sq_add_self_add_one_ne_zero hq
  have hcube := exists_cube hq
  have h3 := three_ne_zero_of_mod hq
  obtain ⟨μ, hμ0, hμ6⟩ := exists_pow_six_ne_one hq h5
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ W :=
    fun X hX => hNW (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  rcases le_P1_or_le_P2_or_transitive hroot hcube hlev with h | h | h
  · exact oddIdxRest_surj_of_le_P1 hmax h hNW hW
  ·
    set e := dualAut (F := F)
    set W' : Subgroup (SL3 F) := W.map e.toMonoidHom
    have hW'P : W' ≤ P1 := by
      rintro _ ⟨g, hg, rfl⟩
      exact dualAut_mem_P1 (h hg)
    have hNW' : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W' := by
      rw [← map_dualAut_normalizer_A0]
      exact Subgroup.map_mono hNW
    have hW' : ¬ Group.IsSolvable W' := by
      intro hs
      apply hW
      set e' := W.equivMapOfInjective e.toMonoidHom e.injective
      exact Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
    obtain ⟨W₁', hW₁'W', φ', hφ'⟩ := oddIdxRest_surj_of_le_P1 hmax hW'P hNW' hW'
    refine ⟨W₁'.map e.symm.toMonoidHom, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp (hW₁'W' hy)
      rw [← hw']
      simpa using hw
    · let ee : ↥W₁' ≃* ↥(W₁'.map e.symm.toMonoidHom) :=
        W₁'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
      exact ⟨φ'.comp ee.symm.toMonoidHom, hφ'.comp ee.symm.surjective⟩
  ·
    have hNtY : (Nt : Subgroup (GL (Fin 2) F)) ≤ ((W ⊓ P1).subgroupOf P1).map rho1 := by
      intro X hX
      exact ⟨⟨lev X, lev_mem_P1 X⟩,
        Subgroup.mem_subgroupOf.mpr ⟨hNW (lev_mem_normalizer_A0 hX), lev_mem_P1 X⟩, rho1_lev X⟩
    rcases hmax _ hNtY with h' | h'
    · exact (false_of_map_rho1_le_Nt hroot hμ0 hμ6 hlev h h'.le).elim
    · obtain ⟨W₁, hW₁, φ, hφ⟩ := exists_sl2_hom_of_le_map (W := W ⊓ P1) rho1 h'
      exact ⟨W₁, hW₁.trans inf_le_left, φ, hφ⟩

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

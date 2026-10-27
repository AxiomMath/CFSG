module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6RootSL2
public import CFSG.Timmesfeld.RankTwo.SLThreeGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


private theorem subtype_comp_tv_eq {F : Type} [Field F]
    {i j : Fin TwistTag.E6.tag.rank}
    (emb : Matrix.SpecialLinearGroup (Fin 3) F →* ↥(adjointGroup TwistTag.E6.tag F))
    (h01 : ∀ c : F, emb (CFSG.Timmesfeld.tv 0 1 c) =
      CFSG.LieType.Steinberg.Adjoint.xPar
        (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) (CFSG.Timmesfeld.sroot i) c)
    (h10 : ∀ c : F, emb (CFSG.Timmesfeld.tv 1 0 c) =
      CFSG.LieType.Steinberg.Adjoint.xPar
        (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) (-CFSG.Timmesfeld.sroot i) c)
    (h12 : ∀ c : F, emb (CFSG.Timmesfeld.tv 1 2 c) =
      CFSG.LieType.Steinberg.Adjoint.xPar
        (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) (CFSG.Timmesfeld.sroot j) c)
    (h21 : ∀ c : F, emb (CFSG.Timmesfeld.tv 2 1 c) =
      CFSG.LieType.Steinberg.Adjoint.xPar
        (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) (-CFSG.Timmesfeld.sroot j) c) :
    ∀ c : F, ((adjointGroup TwistTag.E6.tag F).subtype.comp emb)
        (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F i c ∧
      ((adjointGroup TwistTag.E6.tag F).subtype.comp emb) (CFSG.Timmesfeld.tv 1 0 c) =
        yUnit TwistTag.E6.tag F i c ∧
      ((adjointGroup TwistTag.E6.tag F).subtype.comp emb) (CFSG.Timmesfeld.tv 1 2 c) =
        xUnit TwistTag.E6.tag F j c ∧
      ((adjointGroup TwistTag.E6.tag F).subtype.comp emb) (CFSG.Timmesfeld.tv 2 1 c) =
        yUnit TwistTag.E6.tag F j c := by
  intro c
  have e01 : ((adjointGroup TwistTag.E6.tag F).subtype.comp emb)
      (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F i c := by
    rw [MonoidHom.comp_apply, h01 c]
    exact (CFSG.ComponentClassification.CatLeafProof.coe_xPar_e6 F i c).1
  have e10 : ((adjointGroup TwistTag.E6.tag F).subtype.comp emb)
      (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F i c := by
    rw [MonoidHom.comp_apply, h10 c]
    exact (CFSG.ComponentClassification.CatLeafProof.coe_xPar_e6 F i c).2
  have e12 : ((adjointGroup TwistTag.E6.tag F).subtype.comp emb)
      (CFSG.Timmesfeld.tv 1 2 c) = xUnit TwistTag.E6.tag F j c := by
    rw [MonoidHom.comp_apply, h12 c]
    exact (CFSG.ComponentClassification.CatLeafProof.coe_xPar_e6 F j c).1
  have e21 : ((adjointGroup TwistTag.E6.tag F).subtype.comp emb)
      (CFSG.Timmesfeld.tv 2 1 c) = yUnit TwistTag.E6.tag F j c := by
    rw [MonoidHom.comp_apply, h21 c]
    exact (CFSG.ComponentClassification.CatLeafProof.coe_xPar_e6 F j c).2
  exact ⟨e01, e10, e12, e21⟩

private theorem range_eq_subsystemGroup_of_tv {F : Type} [Field F]
    {i j : Fin TwistTag.E6.tag.rank}
    (ι : Matrix.SpecialLinearGroup (Fin 3) F →* ModGL TwistTag.E6.tag F)
    (hval : ∀ c : F, ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 2 c) = xUnit TwistTag.E6.tag F j c ∧
      ι (CFSG.Timmesfeld.tv 2 1 c) = yUnit TwistTag.E6.tag F j c) :
    ι.range = subsystemGroup TwistTag.E6.tag F ({i, j} : Set (Fin TwistTag.E6.tag.rank)) := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← CFSG.Timmesfeld.closure_tv_three, MonoidHom.map_closure,
      subsystemGroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨h, hh, rfl⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hh
    rcases hh with hh | hh
    · rcases hh with hh | hh
      · rcases hh with hh | hh
        · obtain ⟨c, rfl⟩ := hh
          rw [(hval c).1]
          exact Subgroup.subset_closure ⟨i, by simp, c, Or.inl rfl⟩
        · obtain ⟨c, rfl⟩ := hh
          rw [(hval c).2.1]
          exact Subgroup.subset_closure ⟨i, by simp, c, Or.inr rfl⟩
      · obtain ⟨c, rfl⟩ := hh
        rw [(hval c).2.2.1]
        exact Subgroup.subset_closure ⟨j, by simp, c, Or.inl rfl⟩
    · obtain ⟨c, rfl⟩ := hh
      rw [(hval c).2.2.2]
      exact Subgroup.subset_closure ⟨j, by simp, c, Or.inr rfl⟩
  · rw [subsystemGroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨k, hk, c, rfl | rfl⟩
    · rcases (by simpa using hk : k = i ∨ k = j) with rfl | rfl
      · exact ⟨CFSG.Timmesfeld.tv 0 1 c, (hval c).1⟩
      · exact ⟨CFSG.Timmesfeld.tv 1 2 c, (hval c).2.2.1⟩
    · rcases (by simpa using hk : k = i ∨ k = j) with rfl | rfl
      · exact ⟨CFSG.Timmesfeld.tv 1 0 c, (hval c).2.1⟩
      · exact ⟨CFSG.Timmesfeld.tv 2 1 c, (hval c).2.2.2⟩

theorem exists_sl3_e6pair {F : Type} [Field F] [Finite F]
    {i j : Fin TwistTag.E6.tag.rank} (hij : i ≠ j)
    (hcij : Tag.cartan .E6 i j = -1) (hcji : Tag.cartan .E6 j i = -1)
    (hk : ∃ k : Fin TwistTag.E6.tag.rank,
      ¬ (3 : ℤ) ∣ Tag.cartan .E6 i k + 2 * Tag.cartan .E6 j k) :
    ∃ ι : Matrix.SpecialLinearGroup (Fin 3) F →* ModGL TwistTag.E6.tag F,
      Function.Injective ι ∧
      ι.range = subsystemGroup TwistTag.E6.tag F ({i, j} : Set (Fin TwistTag.E6.tag.rank)) ∧
      ∀ c : F, ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F i c ∧
        ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F i c ∧
        ι (CFSG.Timmesfeld.tv 1 2 c) = xUnit TwistTag.E6.tag F j c ∧
        ι (CFSG.Timmesfeld.tv 2 1 c) = yUnit TwistTag.E6.tag F j c := by
  obtain ⟨O, C, hEx⟩ :=
    CFSG.ComponentClassification.CatLeafProof.exists_e6_chevalleyExtras F
  let D := CFSG.LieType.Steinberg.Adjoint.adjDatum
    (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6) F
  let i' : Fin D.rank := i
  let j' : Fin D.rank := j
  have hcij' : D.cartan i' j' = -1 := hcij
  have hcji' : D.cartan j' i' = -1 := hcji
  obtain ⟨k, hk⟩ := hk
  let k' : Fin D.rank := k
  have hk' : ¬ (3 : ℤ) ∣ D.cartan i' k' + 2 * D.cartan j' k' := hk
  obtain ⟨emb, hinj, -, hvals⟩ :=
    CFSG.ClassicalInvolution.WeakCT.exists_sl3Levi
      (D := D) (x := CFSG.LieType.Steinberg.Adjoint.xPar
        (CFSG.LieType.Chevalley.rootOperatorFamily Tag.E6))
      hEx rfl (show i' ≠ j' from hij) hcij' hcji' hk'
  let ι : Matrix.SpecialLinearGroup (Fin 3) F →* ModGL TwistTag.E6.tag F :=
    (adjointGroup TwistTag.E6.tag F).subtype.comp emb
  have hval : ∀ c : F, ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F i c ∧
      ι (CFSG.Timmesfeld.tv 1 2 c) = xUnit TwistTag.E6.tag F j c ∧
      ι (CFSG.Timmesfeld.tv 2 1 c) = yUnit TwistTag.E6.tag F j c :=
    subtype_comp_tv_eq (i := i) (j := j) emb (fun c => (hvals c).1)
      (fun c => (hvals c).2.1) (fun c => (hvals c).2.2.1) (fun c => (hvals c).2.2.2)
  refine ⟨ι, ?_, range_eq_subsystemGroup_of_tv ι hval, hval⟩
  intro a b hab
  exact hinj ((adjointGroup TwistTag.E6.tag F).subtype_injective hab)

theorem simpleRootSL2_tv {F : Type} [Field F] (k : Fin TwistTag.E6.tag.rank) (c : F) :
    simpleRootSL2 TwistTag.E6.tag F k (CFSG.Timmesfeld.tv 0 1 c) =
        xUnit TwistTag.E6.tag F k c ∧
      simpleRootSL2 TwistTag.E6.tag F k (CFSG.Timmesfeld.tv 1 0 c) =
        yUnit TwistTag.E6.tag F k c := by
  have h01 : (CFSG.Timmesfeld.tv (n := 2) 0 1 c) = CFSG.LieType.Chevalley.uSL c := by
    apply Subtype.ext
    rw [CFSG.Timmesfeld.tv_of_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.SpecialLinearGroup.transvection_coe, CFSG.LieType.Chevalley.coe_uSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]
  have h10 : (CFSG.Timmesfeld.tv (n := 2) 1 0 c) = CFSG.LieType.Chevalley.vSL c := by
    apply Subtype.ext
    rw [CFSG.Timmesfeld.tv_of_ne (show (1 : Fin 2) ≠ 0 by decide),
      Matrix.SpecialLinearGroup.transvection_coe, CFSG.LieType.Chevalley.coe_vSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]
  refine ⟨?_, ?_⟩
  · rw [h01]
    exact CFSG.LieType.Chevalley.simpleRootSL2_uSL k c
  · rw [h10]
    exact CFSG.LieType.Chevalley.simpleRootSL2_vSL k c

theorem range_simpleRootSL2_eq_subsystemGroup {F : Type} [Field F]
    (k : Fin TwistTag.E6.tag.rank) :
    (simpleRootSL2 TwistTag.E6.tag F k).range =
      subsystemGroup TwistTag.E6.tag F ({k} : Set (Fin TwistTag.E6.tag.rank)) := by
  rw [CFSG.LieType.Chevalley.range_simpleRootSL2, subsystemGroup]
  congr 1
  ext g
  constructor
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨k, by simp, c, Or.inl rfl⟩
    · exact ⟨k, by simp, c, Or.inr rfl⟩
  · rintro ⟨l, hl, c, rfl | rfl⟩
    · rw [Set.mem_singleton_iff] at hl
      subst hl
      exact Or.inl ⟨c, rfl⟩
    · rw [Set.mem_singleton_iff] at hl
      subst hl
      exact Or.inr ⟨c, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace

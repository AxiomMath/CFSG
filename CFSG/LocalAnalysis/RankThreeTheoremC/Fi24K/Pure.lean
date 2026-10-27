module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Mixed
import all CFSG.Sporadic.Bridge.Common
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

open CFSG.Sporadic.Fi24 CFSG.HardMathSupport.Dickson.I271.Fi7 Subgroup
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

theorem nonempty_mulEquiv_closure_he_of_relators
    {G : Type*} [Group G] {x y : G}
    (hxne : x ≠ 1)
    (hrel : ∀ v ∈ TauCeti.Sporadic.hePresentation.relatorLetters, wordProd (img2 x y) v = 1) :
    Nonempty (↥(Subgroup.closure ({x, y} : Set G)) ≃*
      (TauCeti.CFSGIndex.sporadic .He).Group) := by
  classical
  have hsimple : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .He).Group := by
    obtain ⟨e⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
    exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm
  set P := TauCeti.Sporadic.hePresentation with hP
  haveI : IsSimpleGroup P.Group := hsimple
  set φ : P.Group →* G := presHom P (img2 x y) hrel with hφ
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      have h0 : presGen P 0 ∈ φ.ker := by
        rw [h]
        exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at h0
      have hx0 : φ (presGen P 0) = x := by
        rw [presHom_presGen P _ hrel (i := 0)
          (by rw [hP, CFSG.Sporadic.Bridge.He.generatorCount_eq]; norm_num)]
        simp [img2]
      rw [hx0] at h0
      exact hxne h0
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  have hgen : Subgroup.closure (Set.range (PresentedGroup.of :
      Fin P.generatorCount → P.Group)) = ⊤ :=
    PresentedGroup.closure_range_of P.relatorSet
  have hof : ∀ i : Fin P.generatorCount, φ (PresentedGroup.of i) = img2 x y i.val := by
    intro i
    have h := presHom_presGen P (img2 x y) hrel i.isLt
    rw [presGen, dif_pos i.isLt] at h
    exact h
  have hrange : φ.range ≤ Subgroup.closure ({x, y} : Set G) := by
    rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure]
    apply (Subgroup.closure_le _).2
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨k, rfl⟩ := hi
    rw [hof k]
    rcases eq_or_ne k.val 0 with h0 | h0
    · rw [show img2 x y k.val = x by simp [img2, h0]]
      exact Subgroup.subset_closure (by simp)
    · rw [show img2 x y k.val = y by simp [img2, h0]]
      exact Subgroup.subset_closure (by simp)
  have hHle : Subgroup.closure ({x, y} : Set G) ≤ φ.range := by
    apply (Subgroup.closure_le _).2
    rintro _ (rfl | rfl)
    · refine ⟨presGen P 0, ?_⟩
      rw [presHom_presGen P _ hrel (i := 0)
        (by rw [hP, CFSG.Sporadic.Bridge.He.generatorCount_eq]; norm_num)]
      simp [img2]
    · refine ⟨presGen P 1, ?_⟩
      rw [presHom_presGen P _ hrel (i := 1)
        (by rw [hP, CFSG.Sporadic.Bridge.He.generatorCount_eq]; norm_num)]
      simp [img2]
  have heq : Subgroup.closure ({x, y} : Set G) = φ.range := le_antisymm hHle hrange
  exact ⟨(MulEquiv.subgroupCongr heq).trans (MonoidHom.ofInjective hinj).symm⟩

theorem sK_mem_closure_pureGens {lam : ℕ} (h1 : 1 ≤ lam) (h6 : lam ≤ 6) {k : ℕ}
    (hk : k ∈ pureGens lam) :
    sK k ∈ Subgroup.closure ((normalizer ((zpowers C7 : Subgroup J) : Set J) : Set J) ∪
      (centralizer ({X7 * Y7 ^ lam} : Set J) : Set J)) := by
  have hZ : ∀ g : J, g * (X7 * Y7 ^ lam) = (X7 * Y7 ^ lam) * g →
      g ∈ Subgroup.closure ((normalizer ((zpowers C7 : Subgroup J) : Set J) : Set J) ∪
        (centralizer ({X7 * Y7 ^ lam} : Set J) : Set J)) := fun g hg =>
    Subgroup.subset_closure (Or.inr (Subgroup.mem_centralizer_singleton_iff.2 hg))
  have hm : (sK (1088 + lam))⁻¹ * C7 * sK (1088 + lam) = X7 * Y7 ^ lam := by
    calc (sK (1088 + lam))⁻¹ * C7 * sK (1088 + lam)
        = (sK (1088 + lam))⁻¹ * (C7 * sK (1088 + lam)) := by group
      _ = (sK (1088 + lam))⁻¹ * (sK (1088 + lam) * (X7 * Y7 ^ lam)) := by
          rw [← sK_conjLine_conj h1 h6]
      _ = X7 * Y7 ^ lam := by group
  have hconj : ∀ M g : J, g * C7 = C7 * g →
      (M⁻¹ * g * M) * (M⁻¹ * C7 * M) = (M⁻¹ * C7 * M) * (M⁻¹ * g * M) := by
    intro M g hg
    calc (M⁻¹ * g * M) * (M⁻¹ * C7 * M) = M⁻¹ * (g * C7) * M := by group
      _ = M⁻¹ * (C7 * g) * M := by rw [hg]
      _ = (M⁻¹ * C7 * M) * (M⁻¹ * g * M) := by group
  simp only [pureGens, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 5 exact Subgroup.subset_closure (Or.inl (sK_common_mem_normalizer (by decide)))
  · rw [sK_cent85 h1 h6]
    refine hZ _ ?_
    rw [← hm]
    exact hconj _ _ sK_1085_comm
  · rw [sK_cent86 h1 h6]
    refine hZ _ ?_
    rw [← hm]
    exact hconj _ _ sK_1086_comm

theorem image_pureGens_subset {lam : ℕ} (h1 : 1 ≤ lam) (h6 : lam ≤ 6) :
    sK '' {k : ℕ | k ∈ pureGens lam} ⊆
      Subgroup.closure ((normalizer ((zpowers C7 : Subgroup J) : Set J) : Set J) ∪
        (centralizer ({X7 * Y7 ^ lam} : Set J) : Set J)) := by
  rintro _ ⟨k, hk, rfl⟩
  exact sK_mem_closure_pureGens h1 h6 hk


theorem exists_he_of_mem_pureSecs (q : PureSec) (hq : q ∈ pureSecs) :
    ∃ H : Subgroup J,
      H ≤ Subgroup.closure ((normalizer ((zpowers C7 : Subgroup J) : Set J) : Set J) ∪
        (centralizer ({X7 * Y7 ^ q.lam} : Set J) : Set J)) ∧
      Nonempty (H ≃* (TauCeti.CFSGIndex.sporadic .He).Group) ∧ Q7 ≤ H ∧
      ∃ h ∈ H, h * (X7 * Y7 ^ q.lam) * h⁻¹ = C7 := by
  have hq' := hq
  simp only [pureSecs, List.mem_cons, List.not_mem_nil, or_false] at hq'
  have h1 : 1 ≤ q.lam := by rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have h6 : q.lam ≤ 6 := by rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  obtain ⟨hxi, hyi, hrels, hxne, hX, hY, hoh, hohl⟩ := pure_facts q hq
  set S : Subgroup J := Subgroup.closure
    ((normalizer ((zpowers C7 : Subgroup J) : Set J) : Set J) ∪
      (centralizer ({X7 * Y7 ^ q.lam} : Set J) : Set J)) with hS
  have hsub : Subgroup.closure (sK '' {k : ℕ | k ∈ pureGens q.lam}) ≤ S :=
    (Subgroup.closure_le _).2 (image_pureGens_subset h1 h6)
  have hH : Subgroup.closure ({sK q.ix, sK q.iy} : Set J) ≤ S := by
    apply (Subgroup.closure_le _).2
    rintro _ (rfl | rfl)
    exacts [hsub hxi, hsub hyi]
  have hQ : Q7 ≤ Subgroup.closure ({sK q.ix, sK q.iy} : Set J) := by
    apply (Subgroup.closure_le _).2
    rintro _ (rfl | rfl)
    exacts [hX, hY]
  refine ⟨Subgroup.closure ({sK q.ix, sK q.iy} : Set J), hH, ?_, hQ, sK q.oh, hoh, ?_⟩
  · exact nonempty_mulEquiv_closure_he_of_relators hxne hrels
  · calc sK q.oh * (X7 * Y7 ^ q.lam) * (sK q.oh)⁻¹
        = (sK q.oh * (X7 * Y7 ^ q.lam)) * (sK q.oh)⁻¹ := by group
      _ = (C7 * sK q.oh) * (sK q.oh)⁻¹ := by rw [hohl]
      _ = C7 := by group

theorem exists_he_le_closure {lam : ℕ} (h1 : 1 ≤ lam) (h6 : lam ≤ 6) :
    ∃ H : Subgroup J,
      H ≤ Subgroup.closure ((normalizer ((zpowers C7 : Subgroup J) : Set J) : Set J) ∪
        (centralizer ({X7 * Y7 ^ lam} : Set J) : Set J)) ∧
      Nonempty (H ≃* (TauCeti.CFSGIndex.sporadic .He).Group) ∧ Q7 ≤ H ∧
      ∃ h ∈ H, h * (X7 * Y7 ^ lam) * h⁻¹ = C7 := by
  obtain ⟨q, hq, hql⟩ : ∃ q ∈ pureSecs, q.lam = lam := by
    interval_cases lam
    · exact ⟨⟨1, 2208, 2216, 2211, 2215, 2543, 2540, 2541, 2542⟩, by simp [pureSecs], rfl⟩
    · exact ⟨⟨2, 2543, 2551, 2546, 2550, 2809, 2806, 2807, 2808⟩, by simp [pureSecs], rfl⟩
    · exact ⟨⟨3, 2809, 2817, 2812, 2816, 3081, 3078, 3079, 3080⟩, by simp [pureSecs], rfl⟩
    · exact ⟨⟨4, 3081, 3089, 3084, 3088, 3321, 3318, 3319, 3320⟩, by simp [pureSecs], rfl⟩
    · exact ⟨⟨5, 3321, 3329, 3324, 3328, 3576, 3573, 3574, 3575⟩, by simp [pureSecs], rfl⟩
    · exact ⟨⟨6, 3576, 3584, 3579, 3583, 3820, 3817, 3818, 3819⟩, by simp [pureSecs], rfl⟩
  rw [← hql]
  exact exists_he_of_mem_pureSecs q hq

end CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

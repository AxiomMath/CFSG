module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.RootSpanPerp
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.WeylFixesS1
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.LeviNormalForm
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Opposite

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false



theorem single_mem_S2set {j : Fin Tag.F4.rank} (hj : j.val = 2 ∨ j.val = 3) :
    (Pi.single j 1 : Fin Tag.F4.rank → ℤ) ∈ S2set ∧ (-Pi.single j 1 : Fin Tag.F4.rank → ℤ) ∈ S2set := by
  show _ ∈ f4ShortList ∧ _ ∈ f4ShortList
  rcases hj with hj | hj
  · have : j = ⟨2, by decide⟩ := Fin.ext hj
    subst this
    decide +kernel
  · have : j = ⟨3, by decide⟩ := Fin.ext hj
    subst this
    decide +kernel

theorem parabolicLevi_J2_le (K : Type) [Field K] :
    parabolicLevi Tag.F4 K {i : Fin Tag.F4.rank | i.val = 2 ∨ i.val = 3} ≤
      torusGroup Tag.F4 K ⊔ X2 K := by
  refine sup_le_sup_left ((Subgroup.closure_le _).2 ?_) _
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan (single_mem_S2set hj).1 c
  · rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan (single_mem_S2set hj).2 c

theorem w₁_smul_theta : w₁ • theta = alpha1 := by
  rw [w₁, wordProd_smul_eq_foldr, leviWord_theta]

theorem w₁_smul_neg_theta : w₁ • (-theta) = -alpha1 := by
  rw [smul_neg, w₁_smul_theta]

theorem isRoot_theta : IsRoot Tag.F4 theta := mem_rootFinset.1 theta_mem

theorem mem_parabolicPosRoots_F4 {β : Fin Tag.F4.rank → ℤ} :
    β ∈ parabolicPosRoots Tag.F4 (Heis.Jθ Tag.F4) ↔
      IsRoot Tag.F4 β ∧ β 0 = 0 ∧ 0 < height β := by
  unfold parabolicPosRoots parabolicRoots Heis.Jθ
  constructor
  · rintro ⟨⟨hr, h0⟩, -, hp⟩
    exact ⟨hr, h0 (Heis.iθ Tag.F4) (by simp), hp⟩
  · rintro ⟨hr, h0, hp⟩
    refine ⟨⟨hr, fun i hi => ?_⟩, hr, hp⟩
    have : i = Heis.iθ Tag.F4 := by simpa using hi
    subst this
    exact h0

theorem w₁_min : ∀ β ∈ parabolicPosRoots Tag.F4 (Heis.Jθ Tag.F4), 0 < height (w₁ • β) := by
  intro β hβ
  obtain ⟨hr, h0, hp⟩ := mem_parabolicPosRoots_F4.1 hβ
  rw [w₁, wordProd_smul_eq_foldr]
  exact leviWord_min β (mem_rootFinset.2 hr) h0 hp

theorem mem_perp_inter {β : Fin Tag.F4.rank → ℤ}
    (hA : β ∈ parabolicPosRoots Tag.F4 (Heis.Jθ Tag.F4))
    (hB : β ∈ (fun β => w₁ • β) '' parabolicPosRoots Tag.F4 (Heis.Jθ Tag.F4)) :
    β ∈ S2set ∧ 0 < height β := by
  obtain ⟨hr, h0, hp⟩ := mem_parabolicPosRoots_F4.1 hA
  obtain ⟨β', hβ', rfl⟩ := hB
  obtain ⟨hr', h0', hp'⟩ := mem_parabolicPosRoots_F4.1 hβ'
  have hrev : (coxeterSystem Tag.F4).wordProd leviWord.reverse • (w₁ • β') =
      leviWord.reverse.foldr (reflect .F4) (w₁ • β') := wordProd_smul_eq_foldr _ _ _
  have hinv : (coxeterSystem Tag.F4).wordProd leviWord.reverse • (w₁ • β') = β' := by
    rw [w₁, ← mul_smul, CoxeterSystem.wordProd_reverse, inv_mul_cancel, one_smul]
  rw [hinv] at hrev
  have := perp_inter_F4 (w₁ • β') (mem_rootFinset.2 hr) ⟨h0, hp⟩ (by rw [← hrev]; exact ⟨h0', hp'⟩)
  exact this

theorem rootSpan_mono_aux {A B : Set (Fin Tag.F4.rank → ℤ)} (h : A ⊆ B) (K : Type) [Field K] :
    rootSpan Tag.F4 K A ≤ rootSpan Tag.F4 K B :=
  iSup₂_le fun α hα => le_iSup₂_of_le α (h hα) le_rfl

theorem rootSubgroup_le_rootSpan_aux {S : Set (Fin Tag.F4.rank → ℤ)} {α : Fin Tag.F4.rank → ℤ}
    (h : α ∈ S) (K : Type) [Field K] : rootSubgroup Tag.F4 K α ≤ rootSpan Tag.F4 K S :=
  le_iSup₂_of_le α h le_rfl

theorem f4LongList_cases : ∀ α ∈ f4LongList, α = alpha1 ∨ α = -alpha1 ∨ α = theta - alpha1 ∨
    α = -(theta - alpha1) ∨ α = theta ∨ α = -theta := by decide +kernel

theorem smul_eq_of_fixes_theta_alpha1 {w : WeylGroup Tag.F4} (h1 : w • theta = theta)
    (h2 : w • alpha1 = alpha1) : ∀ α ∈ f4LongList, w • α = α := by
  intro α hα
  rcases f4LongList_cases α hα with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h2
  · rw [smul_neg, h2]
  · rw [smul_sub, h1, h2]
  · rw [smul_neg, smul_sub, h1, h2]
  · exact h1
  · rw [smul_neg, h1]

theorem centralizer_X1_le (K : Type) [Field K] {g : ModGL Tag.F4 K}
    (hg : g ∈ adjointGroup Tag.F4 K) (hc : ∀ x ∈ X1 K, g * x = x * g) :
    g ∈ torusGroup Tag.F4 K ⊔ X2 K := by
  classical
  have hUθ : Heis.Uθ Tag.F4 K ≤ X1 K := rootSubgroup_le_rootSpan_aux theta_mem_S1set K
  have hUneg : Heis.Uneg Tag.F4 K ≤ X1 K := rootSubgroup_le_rootSpan_aux neg_theta_mem_S1set K
  have hL1 : g ∈ Heis.Lθ Tag.F4 K :=
    Heis.centralizer_Uθ_inf_centralizer_Uneg_le_Lθ Tag.F4 K hg
      (fun x hx => hc x (hUθ hx)) (fun x hx => hc x (hUneg hx))
  set n : ModGL Tag.F4 K := canonicalRep (coxeterSystem Tag.F4) K w₁ with hn
  have hnG : n ∈ adjointGroup Tag.F4 K := canonicalRep_mem_adjointGroup _ K w₁
  have hmapθ : Heis.conjSub n (Heis.Uθ Tag.F4 K) = rootSubgroup Tag.F4 K alpha1 := by
    have := CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := K) w₁ isRoot_theta
    rw [w₁_smul_theta] at this
    exact this
  have hmapneg : Heis.conjSub n (Heis.Uneg Tag.F4 K) = rootSubgroup Tag.F4 K (-alpha1) := by
    have := CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := K) w₁
      (Heis.isRoot_neg_highRoot Tag.F4)
    exact this.trans (by rw [show -highRoot Tag.F4 = -theta from rfl, w₁_smul_neg_theta])
  have hconj : ∀ A : Subgroup (ModGL Tag.F4 K), Heis.conjSub n A ≤ X1 K →
      ∀ x ∈ A, (n⁻¹ * g * n) * x = x * (n⁻¹ * g * n) := by
    intro A hA x hx
    have hx' : n * x * n⁻¹ ∈ Heis.conjSub n A := Heis.mem_conjSub_iff.2 (by
      rw [show n⁻¹ * (n * x * n⁻¹) * n = x by group]; exact hx)
    have e := hc _ (hA hx')
    calc n⁻¹ * g * n * x = n⁻¹ * (g * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * x * n⁻¹) * g) * n := by rw [e]
      _ = x * (n⁻¹ * g * n) := by group
  have hL2 : n⁻¹ * g * n ∈ Heis.Lθ Tag.F4 K :=
    Heis.centralizer_Uθ_inf_centralizer_Uneg_le_Lθ Tag.F4 K
      (mul_mem (mul_mem (inv_mem hnG) hg) hnG)
      (hconj _ (hmapθ ▸ rootSubgroup_le_rootSpan_aux alpha1_mem_S1set K))
      (hconj _ (hmapneg ▸ rootSubgroup_le_rootSpan_aux neg_alpha1_mem_S1set K))
  have hL2' : g ∈ Heis.conjSub n (Heis.Lθ Tag.F4 K) := Heis.mem_conjSub_iff.2 hL2
  have hmin1 : ∀ β ∈ parabolicPosRoots Tag.F4 (Heis.Jθ Tag.F4),
      0 < height ((1 : WeylGroup Tag.F4) • β) := by
    intro β hβ
    rw [one_smul]
    exact (mem_parabolicPosRoots_F4.1 hβ).2.2
  obtain ⟨wa, ha, ua, va, hha, hua, hva, hwa, hga⟩ :=
    Heis.normalForm_conj_Lθ Tag.F4 K (w₀ := 1) hmin1 (g := g)
      (by rw [canonicalRep_one, Heis.conjSub_one]; exact hL1)
  obtain ⟨wb, hb, ub, vb, hhb, hub, hvb, hwb, hgb⟩ :=
    Heis.normalForm_conj_Lθ Tag.F4 K (w₀ := w₁) w₁_min hL2'
  set A := parabolicPosRoots Tag.F4 (Heis.Jθ Tag.F4) with hA
  set B := (fun β => w₁ • β) '' A with hB
  have himg1 : (fun β => (1 : WeylGroup Tag.F4) • β) '' A = A := by
    ext x
    simp
  rw [himg1] at hua hva
  have hposA : ∀ α ∈ A, IsRoot Tag.F4 α ∧ 0 < height α := fun α hα =>
    ⟨(mem_parabolicPosRoots_F4.1 hα).1, (mem_parabolicPosRoots_F4.1 hα).2.2⟩
  have hposB : ∀ α ∈ B, IsRoot Tag.F4 α ∧ 0 < height α := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨IsRoot.smul (mem_parabolicPosRoots_F4.1 hβ).1 _, w₁_min β hβ⟩
  have huaU : ua ∈ posUnipotent Tag.F4 K := rootSpan_le_posUnipotent hposA hua
  have hubU : ub ∈ posUnipotent Tag.F4 K := rootSpan_le_posUnipotent hposB hub
  have hvaI : va ∈ rootSpan Tag.F4 K (inversionSet wa) :=
    rootSpan_mono_aux Set.inter_subset_right K hva
  have hvbI : vb ∈ rootSpan Tag.F4 K (inversionSet wb) :=
    rootSpan_mono_aux Set.inter_subset_right K hvb
  obtain ⟨hw, -, hu, hv⟩ := CFSG.HardMathSupport.Timmesfeld.Torality.bruhat_factor_unique Tag.F4 K wa wb ha hb ua ub va vb hha hhb huaU hubU
    hvaI hvbI (hga.symm.trans hgb)
  have hS2 : rootSpan Tag.F4 K (A ∩ B) ≤ X2 K := by
    refine rootSpan_mono_aux (fun β hβ => (mem_perp_inter hβ.1 hβ.2).1) K
  have huX2 : ua ∈ X2 K := hS2 (rootSpan_inf_perp_F4 K ⟨hua, hu ▸ hub⟩)
  have hvX2 : va ∈ X2 K := hS2 (rootSpan_inf_perp_F4 K
    ⟨rootSpan_mono_aux Set.inter_subset_left K hva,
      hv ▸ rootSpan_mono_aux Set.inter_subset_left K hvb⟩)
  have h1 : wa • theta = theta := by
    have := hwa
    simp only [one_smul] at this
    exact this
  have h2 : wa • alpha1 = alpha1 := by
    have := hwb
    rw [← hw, show highRoot Tag.F4 = theta from rfl, w₁_smul_theta] at this
    exact this
  have hJ2 := weyl_fixes_S1_F4 (smul_eq_of_fixes_theta_alpha1 h1 h2)
  have hnw : canonicalRep (coxeterSystem Tag.F4) K wa ∈ torusGroup Tag.F4 K ⊔ X2 K :=
    parabolicLevi_J2_le K (canonicalRep_mem_parabolicLevi hJ2)
  rw [hga]
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left hha) (Subgroup.mem_sup_right huX2)) hnw)
    (Subgroup.mem_sup_right hvX2)

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

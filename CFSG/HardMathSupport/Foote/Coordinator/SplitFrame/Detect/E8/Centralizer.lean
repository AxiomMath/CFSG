module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.CentralizerData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.WeylFixes
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Transport
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.LeviCompare
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.RootSpanInter

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


theorem parabolicLevi_J2_le (K : Type) [Field K] :
    parabolicLevi Tag.E8 K {i : Fin Tag.E8.rank | i.val < 4} ≤ torusGroup Tag.E8 K ⊔ X2 K := by
  refine sup_le_sup_left ((Subgroup.closure_le _).2 ?_) _
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan (S := S2set) (single_mem_S2set j hj).1 c
  · rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan (S := S2set) (single_mem_S2set j hj).2 c

theorem isRoot_theta : IsRoot Tag.E8 theta := mem_rootFinset.1 theta_mem

theorem mem_parabolicPosRoots_E8 {β : Fin Tag.E8.rank → ℤ} :
    β ∈ parabolicPosRoots Tag.E8 (Heis.Jθ Tag.E8) ↔
      IsRoot Tag.E8 β ∧ β 7 = 0 ∧ 0 < height β := by
  unfold parabolicPosRoots parabolicRoots Heis.Jθ
  constructor
  · rintro ⟨⟨hr, h0⟩, -, hp⟩
    exact ⟨hr, h0 (Heis.iθ Tag.E8) (by simp), hp⟩
  · rintro ⟨hr, h0, hp⟩
    refine ⟨⟨hr, fun i hi => ?_⟩, hr, hp⟩
    have : i = Heis.iθ Tag.E8 := by simpa using hi
    subst this
    exact h0

theorem w5_smul_theta : w5 • theta = Pi.single 5 1 := by
  rw [w5, wordProd_smul_foldr, (leviWord_theta).1]

theorem w6_smul_theta : w6 • theta = Pi.single 6 1 := by
  rw [w6, wordProd_smul_foldr, (leviWord_theta).2.1]

theorem w7_smul_theta : w7 • theta = Pi.single 7 1 := by
  rw [w7, wordProd_smul_foldr, (leviWord_theta).2.2]

theorem w_min : (∀ β ∈ parabolicPosRoots Tag.E8 (Heis.Jθ Tag.E8), 0 < height (w5 • β)) ∧
    (∀ β ∈ parabolicPosRoots Tag.E8 (Heis.Jθ Tag.E8), 0 < height (w6 • β)) ∧
    (∀ β ∈ parabolicPosRoots Tag.E8 (Heis.Jθ Tag.E8), 0 < height (w7 • β)) := by
  refine ⟨fun β hβ => ?_, fun β hβ => ?_, fun β hβ => ?_⟩ <;>
    obtain ⟨hr, h0, hp⟩ := mem_parabolicPosRoots_E8.1 hβ
  · rw [w5, wordProd_smul_foldr]
    exact (leviWord_min β (mem_rootFinset.2 hr) h0 hp).1
  · rw [w6, wordProd_smul_foldr]
    exact (leviWord_min β (mem_rootFinset.2 hr) h0 hp).2.1
  · rw [w7, wordProd_smul_foldr]
    exact (leviWord_min β (mem_rootFinset.2 hr) h0 hp).2.2

theorem mem_perp_inter {β : Fin Tag.E8.rank → ℤ}
    (hA : β ∈ parabolicPosRoots Tag.E8 (Heis.Jθ Tag.E8))
    (h5 : β ∈ (fun β => w5 • β) '' parabolicPosRoots Tag.E8 (Heis.Jθ Tag.E8))
    (h6 : β ∈ (fun β => w6 • β) '' parabolicPosRoots Tag.E8 (Heis.Jθ Tag.E8))
    (h7 : β ∈ (fun β => w7 • β) '' parabolicPosRoots Tag.E8 (Heis.Jθ Tag.E8)) : β ∈ S2set := by
  have hperp : ∀ (w : WeylGroup Tag.E8) (j : ℕ) (hj : j < 8),
      w • theta = Pi.single ⟨j, hj⟩ 1 → β ∈ (fun β => w • β) '' parabolicPosRoots Tag.E8
        (Heis.Jθ Tag.E8) → iform β (Pi.single ⟨j, hj⟩ 1) = 0 := by
    intro w j hj hw ⟨β', hβ', hβe⟩
    rw [← hβe, ← hw, iform_smul w β' theta, iform_comm, iform_theta_apply]
    exact (mem_parabolicPosRoots_E8.1 hβ').2.1
  obtain ⟨hr, h0, hp⟩ := mem_parabolicPosRoots_E8.1 hA
  exact perp_inter_E8 β (mem_rootFinset.2 hr) h0 hp (hperp w5 5 (by decide) w5_smul_theta h5)
    (hperp w6 6 (by decide) w6_smul_theta h6) (hperp w7 7 (by decide) w7_smul_theta h7)

theorem closed_inter' {S T : Set (Fin Tag.E8.rank → ℤ)}
    (hS : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot Tag.E8 (a • α + b • β) →
      a • α + b • β ∈ S)
    (hT : ∀ α ∈ T, ∀ β ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot Tag.E8 (a • α + b • β) →
      a • α + b • β ∈ T) :
    ∀ α ∈ S ∩ T, ∀ β ∈ S ∩ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot Tag.E8 (a • α + b • β) →
      a • α + b • β ∈ S ∩ T :=
  fun _ hα _ hβ a b ha hb hr => ⟨hS _ hα.1 _ hβ.1 a b ha hb hr, hT _ hα.2 _ hβ.2 a b ha hb hr⟩

theorem centralizer_X1_le (K : Type) [Field K] {g : ModGL Tag.E8 K}
    (hg : g ∈ adjointGroup Tag.E8 K) (hc : ∀ x ∈ X1 K, g * x = x * g) :
    g ∈ torusGroup Tag.E8 K ⊔ X2 K := by
  classical
  have hUθ : Uθ Tag.E8 K ≤ X1 K := rootSubgroup_le_rootSpan_of_mem theta_mem_S1set
  have hUneg : Heis.Uneg Tag.E8 K ≤ X1 K := rootSubgroup_le_rootSpan_of_mem neg_theta_mem_S1set
  have hL1 : g ∈ Heis.Lθ Tag.E8 K :=
    Heis.centralizer_Uθ_inf_centralizer_Uneg_le_Lθ Tag.E8 K hg
      (fun x hx => hc x (hUθ hx)) (fun x hx => hc x (hUneg hx))
  have hconjL : ∀ (w₀ : WeylGroup Tag.E8) (j : Fin Tag.E8.rank), w₀ • theta = Pi.single j 1 →
      (j.val = 5 ∨ j.val = 6 ∨ j.val = 7) →
      g ∈ conjSub (canonicalRep (coxeterSystem Tag.E8) K w₀) (Heis.Lθ Tag.E8 K) := by
    intro w₀ j hj hjs
    obtain ⟨hS1, hS1'⟩ := single_mem_S1set' j hjs
    have hmapθ : conjSub (canonicalRep (coxeterSystem Tag.E8) K w₀) (Heis.Uθ Tag.E8 K) =
        rootSubgroup Tag.E8 K (Pi.single j 1) := by
      have := CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := K) w₀ isRoot_theta
      rw [hj] at this
      exact this
    have hmapneg : conjSub (canonicalRep (coxeterSystem Tag.E8) K w₀) (Heis.Uneg Tag.E8 K) =
        rootSubgroup Tag.E8 K (-Pi.single j 1) := by
      have := CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup (L := K) w₀
        (Heis.isRoot_neg_highRoot Tag.E8)
      exact this.trans (by rw [show -highRoot Tag.E8 = -theta from rfl, smul_neg, hj])
    refine Heis.mem_conjSub_Lθ_of_centralizes w₀ hg ?_ ?_
    · intro x hx
      rw [hmapθ] at hx
      exact hc x (rootSubgroup_le_rootSpan_of_mem (S := S1set) hS1 hx)
    · intro x hx
      rw [hmapneg] at hx
      exact hc x (rootSubgroup_le_rootSpan_of_mem (S := S1set) hS1' hx)
  have hL5 := hconjL w5 5 w5_smul_theta (Or.inl rfl)
  have hL6 := hconjL w6 6 w6_smul_theta (Or.inr (Or.inl rfl))
  have hL7 := hconjL w7 7 w7_smul_theta (Or.inr (Or.inr rfl))
  obtain ⟨hmin5, hmin6, hmin7⟩ := w_min
  set A := parabolicPosRoots Tag.E8 (Heis.Jθ Tag.E8) with hA
  have hmin1 : ∀ β ∈ A, 0 < height ((1 : WeylGroup Tag.E8) • β) := by
    intro β hβ
    rw [one_smul]
    exact (mem_parabolicPosRoots_E8.1 hβ).2.2
  obtain ⟨wa, ha, ua, va, hha, hua, hva, hwa, hga⟩ :=
    Heis.normalForm_conj_Lθ Tag.E8 K hmin1 (g := g)
      (by rw [canonicalRep_one, Heis.conjSub_one]; exact hL1)
  have himg1 : (fun β => (1 : WeylGroup Tag.E8) • β) '' A = A := by
    ext x
    simp
  rw [himg1] at hua hva
  obtain ⟨hw5, hu5, hv5⟩ := Heis.normalForm_compare hha hua hva hga hmin5 hL5
  obtain ⟨hw6, hu6, hv6⟩ := Heis.normalForm_compare hha hua hva hga hmin6 hL6
  obtain ⟨hw7, hu7, hv7⟩ := Heis.normalForm_compare hha hua hva hga hmin7 hL7
  have hposA : ∀ α ∈ A, IsRoot Tag.E8 α ∧ 0 < height α := fun α hα => Heis.parabolicPosRoots_pos hα
  have hAc : ∀ α ∈ A, ∀ β ∈ A, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot Tag.E8 (a • α + b • β) →
      a • α + b • β ∈ A := fun α hα β hβ a b ha hb hr => add_mem_parabolicPosRoots hα hβ ha hb hr
  set B5 := (fun β => w5 • β) '' A with hB5
  set B6 := (fun β => w6 • β) '' A with hB6
  set B7 := (fun β => w7 • β) '' A with hB7
  have hposB5 := Heis.image_parabolicPosRoots_pos hmin5
  have hposB6 := Heis.image_parabolicPosRoots_pos hmin6
  have hposB7 := Heis.image_parabolicPosRoots_pos hmin7
  have hBc5 := closed_image_smul w5 hAc
  have hBc6 := closed_image_smul w6 hAc
  have hBc7 := closed_image_smul w7 hAc
  have hposAB5 : ∀ α ∈ A ∩ B5, IsRoot Tag.E8 α ∧ 0 < height α := fun α hα => hposA α hα.1
  have hposAB56 : ∀ α ∈ A ∩ B5 ∩ B6, IsRoot Tag.E8 α ∧ 0 < height α := fun α hα => hposA α hα.1.1
  have hI : ∀ x : ModGL Tag.E8 K, x ∈ rootSpan Tag.E8 K A → x ∈ rootSpan Tag.E8 K B5 →
      x ∈ rootSpan Tag.E8 K B6 → x ∈ rootSpan Tag.E8 K B7 →
      x ∈ rootSpan Tag.E8 K (A ∩ B5 ∩ B6 ∩ B7) := by
    intro x hxA hx5 hx6 hx7
    have h1 : x ∈ rootSpan Tag.E8 K (A ∩ B5) :=
      rootSpan_inf_rootSpan_le_rootSpan_inter K hposA hposB5 hAc hBc5 ⟨hxA, hx5⟩
    have h2 : x ∈ rootSpan Tag.E8 K (A ∩ B5 ∩ B6) :=
      rootSpan_inf_rootSpan_le_rootSpan_inter K hposAB5 hposB6 (closed_inter' hAc hBc5) hBc6
        ⟨h1, hx6⟩
    exact rootSpan_inf_rootSpan_le_rootSpan_inter K hposAB56 hposB7
      (closed_inter' (closed_inter' hAc hBc5) hBc6) hBc7 ⟨h2, hx7⟩
  have hS2 : rootSpan Tag.E8 K (A ∩ B5 ∩ B6 ∩ B7) ≤ X2 K :=
    rootSpan_mono_of_subset (fun β hβ => mem_perp_inter hβ.1.1.1 hβ.1.1.2 hβ.1.2 hβ.2)
  have hvA : va ∈ rootSpan Tag.E8 K A := rootSpan_mono_of_subset Set.inter_subset_left hva
  have huX2 : ua ∈ X2 K := hS2 (hI ua hua hu5 hu6 hu7)
  have hvX2 : va ∈ X2 K := hS2 (hI va hvA hv5 hv6 hv7)
  have h1 : wa • theta = theta := by
    have := hwa
    simp only [one_smul] at this
    exact this
  have h5 : wa • (Pi.single 5 1 : Fin Tag.E8.rank → ℤ) = Pi.single 5 1 := by
    have := hw5
    rwa [show highRoot Tag.E8 = theta from rfl, w5_smul_theta] at this
  have h6 : wa • (Pi.single 6 1 : Fin Tag.E8.rank → ℤ) = Pi.single 6 1 := by
    have := hw6
    rwa [show highRoot Tag.E8 = theta from rfl, w6_smul_theta] at this
  have h7 : wa • (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) = Pi.single 7 1 := by
    have := hw7
    rwa [show highRoot Tag.E8 = theta from rfl, w7_smul_theta] at this
  have hJ2 := weyl_fixes_S1_E8 h1 h5 h6 h7
  have hnw : canonicalRep (coxeterSystem Tag.E8) K wa ∈ torusGroup Tag.E8 K ⊔ X2 K :=
    parabolicLevi_J2_le K (canonicalRep_mem_parabolicLevi hJ2)
  rw [hga]
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left hha) (Subgroup.mem_sup_right huX2)) hnw)
    (Subgroup.mem_sup_right hvX2)

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

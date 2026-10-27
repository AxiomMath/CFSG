module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapOverlap
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
open CFSG.Quasithin (perfectCore)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)

section Reorder

theorem IsHypFrame.comp_perm {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {m : ℕ}
    {Q : QuadraticForm K (ι → K)} {a b : Fin m → ι} (h : IsHypFrame Q a b)
    (σ : Equiv.Perm (Fin m)) : IsHypFrame Q (a ∘ σ) (b ∘ σ) where
  hyp k := h.hyp (σ k)
  left_injective := h.left_injective.comp σ.injective
  right_injective := h.right_injective.comp σ.injective
  left_ne_right k l := h.left_ne_right (σ k) (σ l)

theorem exists_perm_fin_zero_one {m : ℕ} (hm : 2 ≤ m) {p r : Fin m} (hpr : p ≠ r) :
    ∃ σ : Equiv.Perm (Fin m), σ ⟨0, by omega⟩ = p ∧ σ ⟨1, by omega⟩ = r := by
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hx0 : Equiv.swap (⟨0, by omega⟩ : Fin m) p r ≠ ⟨0, by omega⟩ := by
    intro h
    have h' := congrArg (Equiv.swap (⟨0, by omega⟩ : Fin m) p) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h'
    exact hpr h'.symm
  refine ⟨Equiv.swap ⟨0, by omega⟩ p * Equiv.swap ⟨1, by omega⟩ (Equiv.swap ⟨0, by omega⟩ p r),
    ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h01 (Ne.symm hx0),
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

end Reorder

section FrameGen

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin m → Fin d}

theorem IsHypFrame.eichler_mem_stabSub (h : IsHypFrame Q a b) (p : Fin m) {u w : Fin d → K}
    (hu : u (a p) = 0) (hu' : u (b p) = 0) (hw : w (a p) = 0) (hw' : w (b p) = 0) :
    eichler Q u w ∈ stabSub (a p) (b p) :=
  mem_stabSub.2 ⟨eichler_apply_of_polar_eq_zero (by rw [(h.hyp p).polar_left, hu'])
      (by rw [(h.hyp p).polar_left, hw']),
    eichler_apply_of_polar_eq_zero (by rw [(h.hyp p).polar_right, hu])
      (by rw [(h.hyp p).polar_right, hw])⟩

omit [Finite K] in
theorem IsHypFrame.pairSwap_mem_stabSub (h : IsHypFrame Q a b) {p r p' : Fin m} (hp : p' ≠ p)
    (hr : p' ≠ r) : pairSwap Q (a p) (b p) (a r) (b r) ∈ stabSub (a p') (b p') := by
  refine mem_stabSub.2 ⟨h.pairSwap_apply_of_vanish ?_ ?_ ?_ ?_,
    h.pairSwap_apply_of_vanish ?_ ?_ ?_ ?_⟩
  · exact Pi.single_eq_of_ne (h.left_injective.ne (Ne.symm hp)) _
  · exact Pi.single_eq_of_ne (fun e => h.left_ne_right p' p e.symm) _
  · exact Pi.single_eq_of_ne (h.left_injective.ne (Ne.symm hr)) _
  · exact Pi.single_eq_of_ne (fun e => h.left_ne_right p' r e.symm) _
  · exact Pi.single_eq_of_ne (h.left_ne_right p p') _
  · exact Pi.single_eq_of_ne (h.right_injective.ne (Ne.symm hp)) _
  · exact Pi.single_eq_of_ne (h.left_ne_right r p') _
  · exact Pi.single_eq_of_ne (h.right_injective.ne (Ne.symm hr)) _

theorem IsHypFrame.stabDerived_sup_stabDerived (h : IsHypFrame Q a b) (hm : 3 ≤ m)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (z : Fin d → K) (hz : IsUnit (Q z)) (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0)
    (hrest : ∀ v : Fin d → K, (∀ k, v (a k) = 0 ∧ v (b k) = 0) → Q v = 0 → v = 0)
    {p p' : Fin m} (hpp' : p ≠ p') :
    stabDerived Q (a p) (b p) ⊔ stabDerived Q (a p') (b p') = ⊤ := by
  obtain ⟨r, hrp, hrp'⟩ := exists_ne_ne_fin hm p p'
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_fin_zero_one (by omega) (Ne.symm hrp)
  set T := stabDerived Q (a p) (b p) ⊔ stabDerived Q (a p') (b p') with hTdef
  have hEH : elementaryGroup Q ≤ T.map (orthDerived Q).subtype := by
    refine (h.comp_perm σ).elementaryGroup_le_of_pairSwap hm z hz (fun k => hza (σ k))
      (fun k => hzb (σ k)) (fun v hv hv0 => hrest v (fun k => ?_) hv0)
      (fun u w hu hu' hw hw' => ?_) ?_
    · simpa using hv (σ.symm k)
    · simp only [Function.comp_apply, hσ0] at hu hu' hw hw'
      exact ⟨⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩,
        (le_sup_left : stabDerived Q (a p) (b p) ≤ T)
          (mem_subgroupOf.2 (h.eichler_mem_stabSub p hu hu' hw hw')), rfl⟩
    · simp only [Function.comp_apply, hσ0, hσ1]
      exact ⟨⟨pairSwap Q (a p) (b p) (a r) (b r), pairSwap_mem_orthDerived hQ hT⟩,
        (le_sup_right : stabDerived Q (a p') (b p') ≤ T)
          (mem_subgroupOf.2 (h.pairSwap_mem_stabSub hpp'.symm hrp'.symm)), rfl⟩
  have hΩ : orthDerived Q = elementaryGroup Q :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1
  rw [eq_top_iff]
  intro x _
  have hx : (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ elementaryGroup Q := hΩ ▸ x.2
  obtain ⟨y, hy, hyx⟩ := hEH hx
  have hxy : y = x := Subtype.ext hyx
  rw [← hxy]
  exact hy

omit [Finite K] [CharP K 2] in
theorem stabPairsBar_le_perfectCore_inf_centralizer {a a' b b' : Fin d}
    (hb : IsHypCoord Q b b')
    (hperf : ⁅stabPairsBar Q a a' b b', stabPairsBar Q a a' b b'⁆ = stabPairsBar Q a a' b b') :
    stabPairsBar Q a a' b b' ≤
      perfectCore (pairPerpOf Q a a' ⊓ centralizer (pairTorusOf Q b b' : Set _)) := by
  refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf ?_ ?_) hperf
  · exact map_mono fun _ hx => (mem_subgroupOf.mp hx).1
  · have hle : stabPairsBar Q a a' b b' ≤ pairPerpOf Q b b' :=
      map_mono fun _ hx => (mem_subgroupOf.mp hx).2
    exact hle.trans (le_centralizer_iff.mp hb.pairTorusOf_le_centralizer_pairPerpOf)

end FrameGen

section MinusGen

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem minusStabDerived_sup_eq_top (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {p p' : Fin (n - 1)} (hpp' : p ≠ p') :
    stabDerived (coordinateQuadMinus n K (by omega) b c) (minusIndexEquiv n (by omega) (.inl p))
        (minusIndexEquiv n (by omega) (.inr (.inl p))) ⊔
      stabDerived (coordinateQuadMinus n K (by omega) b c)
        (minusIndexEquiv n (by omega) (.inl p')) (minusIndexEquiv n (by omega) (.inr (.inl p'))) =
      ⊤ := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  exact (isHypFrame_minus K hn1 b c).stabDerived_sup_stabDerived (by omega) hQ hT
    (minusAnisoVec hn1) (by rw [coordinateQuadMinus_minusAnisoVec]; exact isUnit_one)
    (minusAnisoVec_frameLeft hn1) (minusAnisoVec_frameRight hn1)
    (eq_zero_of_frame_vanish_minus hn1 hirr) hpp'

theorem minusPairPerp_le_stabPairsBar_sup (hn : 5 ≤ n) (h1 : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a a' a'' : Fin (n - 1)} (h₁ : a ≠ a')
    (h₂ : a ≠ a'') (h₃ : a' ≠ a'') :
    minusPairPerp (K := K) h1 b c a ≤
      stabPairsBar (coordinateQuadMinus n K h1 b c) (minusIndexEquiv n h1 (.inl a))
          (minusIndexEquiv n h1 (.inr (.inl a))) (minusIndexEquiv n h1 (.inl a'))
          (minusIndexEquiv n h1 (.inr (.inl a'))) ⊔
        stabPairsBar (coordinateQuadMinus n K h1 b c) (minusIndexEquiv n h1 (.inl a))
          (minusIndexEquiv n h1 (.inr (.inl a))) (minusIndexEquiv n h1 (.inl a''))
          (minusIndexEquiv n h1 (.inr (.inl a''))) := by
  obtain ⟨j₁, hj₁⟩ := exists_avoid_eq (M := n - 1 - 1) (by omega : n - 1 - 1 + 1 = n - 1)
    (Ne.symm h₁)
  obtain ⟨j₂, hj₂⟩ := exists_avoid_eq (M := n - 1 - 1) (by omega : n - 1 - 1 + 1 = n - 1)
    (Ne.symm h₂)
  have hj : j₁ ≠ j₂ := fun e => h₃ (by rw [← hj₁, ← hj₂, e])
  set S₁ := stabPairsBar (coordinateQuadMinus n K h1 b c) (minusIndexEquiv n h1 (.inl a))
    (minusIndexEquiv n h1 (.inr (.inl a))) (minusIndexEquiv n h1 (.inl a'))
    (minusIndexEquiv n h1 (.inr (.inl a'))) with hS₁
  set S₂ := stabPairsBar (coordinateQuadMinus n K h1 b c) (minusIndexEquiv n h1 (.inl a))
    (minusIndexEquiv n h1 (.inr (.inl a))) (minusIndexEquiv n h1 (.inl a''))
    (minusIndexEquiv n h1 (.inr (.inl a''))) with hS₂
  set D := minusPairPerp (K := K) h1 b c a with hD
  set φ := minusPairPerpEquiv (K := K) hn hirr a with hφ
  have hm₁ : (S₁.subgroupOf D).map φ.toMonoidHom = _ := map_minusStabPairsBar hn hirr hj₁
  have hm₂ : (S₂.subgroupOf D).map φ.toMonoidHom = _ := map_minusStabPairsBar hn hirr hj₂
  have htop := minusStabDerived_sup_eq_top (K := K) (n := n - 1) (by omega) hirr hj
  intro x hx
  have hy : φ ⟨x, hx⟩ ∈ (S₁.subgroupOf D ⊔ S₂.subgroupOf D).map φ.toMonoidHom := by
    rw [Subgroup.map_sup, hm₁, hm₂, htop]
    exact mem_top _
  obtain ⟨y, hy, hyx⟩ := hy
  have hyx' : y = ⟨x, hx⟩ := φ.injective hyx
  rw [hyx'] at hy
  have hle : (S₁.subgroupOf D ⊔ S₂.subgroupOf D).map D.subtype ≤ S₁ ⊔ S₂ := by
    rw [Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype]
    exact sup_le_sup inf_le_left inf_le_left
  exact hle ⟨⟨x, hx⟩, hy, rfl⟩

theorem stabPairsBar_le_minusOverlap (hn : 5 ≤ n) (h1 : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a a' : Fin (n - 1)} (h : a ≠ a') :
    stabPairsBar (coordinateQuadMinus n K h1 b c) (minusIndexEquiv n h1 (.inl a))
        (minusIndexEquiv n h1 (.inr (.inl a))) (minusIndexEquiv n h1 (.inl a'))
        (minusIndexEquiv n h1 (.inr (.inl a'))) ≤ minusOverlap (K := K) h1 b c a a' :=
  stabPairsBar_le_perfectCore_inf_centralizer (isHypCoord_coordinateQuadMinus h1 b c a')
    (isPerfect_iff.mp (isQuasisimple_minusStabPairsBar_of_five_le hn hirr h).1.1)

theorem minusPairPerp_le_minusOverlap_sup (hn : 5 ≤ n) (h1 : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a a' a'' : Fin (n - 1)} (h₁ : a ≠ a')
    (h₂ : a ≠ a'') (h₃ : a' ≠ a'') :
    minusPairPerp (K := K) h1 b c a ≤ minusOverlap h1 b c a a' ⊔ minusOverlap h1 b c a a'' :=
  (minusPairPerp_le_stabPairsBar_sup hn h1 hirr h₁ h₂ h₃).trans
    (sup_le_sup (stabPairsBar_le_minusOverlap hn h1 hirr h₁)
      (stabPairsBar_le_minusOverlap hn h1 hirr h₂))

theorem iSup_minusPairPerp_eq_top (hn : 4 ≤ n) (h1 : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ⨆ a : Fin (n - 1), minusPairPerp (K := K) h1 b c a = ⊤ := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  have h := isHypFrame_minus K h1 b c
  refine eq_top_of_minusPairPerp_le hn hirr
    (le_iSup (fun a => minusPairPerp (K := K) h1 b c a) ⟨0, by omega⟩) ?_
  refine le_iSup (fun a => minusPairPerp (K := K) h1 b c a) ⟨2, by omega⟩ ?_
  refine ⟨⟨_, pairSwap_mem_orthDerived hQ hT⟩,
    mem_subgroupOf.2 (h.pairSwap_mem_stabSub ?_ ?_), rfl⟩
  · simp [Fin.ext_iff]
  · simp [Fin.ext_iff]

theorem minusSwapGenInput_of_five_le (hn : 5 ≤ n) (h1 : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : MinusSwapGenInput n K h1 b c where
  le_sup _ _ _ h₁ h₂ h₃ := minusPairPerp_le_minusOverlap_sup hn h1 hirr h₁ h₂ h₃
  iSup_eq_top := iSup_minusPairPerp_eq_top (by omega) h1 hirr

end MinusGen

section MinusOverlap

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem minusOverlap_eq_stabPairsBar_of_five_le (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (h1 : 1 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a a' : Fin (n - 1)} (h : a ≠ a') :
    minusOverlap (K := K) h1 b c a a' =
      stabPairsBar (coordinateQuadMinus n K h1 b c)
        (minusIndexEquiv n h1 (.inl a)) (minusIndexEquiv n h1 (.inr (.inl a)))
        (minusIndexEquiv n h1 (.inl a')) (minusIndexEquiv n h1 (.inr (.inl a'))) :=
  perfectCore_pairPerpOf_inf_centralizer_pairTorusOf hq
    (isHypCoord_coordinateQuadMinus _ b c a) (isHypCoord_coordinateQuadMinus _ b c a')
    (isPerfect_iff.mp (isQuasisimple_minusStabPairsBar_of_five_le hn hirr h).1.1)

theorem isSimpleGroup_minusOverlap_of_five_le (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (h1 : 1 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a a' : Fin (n - 1)} (h : a ≠ a') :
    IsSimpleGroup (minusOverlap (K := K) h1 b c a a') := by
  rw [minusOverlap_eq_stabPairsBar_of_five_le hq hn h1 hirr h]
  obtain ⟨hqs, hZ⟩ := isQuasisimple_minusStabPairsBar_of_five_le (K := K) hn hirr h
  exact isSimpleGroup_of_isQuasisimple_of_center_eq_bot hqs hZ

theorem center_minusOverlap_eq_bot_of_five_le (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (h1 : 1 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a a' : Fin (n - 1)} (h : a ≠ a') :
    center (minusOverlap (K := K) h1 b c a a') = ⊥ := by
  rw [minusOverlap_eq_stabPairsBar_of_five_le hq hn h1 hirr h]
  exact (isQuasisimple_minusStabPairsBar_of_five_le (K := K) hn hirr h).2

theorem exists_ne_one_mem_minusOverlap_triple_of_five_le (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    (h1 : 1 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {o k l : Fin (n - 1)}
    (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) :
    ∃ x : matrixProjectiveDerived (coordinateQuadMinus n K h1 b c), x ≠ 1 ∧
      x ∈ minusOverlap (K := K) h1 b c o k ∧ x ∈ minusOverlap (K := K) h1 b c o l ∧
        x ∈ minusOverlap (K := K) h1 b c k l := by
  obtain ⟨j, hjo, hjk, hjl⟩ := exists_ne_ne_ne_fin (by omega) o k l
  have hne : minusPairTorus (K := K) h1 b c j ≠ ⊥ :=
    ne_bot_of_one_lt_card (by rw [card_minusPairTorus]; omega)
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hmem : ∀ {a a' : Fin (n - 1)}, a ≠ a' → j ≠ a → j ≠ a' →
      x ∈ minusOverlap (K := K) h1 b c a a' := fun h hja hja' => by
    rw [minusOverlap_eq_stabPairsBar_of_five_le hq hn h1 hirr h]
    exact minusPairTorus_le_stabPairsBar _ b c hja hja' hx
  exact ⟨x, hx1', hmem hok hjo hjk, hmem hol hjo hjl, hmem hkl hjk hjl⟩

theorem minusSwapOverlapInput_of_five_le (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (h1 : 1 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : MinusSwapOverlapInput n K h1 b c where
  isSimpleGroup _ _ h := isSimpleGroup_minusOverlap_of_five_le hq hn h1 hirr h
  center_eq_bot _ _ h := center_minusOverlap_eq_bot_of_five_le hq hn h1 hirr h
  le_sup := (minusSwapGenInput_of_five_le hn h1 hirr).le_sup
  triple _ _ _ hok hol hkl :=
    exists_ne_one_mem_minusOverlap_triple_of_five_le hq hn h1 hirr hok hol hkl
  iSup_eq_top := (minusSwapGenInput_of_five_le hn h1 hirr).iSup_eq_top

end MinusOverlap

end CFSG.SeitzReduction.OmegaPilot

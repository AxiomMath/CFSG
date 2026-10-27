module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapMinus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)

section Eichler

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}

theorem eichler_mem_orthDerived_of_ne_zero_ne_one (hQ : (polarBilin Q).Nondegenerate) {c : K}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) (u w : W) : eichler Q u w ∈ orthDerived Q := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  swap
  · rw [eichler_of_not h]
    exact one_mem _
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
    exact one_mem _
  obtain ⟨y, hy⟩ : ∃ y, polar Q u y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hQ.1 u fun v => by rw [polarBilin_apply_apply]; exact hcon v)
  obtain ⟨y', hy'⟩ : ∃ y', polar Q u y' = 1 :=
    ⟨(polar Q u y)⁻¹ • y, by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]⟩
  have huu : polar Q u u = 0 := polar_self_eq_zero h.1
  obtain ⟨f, hQf, hpf⟩ : ∃ f, Q f = 0 ∧ polar Q u f = 1 := by
    refine ⟨y' + (-Q y') • u, ?_, ?_⟩
    · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, h.1, smul_zero, add_zero,
        polar_smul_right, polar_comm, hy', smul_eq_mul, mul_one, add_neg_cancel]
    · rw [polar_add_right, polar_smul_right, huu, smul_zero, add_zero, hy']
  let P : HypPair Q := ⟨u, f, h.1, hQf, hpf⟩
  have hw₀ : P.proj w ∈ P.perp := P.proj_mem_perp w
  have hwu : polar Q w u = 0 := by rw [polar_comm]; exact h.2
  have hw : w = P.proj w + polar Q w f • u := by
    change w = (w - polar Q w f • u - polar Q w u • f) + polar Q w f • u
    rw [hwu, zero_smul, sub_zero, sub_add_cancel]
  have hE : eichler Q u w = eichler Q P.e (P.proj w) := by
    change eichler Q u w = eichler Q u (P.proj w)
    conv_lhs => rw [hw]
    exact eichler_add_smul_self h.1 _ _
  rw [hE]
  exact CFSG.RankThree.Classical.eichler_mem_commutator_orthogonalGroup hc0 hc1 P hw₀

end Eichler

section Trick

variable {K : Type} [Field K] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)} {a b : Fin m → Fin d}

theorem IsHypFrame.frameRootElt_eq_conj (h : IsHypFrame Q a b) {p q : Fin m} (hpq : p ≠ q)
    {z w' : Fin d → K} (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0)
    (hwa : ∀ k, w' (a k) = 0) (hwb : ∀ k, w' (b k) = 0) :
    frameRootElt Q a b p q (-polar Q z w') =
      (eichler Q (Pi.single (a p) 1) z)⁻¹ *
        (eichler Q (Pi.single (b q) 1) w' * eichler Q (Pi.single (a p) 1) z *
          (eichler Q (Pi.single (b q) 1) w')⁻¹) := by
  have hgO := eichler_mem_orthogonalGroup Q (Pi.single (b q) 1) w'
  have hfq : Q (Pi.single (b q) 1) = 0 := (h.hyp q).map_right
  have hfw : polar Q (Pi.single (b q) 1) w' = 0 := by rw [(h.hyp q).polar_right]; exact hwa q
  have hep : eichler Q (Pi.single (b q) 1) w' (Pi.single (a p) 1) = Pi.single (a p) 1 := by
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [(h.hyp p).polar_left, Pi.single_eq_of_ne (fun e => hpq (h.right_injective e))]
    · rw [(h.hyp p).polar_left]
      exact hwb p
  have hzq : polar Q z (Pi.single (b q) 1) = 0 := by
    rw [polar_comm, (h.hyp q).polar_right]
    exact hza q
  have hgz : eichler Q (Pi.single (b q) 1) w' z = z + (-polar Q z w') • Pi.single (b q) 1 := by
    rw [eichler_apply hfq hfw, hzq, zero_smul, add_zero, mul_zero, add_zero, neg_smul,
      sub_eq_add_neg]
  have hconj := eichler_conj hgO (Pi.single (a p) 1) z
  rw [hep, hgz] at hconj
  have hpz : polar Q (Pi.single (a p) 1) z = 0 := by rw [(h.hyp p).polar_left]; exact hzb p
  have hpf : polar Q (Pi.single (a p) 1) ((-polar Q z w') • Pi.single (b q) 1) = 0 := by
    rw [(h.hyp p).polar_left, Pi.smul_apply,
      Pi.single_eq_of_ne (fun e => hpq (h.right_injective e)), smul_zero]
  rw [hconj, ← eichler_mul hpz hpf, inv_mul_cancel_left]
  rfl

end Trick

section Six

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem minusStabDerived_sup_eq_top_three (hq : 4 ≤ Nat.card K) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0) {p p' : Fin (4 - 1 - 1)} (hpp' : p ≠ p') :
    stabDerived (coordinateQuadMinus (4 - 1) K (by omega) β γ)
        (minusIndexEquiv (4 - 1) (by omega) (.inl p))
        (minusIndexEquiv (4 - 1) (by omega) (.inr (.inl p))) ⊔
      stabDerived (coordinateQuadMinus (4 - 1) K (by omega) β γ)
        (minusIndexEquiv (4 - 1) (by omega) (.inl p'))
        (minusIndexEquiv (4 - 1) (by omega) (.inr (.inl p'))) = ⊤ := by
  have h1 : 1 ≤ 4 - 1 := by omega
  have hF := isHypFrame_minus K h1 β γ
  obtain ⟨hR, hW⟩ := regular_wittIndex_coordinateQuadMinus (K := K) (m := 4 - 1) h1 hirr
  obtain ⟨c₀, hc0, hc1⟩ := CFSG.RankThree.PartOne.KCOrthogonal.exists_ne_zero_ne_one_of_two_lt
    (K := K) (by omega)
  have hE : ∀ u w, eichler (coordinateQuadMinus (4 - 1) K h1 β γ) u w ∈
      orthDerived (coordinateQuadMinus (4 - 1) K h1 β γ) :=
    eichler_mem_orthDerived_of_ne_zero_ne_one hR hc0 hc1
  set T := stabDerived (coordinateQuadMinus (4 - 1) K h1 β γ)
        (minusIndexEquiv (4 - 1) h1 (.inl p)) (minusIndexEquiv (4 - 1) h1 (.inr (.inl p))) ⊔
      stabDerived (coordinateQuadMinus (4 - 1) K h1 β γ)
        (minusIndexEquiv (4 - 1) h1 (.inl p')) (minusIndexEquiv (4 - 1) h1 (.inr (.inl p')))
    with hTdef
  set H := T.map (orthDerived (coordinateQuadMinus (4 - 1) K h1 β γ)).subtype with hHdef
  have hk : ∀ k : Fin (4 - 1 - 1), k = p ∨ k = p' := by
    intro k
    rcases k with ⟨k, hk⟩
    rcases p with ⟨p, hp⟩
    rcases p' with ⟨p', hp'⟩
    simp only [ne_eq, Fin.mk.injEq] at hpp' ⊢
    omega
  have hin : ∀ (k : Fin (4 - 1 - 1)) {g}
      (hg : g ∈ orthDerived (coordinateQuadMinus (4 - 1) K h1 β γ)),
      g ∈ stabSub (minusFrameLeft h1 k) (minusFrameRight h1 k) → g ∈ H := by
    intro k g hg hgs
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rcases hk k with rfl | rfl
    · exact (le_sup_left : _ ≤ T) (mem_subgroupOf.2 hgs)
    · exact (le_sup_right : _ ≤ T) (mem_subgroupOf.2 hgs)
  have A := isAnisoCoord_coordinateQuadMinus (K := K) h1 hirr
  have hβ : β ≠ 0 := A.b_ne_zero
  have hroot : ∀ p₁ q₁ : Fin (4 - 1 - 1), p₁ ≠ q₁ → ∀ x : K,
      frameRootElt (coordinateQuadMinus (4 - 1) K h1 β γ) (minusFrameLeft h1)
        (minusFrameRight h1) p₁ q₁ x ∈ H := by
    intro p₁ q₁ hpq x
    set w' : Fin (2 * (4 - 1)) → K := (-x / β) • Pi.single (anisoCoordRight h1) 1 with hw'
    have hwa : ∀ k, w' (minusFrameLeft h1 k) = 0 := fun k => by
      simp [hw', minusFrameLeft, anisoCoordRight, (minusIndexEquiv (4 - 1) h1).injective.eq_iff]
    have hwb : ∀ k, w' (minusFrameRight h1 k) = 0 := fun k => by
      simp [hw', minusFrameRight, anisoCoordRight, (minusIndexEquiv (4 - 1) h1).injective.eq_iff]
    have hpol : polar (coordinateQuadMinus (4 - 1) K h1 β γ) (minusAnisoVec h1) w' = -x := by
      change polar (coordinateQuadMinus (4 - 1) K h1 β γ) (Pi.single (anisoCoordLeft h1) 1) w' = -x
      rw [A.polar_left, hw', Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        mul_div_cancel₀ _ hβ]
    have key := hF.frameRootElt_eq_conj hpq (minusAnisoVec_frameLeft h1)
      (minusAnisoVec_frameRight h1) hwa hwb
    rw [hpol, neg_neg] at key
    rw [key]
    have h₁ : eichler (coordinateQuadMinus (4 - 1) K h1 β γ) (Pi.single (minusFrameLeft h1 p₁) 1)
        (minusAnisoVec h1) ∈ H :=
      hin q₁ (hE _ _) (hF.eichler_mem_stabSub q₁
        (Pi.single_eq_of_ne (fun e => hpq.symm (hF.left_injective e)) _)
        (Pi.single_eq_of_ne (fun e => hF.left_ne_right p₁ q₁ e.symm) _)
        (minusAnisoVec_frameLeft h1 q₁) (minusAnisoVec_frameRight h1 q₁))
    have h₂ : eichler (coordinateQuadMinus (4 - 1) K h1 β γ) (Pi.single (minusFrameRight h1 q₁) 1)
        w' ∈ H :=
      hin p₁ (hE _ _) (hF.eichler_mem_stabSub p₁
        (Pi.single_eq_of_ne (fun e => hF.left_ne_right p₁ q₁ e) _)
        (Pi.single_eq_of_ne (fun e => hpq (hF.right_injective e)) _) (hwa p₁) (hwb p₁))
    exact mul_mem (inv_mem h₁) (mul_mem (mul_mem h₂ h₁) (inv_mem h₂))
  have hplane : ∀ u w : Fin (2 * (4 - 1)) → K,
      (∀ k, k ≠ p → u (minusFrameLeft h1 k) = 0 ∧ u (minusFrameRight h1 k) = 0) →
      (∀ k, k ≠ p → w (minusFrameLeft h1 k) = 0 ∧ w (minusFrameRight h1 k) = 0) →
      eichler (coordinateQuadMinus (4 - 1) K h1 β γ) u w ∈ H := fun u w hu hw =>
    hin p' (hE u w) (hF.eichler_mem_stabSub p' (hu p' hpp'.symm).1 (hu p' hpp'.symm).2
      (hw p' hpp'.symm).1 (hw p' hpp'.symm).2)
  have hEH : elementaryGroup (coordinateQuadMinus (4 - 1) K h1 β γ) ≤ H :=
    hF.elementaryGroup_le_of_rootElt (coordinateQuadMinus_minusAnisoVec h1 β γ)
      (minusAnisoVec_frameLeft h1) (minusAnisoVec_frameRight h1)
      (eq_zero_of_frame_vanish_minus h1 hirr) hroot p hplane
  have hts : ∀ U : Submodule K (Fin (2 * (4 - 1)) → K), Module.finrank K U = 3 →
      ∃ u ∈ U, coordinateQuadMinus (4 - 1) K h1 β γ u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    have := hW U hcon
    omega
  obtain ⟨hqs, hZ⟩ := isQuasisimple_orthDerived_of_six hR (by rw [Module.finrank_fin_fun]) hts
  have hsimple := isSimpleGroup_of_isQuasisimple_of_center_eq_bot hqs hZ
  set E' := (elementaryGroup (coordinateQuadMinus (4 - 1) K h1 β γ)).subgroupOf
    (orthDerived (coordinateQuadMinus (4 - 1) K h1 β γ)) with hE'def
  have hE'n : E'.Normal := ⟨fun x hx g => mem_subgroupOf.2
    (conj_mem_elementaryGroup (Subgroup.commutator_le_self _ g.2) (mem_subgroupOf.1 hx))⟩
  have := hsimple
  have := hE'n
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal E' with hbot | htop
  · exfalso
    set r := frameRootElt (coordinateQuadMinus (4 - 1) K h1 β γ) (minusFrameLeft h1)
      (minusFrameRight h1) p p' 1 with hr
    have hrE : (⟨r, hE _ _⟩ : orthDerived (coordinateQuadMinus (4 - 1) K h1 β γ)) ∈ E' :=
      mem_subgroupOf.2 (eichler_mem_elementaryGroup _ _ _)
    rw [hbot, mem_bot] at hrE
    have hr1 : r = 1 := congrArg Subtype.val hrE
    have happ := congrFun (congrArg (fun g => (g : (Fin (2 * (4 - 1)) → K) ≃ₗ[K] _)
      (Pi.single (minusFrameRight h1 p) 1)) hr1) (minusFrameRight h1 p')
    simp only [hr] at happ
    rw [hF.frameRootElt_apply hpp'] at happ
    simp [hF.right_injective.eq_iff, Ne.symm hpp', (hF.left_ne_right p' p)] at happ
  · rw [eq_top_iff]
    intro x _
    have hx : (x : (Fin (2 * (4 - 1)) → K) ≃ₗ[K] _) ∈ H :=
      hEH (mem_subgroupOf.1 (htop ▸ mem_top x : x ∈ E'))
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← Subtype.ext hyx]
    exact hy

end Six

section Four

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem minusPairPerp_le_stabPairsBar_sup_four (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a a' a'' : Fin (4 - 1)} (h₁ : a ≠ a')
    (h₂ : a ≠ a'') (h₃ : a' ≠ a'') :
    minusPairPerp (K := K) (n := 4) (by omega) b c a ≤
      stabPairsBar (coordinateQuadMinus 4 K (by omega) b c) (minusIndexEquiv 4 (by omega) (.inl a))
          (minusIndexEquiv 4 (by omega) (.inr (.inl a))) (minusIndexEquiv 4 (by omega) (.inl a'))
          (minusIndexEquiv 4 (by omega) (.inr (.inl a'))) ⊔
        stabPairsBar (coordinateQuadMinus 4 K (by omega) b c)
          (minusIndexEquiv 4 (by omega) (.inl a)) (minusIndexEquiv 4 (by omega) (.inr (.inl a)))
          (minusIndexEquiv 4 (by omega) (.inl a''))
          (minusIndexEquiv 4 (by omega) (.inr (.inl a''))) := by
  obtain ⟨j₁, hj₁⟩ := exists_avoid_eq (M := 4 - 1 - 1) (by omega : 4 - 1 - 1 + 1 = 4 - 1)
    (Ne.symm h₁)
  obtain ⟨j₂, hj₂⟩ := exists_avoid_eq (M := 4 - 1 - 1) (by omega : 4 - 1 - 1 + 1 = 4 - 1)
    (Ne.symm h₂)
  have hj : j₁ ≠ j₂ := fun e => h₃ (by rw [← hj₁, ← hj₂, e])
  set S₁ := stabPairsBar (coordinateQuadMinus 4 K (by omega) b c)
    (minusIndexEquiv 4 (by omega) (.inl a)) (minusIndexEquiv 4 (by omega) (.inr (.inl a)))
    (minusIndexEquiv 4 (by omega) (.inl a')) (minusIndexEquiv 4 (by omega) (.inr (.inl a')))
    with hS₁
  set S₂ := stabPairsBar (coordinateQuadMinus 4 K (by omega) b c)
    (minusIndexEquiv 4 (by omega) (.inl a)) (minusIndexEquiv 4 (by omega) (.inr (.inl a)))
    (minusIndexEquiv 4 (by omega) (.inl a'')) (minusIndexEquiv 4 (by omega) (.inr (.inl a'')))
    with hS₂
  set D := minusPairPerp (K := K) (n := 4) (by omega) b c a with hD
  set φ := minusPairPerpEquivOfLe (K := K) (n := 4) le_rfl hirr a with hφ
  have hm₁ : (S₁.subgroupOf D).map φ.toMonoidHom = _ := map_minusStabPairsBarOfLe le_rfl hirr hj₁
  have hm₂ : (S₂.subgroupOf D).map φ.toMonoidHom = _ := map_minusStabPairsBarOfLe le_rfl hirr hj₂
  have htop := minusStabDerived_sup_eq_top_three (K := K) hq hirr hj
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

theorem minusFourSwapGenInput_holds (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : MinusFourSwapGenInput K b c := by
  intro a a' a'' h₁ h₂ h₃
  rw [minusOverlap_eq_stabPairsBar_four hq hirr h₁, minusOverlap_eq_stabPairsBar_four hq hirr h₂]
  exact minusPairPerp_le_stabPairsBar_sup_four hq hirr h₁ h₂ h₃

end Four

end CFSG.SeitzReduction.OmegaPilot

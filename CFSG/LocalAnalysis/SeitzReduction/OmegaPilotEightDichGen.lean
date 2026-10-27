module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapPlusGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightLeviOTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus plusIndexEquiv regular_coordinateQuadPlus)

section Trick

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_smul_eq_conj {u v z w : V} (hv : Q v = 0) (huv : polar Q u v = 0)
    (huz : polar Q u z = 0) (huw : polar Q u w = 0) (hvz : polar Q v z = 0)
    (hvw : polar Q v w = 0) :
    eichler Q u ((-polar Q z w) • v) =
      (eichler Q u z)⁻¹ * (eichler Q v w * eichler Q u z * (eichler Q v w)⁻¹) := by
  have hconj := eichler_conj (eichler_mem_orthogonalGroup Q v w) u z
  have hu : eichler Q v w u = u := eichler_apply_of_polar_eq_zero huv huw
  have hzv : polar Q z v = 0 := by rw [polar_comm]; exact hvz
  have hz : eichler Q v w z = z + (-polar Q z w) • v := by
    rw [eichler_apply hv hvw, hzv, zero_smul, add_zero, mul_zero, add_zero, neg_smul,
      sub_eq_add_neg]
  rw [hu, hz] at hconj
  have hpv : polar Q u ((-polar Q z w) • v) = 0 := by rw [polar_smul_right, huv, smul_zero]
  rw [hconj, ← eichler_mul huz hpv, inv_mul_cancel_left]

end Trick

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_zero_of_polar_plusFrame' {m : ℕ} {v : Fin (2 * m) → K}
    (hv : ∀ k r, polar (coordinateQuadPlus m K) v (coordFrameVec (plusFrameLeft m)
      (plusFrameRight m) k r) = 0) : v = 0 := by
  have h := isHypFrame_plus K m
  obtain hab := h.apply_eq_zero_of_polar hv
  funext x
  obtain ⟨y, rfl⟩ := (plusIndexEquiv m).surjective x
  rcases y with y | y
  · exact (hab y).1
  · exact (hab y).2

theorem plusStabDerived_sup_eq_top {m : ℕ} (hm : 3 ≤ m) {p p' : Fin m} (hpp' : p ≠ p') :
    stabDerived (coordinateQuadPlus m K) (plusIndexEquiv m (.inl p))
        (plusIndexEquiv m (.inr p)) ⊔
      stabDerived (coordinateQuadPlus m K) (plusIndexEquiv m (.inl p'))
        (plusIndexEquiv m (.inr p')) = ⊤ := by
  have h := isHypFrame_plus K m
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus m K hm
  set F := h.toHypFrameOfThree hm with hF
  set T := stabDerived (coordinateQuadPlus m K) (plusIndexEquiv m (.inl p))
        (plusIndexEquiv m (.inr p)) ⊔
      stabDerived (coordinateQuadPlus m K) (plusIndexEquiv m (.inl p'))
        (plusIndexEquiv m (.inr p')) with hTdef
  set H := T.map (orthDerived (coordinateQuadPlus m K)).subtype with hHdef
  have hE := eichler_mem_orthDerived hQ hT
  have hin : ∀ (k : Fin m), (k = p ∨ k = p') → ∀ u w : Fin (2 * m) → K,
      u (plusFrameLeft m k) = 0 → u (plusFrameRight m k) = 0 →
      w (plusFrameLeft m k) = 0 → w (plusFrameRight m k) = 0 →
      eichler (coordinateQuadPlus m K) u w ∈ H := by
    intro k hk u w hu hu' hw hw'
    have hs := h.eichler_mem_stabSub k hu hu' hw hw'
    refine ⟨⟨_, hE u w⟩, ?_, rfl⟩
    rcases hk with rfl | rfl
    · exact (le_sup_left : _ ≤ T) (mem_subgroupOf.2 hs)
    · exact (le_sup_right : _ ≤ T) (mem_subgroupOf.2 hs)
  have hvan : ∀ {k l : Fin m}, k ≠ l → ∀ (r : Bool) (c : K),
      (c • coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) k r) (plusFrameLeft m l)
        = 0 ∧
      (c • coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) k r) (plusFrameRight m l)
        = 0 := by
    intro k l hkl r c
    obtain ⟨h1, h2⟩ := h.coordFrameVec_vanish hkl r
    exact ⟨by rw [Pi.smul_apply, h1, smul_zero], by rw [Pi.smul_apply, h2, smul_zero]⟩
  have hvan1 : ∀ {k l : Fin m}, k ≠ l → ∀ (r : Bool),
      coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) k r (plusFrameLeft m l) = 0 ∧
      coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) k r (plusFrameRight m l) = 0 :=
    fun hkl r => h.coordFrameVec_vanish hkl r
  have hlong : ∀ {i j : Fin m}, i ≠ j → ∀ (s t : Bool) (c : K),
      eichler (coordinateQuadPlus m K) (F.vec j t) (c • F.vec i s) ∈ H := by
    intro i j hij s t c
    rw [hF, IsHypFrame.toHypFrameOfThree_vec]
    by_cases hp : p ≠ i ∧ p ≠ j
    · exact hin p (Or.inl rfl) _ _ (hvan1 (Ne.symm hp.2) t).1 (hvan1 (Ne.symm hp.2) t).2
        (hvan (Ne.symm hp.1) s c).1 (hvan (Ne.symm hp.1) s c).2
    by_cases hp' : p' ≠ i ∧ p' ≠ j
    · exact hin p' (Or.inr rfl) _ _ (hvan1 (Ne.symm hp'.2) t).1 (hvan1 (Ne.symm hp'.2) t).2
        (hvan (Ne.symm hp'.1) s c).1 (hvan (Ne.symm hp'.1) s c).2
    have hi : i = p ∨ i = p' := by
      by_contra hcon
      push Not at hcon hp hp'
      rcases eq_or_ne p i with hpi | hpi
      · exact hcon.1 hpi.symm
      · have hpj := hp hpi
        rcases eq_or_ne p' i with hpi' | hpi'
        · exact hcon.2 hpi'.symm
        · exact hpp' (hpj.trans (hp' hpi').symm)
    have hj : j = p ∨ j = p' := by
      by_contra hcon
      push Not at hcon hp hp'
      rcases eq_or_ne p i with hpi | hpi
      · rcases eq_or_ne p' i with hpi' | hpi'
        · exact hpp' (hpi.trans hpi'.symm)
        · exact hcon.2 (hp' hpi').symm
      · exact hcon.1 (hp hpi).symm
    obtain ⟨k, hki, hkj⟩ := exists_ne_ne_fin hm i j
    set u := coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) j t with hu
    set v := coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) i s with hv
    set z := coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) k true with hz
    set w := (-c) • coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) k false with hw
    have hpol : ∀ {x y : Fin m}, x ≠ y → ∀ (r r' : Bool) (c' : K),
        polar (coordinateQuadPlus m K)
          (coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) x r)
          (c' • coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) y r') = 0 := by
      intro x y hxy r r' c'
      have h0 := F.polar_vec_of_ne hxy r r'
      rw [hF, IsHypFrame.toHypFrameOfThree_vec] at h0
      rw [polar_smul_right, h0, smul_zero]
    have hpol1 : ∀ {x y : Fin m}, x ≠ y → ∀ (r r' : Bool),
        polar (coordinateQuadPlus m K)
          (coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) x r)
          (coordFrameVec (K := K) (plusFrameLeft m) (plusFrameRight m) y r') = 0 := by
      intro x y hxy r r'
      simpa using hpol hxy r r' 1
    have hzw : polar (coordinateQuadPlus m K) z w = -c := by
      rw [hz, hw, polar_smul_right, h.polar_coordFrameVec]
      simp [h.coordFrameVec_apply_right]
    have key := eichler_smul_eq_conj (Q := coordinateQuadPlus m K) (u := u) (v := v) (z := z)
      (w := w) (F.map_vec i s) (hpol1 hij.symm t s) (hpol1 hkj.symm t true)
      (hpol hkj.symm t false (-c)) (hpol1 hki.symm s true) (hpol hki.symm s false (-c))
    rw [hzw, neg_neg] at key
    rw [key]
    have h₁ : eichler (coordinateQuadPlus m K) u z ∈ H :=
      hin i hi u z (hvan1 hij.symm t).1 (hvan1 hij.symm t).2 (hvan1 hki true).1
        (hvan1 hki true).2
    have h₂ : eichler (coordinateQuadPlus m K) v w ∈ H :=
      hin j hj v w (hvan1 hij s).1 (hvan1 hij s).2 (hvan hkj false (-c)).1
        (hvan hkj false (-c)).2
    exact mul_mem (inv_mem h₁) (mul_mem (mul_mem h₂ h₁) (inv_mem h₂))
  have hperp : ∀ (i : Fin m) (s : Bool) (v : Fin (2 * m) → K),
      (∀ k r, polar (coordinateQuadPlus m K) v (F.vec k r) = 0) →
      eichler (coordinateQuadPlus m K) (F.vec i s) v ∈ H := by
    intro i s v hv
    rw [eq_zero_of_polar_plusFrame' hv, eichler_zero_right]
    exact one_mem _
  have hEH : elementaryGroup (coordinateQuadPlus m K) ≤ H :=
    F.elementaryGroup_le hlong hperp fun v hv _ => eq_zero_of_polar_plusFrame' hv
  have hΩ : orthDerived (coordinateQuadPlus m K) = elementaryGroup (coordinateQuadPlus m K) :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1
  rw [eq_top_iff]
  intro x _
  have hx : (x : (Fin (2 * m) → K) ≃ₗ[K] _) ∈ H := hEH (hΩ ▸ x.2)
  obtain ⟨y, hy, hyx⟩ := hx
  rw [← Subtype.ext hyx]
  exact hy

end Plus

section Four

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem pairPerp_le_stabTwoBar_sup_four {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : pairPerp (K := K) a ≤ stabTwoBar K a b ⊔ stabTwoBar K a c := by
  obtain ⟨j₁, hj₁⟩ := exists_avoid_eq (M := 4 - 1) (by omega : 4 - 1 + 1 = 4) (Ne.symm hab)
  obtain ⟨j₂, hj₂⟩ := exists_avoid_eq (M := 4 - 1) (by omega : 4 - 1 + 1 = 4) (Ne.symm hac)
  have hj : j₁ ≠ j₂ := fun e => hbc (by rw [← hj₁, ← hj₂, e])
  set φ := pairPerpEquiv (K := K) (le_rfl : 4 ≤ 4) a with hφ
  have hm₁ := map_stabTwoBar (K := K) (le_rfl : 4 ≤ 4) hj₁
  have hm₂ := map_stabTwoBar (K := K) (le_rfl : 4 ≤ 4) hj₂
  have htop := plusStabDerived_sup_eq_top (K := K) (m := 4 - 1) (by omega) hj
  intro x hx
  have hy : φ ⟨x, hx⟩ ∈ ((stabTwoBar K a b).subgroupOf (pairPerp a) ⊔
      (stabTwoBar K a c).subgroupOf (pairPerp a)).map φ.toMonoidHom := by
    rw [Subgroup.map_sup, hm₁, hm₂, htop]
    exact mem_top _
  obtain ⟨y, hy, hyx⟩ := hy
  have hyx' : y = ⟨x, hx⟩ := φ.injective hyx
  rw [hyx'] at hy
  have hle : ((stabTwoBar K a b).subgroupOf (pairPerp a) ⊔
      (stabTwoBar K a c).subgroupOf (pairPerp a)).map (pairPerp (K := K) a).subtype ≤
        stabTwoBar K a b ⊔ stabTwoBar K a c := by
    rw [Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype]
    exact sup_le_sup inf_le_left inf_le_left
  exact hle ⟨⟨x, hx⟩, hy, rfl⟩

theorem stabTwoBar_le_plusOverlap_four (hq : 4 ≤ Nat.card K) {a b : Fin 4} (hab : a ≠ b) :
    stabTwoBar K a b ≤ plusOverlap (K := K) a b :=
  stabPairsBar_le_perfectCore_inf_centralizer (isHypCoord_coordinateQuadPlus b)
    (plusFourLeviInput_holds K hq a b hab).1

theorem pairPerp_le_plusOverlap_sup_four (hq : 4 ≤ Nat.card K) {a b c : Fin 4} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    pairPerp (K := K) a ≤ plusOverlap a b ⊔ plusOverlap a c :=
  (pairPerp_le_stabTwoBar_sup_four hab hac hbc).trans
    (sup_le_sup (stabTwoBar_le_plusOverlap_four hq hab) (stabTwoBar_le_plusOverlap_four hq hac))

theorem plusFourSwapGenInput_holds (hq : 4 ≤ Nat.card K) : PlusFourSwapGenInput K :=
  plusFourSwapGenInput_of_levi plusFourLeviInput_holds hq fun _ _ _ hab hac hbc =>
    pairPerp_le_plusOverlap_sup_four hq hab hac hbc

end Four

section Swap

open CFSG.SeitzReduction.SeitzQ2 (SwapPairExclusion)


theorem omegaPlusFourSwapInput_of_dichotomy (hdich : PlusFourSwapDichotomyInput)
    (hP : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
    OmegaPlusFourSwapInput :=
  omegaPlusFourSwapInput_of_inputs (fun _ _ _ _ hq => plusFourSwapGenInput_holds hq) hdich hP

end Swap

end CFSG.SeitzReduction.OmegaPilot

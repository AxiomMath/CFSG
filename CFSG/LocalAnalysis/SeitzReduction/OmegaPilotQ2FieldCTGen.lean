module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldCTSupp
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveFlip
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived
  matrixDerived matrixProjectiveProjection)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus plusIndexEquiv regular_coordinateQuadPlus)
open CFSG.SeitzReduction.SymplecticPilot (planeCoords planeOf)

section Nodes

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem iSup_perfectCore_centralizer_eq_top {n f : ℕ} (hn : 4 ≤ n) (hFf : Nat.card F = 2 ^ f)
    (hF : 4 ≤ Nat.card F) {ι' : Type*}
    (H : ι' → Subgroup (matrixProjectiveDerived (coordinateQuadPlus n F)))
    (hH : ∀ j : Fin n, ∃ y, rationalNode (K := F) (by omega : 1 ≤ n) j ≤
      centralizer (H y : Set (matrixProjectiveDerived (coordinateQuadPlus n F)))) :
    ⨆ y, perfectCore (centralizer
      (H y : Set (matrixProjectiveDerived (coordinateQuadPlus n F)))) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← iSup_rationalNode (K := F) hn hFf hF]
  refine iSup_le fun j => ?_
  obtain ⟨y, hy⟩ := hH j
  exact (le_perfectCore_of_perfect hy (commutator_rationalNode (by omega) hF j)).trans
    (le_iSup (fun y => perfectCore (centralizer
      (H y : Set (matrixProjectiveDerived (coordinateQuadPlus n F))))) y)

theorem rationalNode_le_centralizer_of_le_suppBar {n : ℕ} (hn : 1 ≤ n) (j : Fin n)
    {P : Finset (Fin n)} (hP : Disjoint (plusNodeSet n j) P)
    {H : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n F))}
    (hH : H ≤ suppBar (coordinateQuadPlus n F) (plusIndexEquiv n '' planeCoords P)) :
    rationalNode (K := F) hn j ≤
      centralizer (H : Set (matrixProjectiveDerived (coordinateQuadPlus n F))) :=
  ((rationalNode_le_suppBar hn j).trans (suppBar_le_centralizer
    ((Set.disjoint_image_iff (plusIndexEquiv n).injective).2 (disjoint_planeCoords hP)))).trans
    (centralizer_le hH)

end Nodes

section Swap

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

variable (K) in
@[expose] noncomputable def planeSwapLin (i j : Fin n) :
    (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K) :=
  pairSwap (coordinateQuadPlus n K) (plusIndexEquiv n (.inl i)) (plusIndexEquiv n (.inr i))
    (plusIndexEquiv n (.inl j)) (plusIndexEquiv n (.inr j))

theorem planeSwap_apply {i j : Fin n} (hij : i ≠ j) (s : Fin n ⊕ Fin n) :
    planeSwapLin K i j (Pi.single (plusIndexEquiv n s) 1) =
      Pi.single (plusIndexEquiv n (Sum.map (Equiv.swap i j) (Equiv.swap i j) s)) 1 := by
  have hi := isHypCoord_coordinateQuadPlus (K := K) i
  have hj := isHypCoord_coordinateQuadPlus (K := K) j
  have hd := pairDisjoint_plus hij
  obtain ⟨hl, hr⟩ := pairSwap_apply_left hi hj hd
  obtain ⟨hl', hr'⟩ := pairSwap_apply_right' hi hj hd
  rcases s with k | k
  · by_cases hki : k = i
    · subst hki
      rw [Sum.map_inl, Equiv.swap_apply_left]
      exact hl
    · by_cases hkj : k = j
      · subst hkj
        rw [Sum.map_inl, Equiv.swap_apply_right]
        exact hl'
      · rw [Sum.map_inl, Equiv.swap_apply_of_ne_of_ne hki hkj]
        refine pairSwap_apply_single_of_ne hi hj ?_ ?_ ?_ ?_ <;> intro h <;>
          have := (plusIndexEquiv n).injective h <;> simp_all
  · by_cases hki : k = i
    · subst hki
      rw [Sum.map_inr, Equiv.swap_apply_left]
      exact hr
    · by_cases hkj : k = j
      · subst hkj
        rw [Sum.map_inr, Equiv.swap_apply_right]
        exact hr'
      · rw [Sum.map_inr, Equiv.swap_apply_of_ne_of_ne hki hkj]
        refine pairSwap_apply_single_of_ne hi hj ?_ ?_ ?_ ?_ <;> intro h <;>
          have := (plusIndexEquiv n).injective h <;> simp_all

theorem planeSwapLin_mem_orthDerived [Finite K] (hn : 3 ≤ n) (i j : Fin n) :
    planeSwapLin K i j ∈ orthDerived (coordinateQuadPlus n K) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n K hn
  exact pairSwap_mem_orthDerived hQ hT

end Swap

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

variable (m) in
@[expose] def lowPlanes : Finset (Fin (m + 2)) := Finset.univ.filter fun x => x.val < 2

variable (m) in
@[expose] def midPlanes : Finset (Fin (m + 2)) :=
  Finset.univ.filter fun x => x.val = 3 ∨ x.val = 4

theorem mem_lowPlanes {x : Fin (m + 2)} : x ∈ lowPlanes m ↔ x.val < 2 := by simp [lowPlanes]

theorem mem_midPlanes {x : Fin (m + 2)} : x ∈ midPlanes m ↔ x.val = 3 ∨ x.val = 4 := by
  simp [midPlanes]

theorem single_mem_image_perpSub {b c : K} (hb : b ≠ 0) (s : Fin (m + 2) ⊕ Fin (m + 2))
    (hs : 2 ≤ (planeOf s).val) :
    (Pi.single (plusIndexEquiv (m + 2) s) 1 : Fin (2 * (m + 2)) → K) ∈
      (plusAnisoIsometry b c hb).toLinearEquiv ''
        (perpSub K (plusAnisoLeft m) (plusAnisoRight m) : Set (Fin (2 * (m + 2)) → K)) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin m, s = .inl j.succ.succ ∨ s = .inr j.succ.succ := by
    rcases s with i | i <;> rcases fin_cases_two i with rfl | rfl | ⟨j, rfl⟩
    all_goals first
      | exact ⟨j, Or.inl rfl⟩
      | exact ⟨j, Or.inr rfl⟩
      | (simp [planeOf] at hs)
  have h0 : s ≠ .inl 0 := by
    rcases hj with rfl | rfl
    · exact fun h => fin_succ_succ_ne_zero j (Sum.inl_injective h)
    · exact Sum.inr_ne_inl
  have h0' : s ≠ .inr 0 := by
    rcases hj with rfl | rfl
    · exact Sum.inl_ne_inr
    · exact fun h => fin_succ_succ_ne_zero j (Sum.inr_injective h)
  refine ⟨_, ⟨?_, ?_⟩, plusAnisoIsometry_single hb j s hj⟩
  · exact Pi.single_eq_of_ne (fun h => h0 ((plusIndexEquiv (m + 2)).injective h).symm) 1
  · exact Pi.single_eq_of_ne (fun h => h0' ((plusIndexEquiv (m + 2)).injective h).symm) 1

theorem map_plusAnisoTorus_le_fixVecBar {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (plusAnisoTorus m hirr).map (plusAnisoProjEquiv m hirr).toMonoidHom ≤
      fixVecBar (coordinateQuadPlus (m + 2) K)
        ((plusAnisoIsometry b c (coeff_ne_zero_of_irreducible' hirr)).toLinearEquiv ''
          (perpSub K (plusAnisoLeft m) (plusAnisoRight m) : Set (Fin (2 * (m + 2)) → K))) :=
  (map_mono (anisoTorusOf_le_fixVecBar (Q := plusAnisoQuad K m b c)
    (isAnisoCoord_plusAnisoQuad (m := m) hirr).ne b c)).trans
    (map_fixVecBar_le_of_isometry _ _ (fun g => plusAnisoProjEquiv_projHom hirr g) _)

theorem map_plusAnisoTorus_le_suppBar {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (plusAnisoTorus m hirr).map (plusAnisoProjEquiv m hirr).toMonoidHom ≤
      suppBar (coordinateQuadPlus (m + 2) K)
        (plusIndexEquiv (m + 2) '' planeCoords (lowPlanes m)) := by
  refine (map_plusAnisoTorus_le_fixVecBar hirr).trans
    (fixVecBar_le_suppBar (fun x hx => ?_) (dual_coordinateQuadPlus _))
  obtain ⟨s, rfl⟩ := (plusIndexEquiv (m + 2)).surjective x
  refine single_mem_image_perpSub _ s ?_
  by_contra h
  exact hx ⟨s, by rw [SymplecticPilot.mem_planeCoords, mem_lowPlanes]; omega, rfl⟩

theorem two_le_swap_swap (hm : 3 ≤ m) (p : Fin (m + 2)) (hp : ¬ (p.val = 3 ∨ p.val = 4)) :
    2 ≤ (Equiv.swap (⟨1, by omega⟩ : Fin (m + 2)) ⟨4, by omega⟩
      (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2)) ⟨3, by omega⟩ p)).val := by
  simp only [Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> simp only [Fin.ext_iff] at * <;> omega

@[expose] noncomputable def plusSwapLin (K : Type) [Field K] [CharP K 2] (m : ℕ) (hm : 3 ≤ m) :
    (Fin (2 * (m + 2)) → K) ≃ₗ[K] (Fin (2 * (m + 2)) → K) :=
  planeSwapLin K (⟨0, by omega⟩ : Fin (m + 2)) ⟨3, by omega⟩ *
    planeSwapLin K (⟨1, by omega⟩ : Fin (m + 2)) ⟨4, by omega⟩

theorem plusSwapLin_mem_orthDerived (hm : 3 ≤ m) :
    plusSwapLin K m hm ∈ orthDerived (coordinateQuadPlus (m + 2) K) :=
  mul_mem (planeSwapLin_mem_orthDerived (by omega) _ _)
    (planeSwapLin_mem_orthDerived (by omega) _ _)

theorem map_conj_plusAnisoTorus_le_suppBar (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ((plusAnisoTorus m hirr).map (plusAnisoProjEquiv m hirr).toMonoidHom).map
        (MulAut.conj (projHom (coordinateQuadPlus (m + 2) K)
          ⟨plusSwapLin K m hm, plusSwapLin_mem_orthDerived hm⟩)).toMonoidHom ≤
      suppBar (coordinateQuadPlus (m + 2) K)
        (plusIndexEquiv (m + 2) '' planeCoords (midPlanes m)) := by
  refine (map_mono (map_plusAnisoTorus_le_fixVecBar hirr)).trans ?_
  rw [map_conj_fixVecBar]
  refine fixVecBar_le_suppBar (fun x hx => ?_) (dual_coordinateQuadPlus _)
  obtain ⟨s, rfl⟩ := (plusIndexEquiv (m + 2)).surjective x
  have hs : ¬ ((planeOf s).val = 3 ∨ (planeOf s).val = 4) := fun h =>
    hx ⟨s, by rw [SymplecticPilot.mem_planeCoords, mem_midPlanes]; exact h, rfl⟩
  set τ₁ := Equiv.swap (⟨0, by omega⟩ : Fin (m + 2)) ⟨3, by omega⟩ with hτ₁
  set τ₂ := Equiv.swap (⟨1, by omega⟩ : Fin (m + 2)) ⟨4, by omega⟩ with hτ₂
  set t := Sum.map τ₂ τ₂ (Sum.map τ₁ τ₁ s) with ht
  have hpt : planeOf t = τ₂ (τ₁ (planeOf s)) := by
    rw [ht]
    rcases s with i | i <;> rfl
  have h03 : (⟨0, by omega⟩ : Fin (m + 2)) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have h14 : (⟨1, by omega⟩ : Fin (m + 2)) ≠ ⟨4, by omega⟩ := by simp [Fin.ext_iff]
  have hσ : plusSwapLin K m hm (Pi.single (plusIndexEquiv (m + 2) t) 1) =
      Pi.single (plusIndexEquiv (m + 2) s) 1 := by
    rw [plusSwapLin, LinearEquiv.mul_apply, planeSwap_apply h14, planeSwap_apply h03]
    congr 2
    rw [ht, Sum.map_map, Sum.map_map]
    rcases s with i | i <;> simp [hτ₁, hτ₂, Equiv.swap_apply_self]
  obtain ⟨w, hw, hSw⟩ := single_mem_image_perpSub (K := K) (coeff_ne_zero_of_irreducible' hirr) t
    (by rw [hpt]; exact two_le_swap_swap hm _ hs)
  exact ⟨_, ⟨w, hw, rfl⟩, by rw [hSw]; exact hσ⟩

end Plus

section PlusGen

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem iSup_perfectCore_centralizer_plusAnisoTorus_eq_top {m f : ℕ} (hm : 4 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ι : K →+* F) (hFf : Nat.card F = 2 ^ f)
    (hF : 4 ≤ Nat.card F) :
    ⨆ y : matrixProjectiveDerived (coordinateQuadPlus (m + 2) K),
      perfectCore (centralizer (((((plusAnisoTorus m hirr).map
        (plusAnisoProjEquiv m hirr).toMonoidHom).map (MulAut.conj y).toMonoidHom).map
        (fieldEmbed ι (m + 2) (by omega)) :
          Subgroup (matrixProjectiveDerived (coordinateQuadPlus (m + 2) F))) :
        Set (matrixProjectiveDerived (coordinateQuadPlus (m + 2) F)))) = ⊤ := by
  refine iSup_perfectCore_centralizer_eq_top (by omega) hFf hF _ fun j => ?_
  by_cases hj : 2 ≤ j.val
  · refine ⟨1, rationalNode_le_centralizer_of_le_suppBar _ j (P := lowPlanes m) ?_ ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_plusNodeSet] at hx
      rw [mem_lowPlanes] at hx'
      omega
    · rw [map_conj_one_eq]
      exact (map_mono (map_plusAnisoTorus_le_suppBar hirr)).trans
        (map_fieldEmbed_suppBar_le ι _ _)
  · refine ⟨projHom _ ⟨plusSwapLin K m (by omega), plusSwapLin_mem_orthDerived (by omega)⟩,
      rationalNode_le_centralizer_of_le_suppBar _ j (P := midPlanes m) ?_ ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_plusNodeSet] at hx
      rw [mem_midPlanes] at hx'
      omega
    · exact (map_mono (map_conj_plusAnisoTorus_le_suppBar (by omega) hirr)).trans
        (map_fieldEmbed_suppBar_le ι _ _)

theorem omegaPlusTwoFieldGenInput_holds : OmegaPlusTwoFieldGenInput := by
  intro m hm K _ _ _ b c hirr _ F _ _ _ ι hF4
  exact iSup_perfectCore_centralizer_plusAnisoTorus_eq_top (f := 2) hm hirr ι
    (by rw [hF4]; norm_num) (by omega)

end PlusGen

end CFSG.SeitzReduction.OmegaPilot

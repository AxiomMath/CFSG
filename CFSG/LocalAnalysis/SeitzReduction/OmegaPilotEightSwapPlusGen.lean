module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapPlusMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus plusIndexEquiv regular_coordinateQuadPlus)

section Frame

variable {K : Type} [Field K] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)} {a b : Fin m → Fin d}

@[expose] noncomputable def IsHypFrame.toHypFrameOfThree (h : IsHypFrame Q a b) (hm : 3 ≤ m) :
    CFSG.LieType.Universal.Spin.HypFrame Q m where
  vec := coordFrameVec a b
  map_vec k s := by
    cases s
    · exact (h.hyp k).map_right
    · exact (h.hyp k).map_left
  polar_vec_of_ne i j hij s t := by
    rw [h.polar_coordFrameVec]
    cases s
    · simp [h.coordFrameVec_apply_left, Ne.symm hij]
    · simp [h.coordFrameVec_apply_right, Ne.symm hij]
  polar_vec_not i s := by
    rw [h.polar_coordFrameVec]
    cases s
    · simp [h.coordFrameVec_apply_left]
    · simp [h.coordFrameVec_apply_right]
  exists_aux i j := by
    obtain ⟨k, hki, hkj⟩ := exists_ne_ne_fin hm i j
    refine ⟨Pi.single (a k) 1 + Pi.single (b k) 1, ?_, fun s => ⟨?_, ?_⟩⟩
    · rw [QuadraticMap.map_add Q, (h.hyp k).map_left, (h.hyp k).map_right, (h.hyp k).polar_left,
        Pi.single_eq_same, zero_add, zero_add]
      exact isUnit_one
    · rw [h.polar_coordFrameVec]
      have h1 : a k ≠ b i := h.left_ne_right k i
      have h2 : b k ≠ b i := fun e => hki (h.right_injective e)
      have h3 : a k ≠ a i := fun e => hki (h.left_injective e)
      have h4 : b k ≠ a i := fun e => h.left_ne_right i k e.symm
      cases s <;> simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]
    · rw [h.polar_coordFrameVec]
      have h1 : a k ≠ b j := h.left_ne_right k j
      have h2 : b k ≠ b j := fun e => hkj (h.right_injective e)
      have h3 : a k ≠ a j := fun e => hkj (h.left_injective e)
      have h4 : b k ≠ a j := fun e => h.left_ne_right j k e.symm
      cases s <;> simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]

@[simp] theorem IsHypFrame.toHypFrameOfThree_vec (h : IsHypFrame Q a b) (hm : 3 ≤ m) :
    (h.toHypFrameOfThree hm).vec = coordFrameVec a b := rfl

end Frame

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_zero_of_polar_plusFrame {v : Fin (2 * 4) → K}
    (hv : ∀ k r, polar (coordinateQuadPlus 4 K) v (coordFrameVec (plusFrameLeft 4)
      (plusFrameRight 4) k r) = 0) : v = 0 := by
  have h := isHypFrame_plus K 4
  obtain hab := h.apply_eq_zero_of_polar hv
  funext x
  obtain ⟨y, rfl⟩ := (plusIndexEquiv 4).surjective x
  rcases y with y | y
  · exact (hab y).1
  · exact (hab y).2

theorem iSup_pairPerp_eq_top_four : ⨆ k : Fin 4, pairPerp (K := K) k = ⊤ := by
  have h := isHypFrame_plus K 4
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  set F := h.toHypFrameOfThree (by norm_num) with hF
  set T : Subgroup (orthDerived (coordinateQuadPlus 4 K)) := ⨆ k : Fin 4,
    stabDerived (coordinateQuadPlus 4 K) (plusFrameLeft 4 k) (plusFrameRight 4 k) with hTdef
  set H := T.map (orthDerived (coordinateQuadPlus 4 K)).subtype with hHdef
  have hin : ∀ (k : Fin 4) {g} (hg : g ∈ orthDerived (coordinateQuadPlus 4 K)),
      g ∈ stabSub (plusFrameLeft 4 k) (plusFrameRight 4 k) → g ∈ H := fun k g hg hgs =>
    ⟨⟨g, hg⟩, le_iSup (fun k : Fin 4 => stabDerived (coordinateQuadPlus 4 K)
      (plusFrameLeft 4 k) (plusFrameRight 4 k)) k (mem_subgroupOf.2 hgs), rfl⟩
  have hE := eichler_mem_orthDerived hQ hT
  have hlong : ∀ {i j : Fin 4}, i ≠ j → ∀ (s t : Bool) (c : K),
      eichler (coordinateQuadPlus 4 K) (F.vec j t) (c • F.vec i s) ∈ H := by
    intro i j hij s t c
    obtain ⟨k, hki, hkj⟩ := exists_ne_ne_fin (by norm_num : 3 ≤ 4) i j
    refine hin k (hE _ _) (mem_stabSub.2 ⟨?_, ?_⟩)
    · refine eichler_apply_of_polar_eq_zero ?_ ?_
      · rw [hF, IsHypFrame.toHypFrameOfThree_vec, polar_comm]
        exact F.polar_vec_of_ne hkj.symm t true
      · rw [hF, IsHypFrame.toHypFrameOfThree_vec, polar_comm, polar_smul_left,
          show (Pi.single (plusFrameLeft 4 k) 1 : Fin (2 * 4) → K) =
            coordFrameVec (plusFrameLeft 4) (plusFrameRight 4) k true from rfl,
          polar_comm]
        rw [show polar (coordinateQuadPlus 4 K)
            (coordFrameVec (plusFrameLeft 4) (plusFrameRight 4) k true)
            (coordFrameVec (plusFrameLeft 4) (plusFrameRight 4) i s) = 0 from
            F.polar_vec_of_ne hki true s, smul_zero]
    · refine eichler_apply_of_polar_eq_zero ?_ ?_
      · rw [hF, IsHypFrame.toHypFrameOfThree_vec, polar_comm]
        exact F.polar_vec_of_ne hkj.symm t false
      · rw [hF, IsHypFrame.toHypFrameOfThree_vec, polar_comm, polar_smul_left,
          show (Pi.single (plusFrameRight 4 k) 1 : Fin (2 * 4) → K) =
            coordFrameVec (plusFrameLeft 4) (plusFrameRight 4) k false from rfl,
          polar_comm]
        rw [show polar (coordinateQuadPlus 4 K)
            (coordFrameVec (plusFrameLeft 4) (plusFrameRight 4) k false)
            (coordFrameVec (plusFrameLeft 4) (plusFrameRight 4) i s) = 0 from
            F.polar_vec_of_ne hki false s, smul_zero]
  have hperp : ∀ (i : Fin 4) (s : Bool) (v : Fin (2 * 4) → K),
      (∀ k r, polar (coordinateQuadPlus 4 K) v (F.vec k r) = 0) →
      eichler (coordinateQuadPlus 4 K) (F.vec i s) v ∈ H := by
    intro i s v hv
    rw [eq_zero_of_polar_plusFrame hv, eichler_zero_right]
    exact one_mem _
  have hEH : elementaryGroup (coordinateQuadPlus 4 K) ≤ H :=
    F.elementaryGroup_le hlong hperp fun v hv _ => eq_zero_of_polar_plusFrame hv
  have hΩ : orthDerived (coordinateQuadPlus 4 K) = elementaryGroup (coordinateQuadPlus 4 K) :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1
  have hTtop : T = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : (Fin (2 * 4) → K) ≃ₗ[K] _) ∈ H := hEH (hΩ ▸ x.2)
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← Subtype.ext hyx]
    exact hy
  have hmap : ⨆ k : Fin 4, pairPerp (K := K) k = T.map (projHom (coordinateQuadPlus 4 K)) := by
    rw [hTdef, Subgroup.map_iSup]
    rfl
  rw [hmap, hTtop, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
  exact projHom_surjective _

theorem plusFourSwapGenInput_of_levi (hlevi : PlusFourLeviInput) (hq : 4 ≤ Nat.card K)
    (hle : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      pairPerp (K := K) a ≤ plusOverlap a b ⊔ plusOverlap a c) : PlusFourSwapGenInput K where
  le_sup := hle
  triple _ _ _ hok hol hkl := plusFourSwapTriple_of_levi hlevi hq hok hol hkl
  iSup_eq_top := iSup_pairPerp_eq_top_four

end Plus

end CFSG.SeitzReduction.OmegaPilot

module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHsylBasic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

section Coord

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

@[expose] def piW (a a' b b' : Fin d) (v : Fin d → K) : Fin d → K :=
  perpPart b b' (perpPart a a' v)

@[expose] def subW (K : Type*) [Field K] (a a' b b' : Fin d) : Submodule K (Fin d → K) :=
  perpSub K a a' ⊓ perpSub K b b'

theorem mem_subW {v : Fin d → K} :
    v ∈ subW K a a' b b' ↔ (v a = 0 ∧ v a' = 0) ∧ v b = 0 ∧ v b' = 0 := Iff.rfl

theorem piW_apply_of_ne {i : Fin d} (h1 : i ≠ a) (h2 : i ≠ a') (h3 : i ≠ b) (h4 : i ≠ b')
    (v : Fin d → K) : piW a a' b b' v i = v i := by
  rw [piW, perpPart_apply_of_ne h3 h4, perpPart_apply_of_ne h1 h2]

theorem piW_mem (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b') (hd : PairDisjoint a a' b b')
    (v : Fin d → K) : piW a a' b b' v ∈ subW K a a' b b' := by
  refine ⟨⟨?_, ?_⟩, perpPart_apply_left hj.ne _, perpPart_apply_right hj.ne _⟩
  · rw [piW, perpPart_apply_of_ne hd.left_ne_left.symm hd.right_ne_left.symm,
      perpPart_apply_left hi.ne]
  · rw [piW, perpPart_apply_of_ne hd.left_ne_right.symm hd.right_ne_right.symm,
      perpPart_apply_right hi.ne]

theorem piW_eq_self {w : Fin d → K} (hw : w ∈ subW K a a' b b') : piW a a' b b' w = w := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hw
  simp [piW, perpPart, h1, h2, h3, h4]

theorem piW_add (v w : Fin d → K) :
    piW a a' b b' (v + w) = piW a a' b b' v + piW a a' b b' w := by
  funext i
  simp only [piW, perpPart, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem piW_smul (c : K) (v : Fin d → K) : piW a a' b b' (c • v) = c • piW a a' b b' v := by
  funext i
  simp only [piW, perpPart, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem piW_single_of_mem {i : Fin d} (hi : i = a ∨ i = a' ∨ i = b ∨ i = b')
    (hd : PairDisjoint a a' b b') (haa : a ≠ a') (hbb : b ≠ b') :
    piW a a' b b' (Pi.single i (1 : K)) = 0 := by
  funext j
  by_cases hja : j = a
  · subst hja
    rw [piW, perpPart_apply_of_ne hd.left_ne_left.symm hd.right_ne_left.symm,
      perpPart_apply_left haa]
    rfl
  by_cases hja' : j = a'
  · subst hja'
    rw [piW, perpPart_apply_of_ne hd.left_ne_right.symm hd.right_ne_right.symm,
      perpPart_apply_right haa]
    rfl
  by_cases hjb : j = b
  · subst hjb
    rw [piW, perpPart_apply_left hbb]
    rfl
  by_cases hjb' : j = b'
  · subst hjb'
    rw [piW, perpPart_apply_right hbb]
    rfl
  rw [piW_apply_of_ne hja hja' hjb hjb', Pi.zero_apply]
  rcases hi with rfl | rfl | rfl | rfl <;> exact Pi.single_eq_of_ne (by assumption) _

theorem eq_coord (hd : PairDisjoint a a' b b') (v : Fin d → K) :
    v = v a • Pi.single a 1 + v a' • Pi.single a' 1 + v b • Pi.single b 1 +
      v b' • Pi.single b' 1 + piW a a' b b' v := by
  have h1 := eq_add_perpPart a a' v
  have h2 := eq_add_perpPart b b' (perpPart a a' v)
  rw [perpPart_apply_of_ne hd.left_ne_left hd.left_ne_right,
    perpPart_apply_of_ne hd.right_ne_left hd.right_ne_right] at h2
  rw [piW]
  conv_lhs => rw [h1, h2]
  abel

theorem map_eq_coord (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') (v : Fin d → K) :
    Q v = v a * v a' + v b * v b' + Q (piW a a' b b' v) := by
  rw [hi.apply_eq v, hj.apply_eq, perpPart_apply_of_ne hd.left_ne_left hd.left_ne_right,
    perpPart_apply_of_ne hd.right_ne_left hd.right_ne_right, piW]
  ring

theorem polar_eq_coord (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') (x y : Fin d → K) :
    polar Q x y = x a * y a' + x a' * y a + x b * y b' + x b' * y b +
      polar Q (piW a a' b b' x) (piW a a' b b' y) := by
  have hW := piW_mem hi hj hd y
  have h1 : ∀ w ∈ subW K a a' b b', polar Q (piW a a' b b' x) w = polar Q x w := by
    intro w hw
    rw [piW, hj.polar_perpPart_left _ hw.2, hi.polar_perpPart_left _ hw.1]
  have h2 : polar Q x (perpPart b b' (perpPart a a' y)) =
      polar Q (piW a a' b b' x) (piW a a' b b' y) := (h1 _ hW).symm
  rw [hi.polar_eq x y, hj.polar_eq x, perpPart_apply_of_ne hd.left_ne_left hd.left_ne_right,
    perpPart_apply_of_ne hd.right_ne_left hd.right_ne_right, h2]
  ring

end Coord

section Radical

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

theorem rootRadical_coords (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hg : g ∈ rootRadical Q hi.hypPair hj.hypPair) :
    (g (Pi.single a' 1)) a' = 1 ∧ (g (Pi.single a' 1)) b' = 0 ∧ (g (Pi.single b' 1)) a' = 0 ∧
      (g (Pi.single b' 1)) b' = 1 := by
  obtain ⟨hgO, hg1, hg2, -⟩ := hg
  simp only [IsHypCoord.hypPair_e] at hg1 hg2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := polar_map_of_mem hgO (Pi.single a 1) (Pi.single a' 1)
    rwa [hg1, hi.polar_left, hi.polar_left, Pi.single_eq_same] at h
  · have h := polar_map_of_mem hgO (Pi.single b 1) (Pi.single a' 1)
    rwa [hg2, hj.polar_left, hj.polar_left, Pi.single_eq_of_ne hd.right_ne_right] at h
  · have h := polar_map_of_mem hgO (Pi.single a 1) (Pi.single b' 1)
    rwa [hg1, hi.polar_left, hi.polar_left, Pi.single_eq_of_ne hd.right_ne_right.symm] at h
  · have h := polar_map_of_mem hgO (Pi.single b 1) (Pi.single b' 1)
    rwa [hg2, hj.polar_left, hj.polar_left, Pi.single_eq_same] at h

theorem rootRadical_apply_f₁ (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hg : g ∈ rootRadical Q hi.hypPair hj.hypPair) :
    g (Pi.single a' 1) = (-Q (piW a a' b b' (g (Pi.single a' 1)))) • Pi.single a 1 +
      Pi.single a' 1 + (g (Pi.single a' 1)) b • Pi.single b 1 +
      piW a a' b b' (g (Pi.single a' 1)) := by
  obtain ⟨hxa', hxb', -, -⟩ := rootRadical_coords hi hj hd hg
  have hQx : Q (g (Pi.single a' 1)) = 0 := by rw [map_of_mem hg.1, hi.map_right]
  have hxa : (g (Pi.single a' 1)) a = -Q (piW a a' b b' (g (Pi.single a' 1))) := by
    rw [map_eq_coord hi hj hd, hxa', hxb'] at hQx
    linear_combination hQx
  conv_lhs => rw [eq_coord hd (g (Pi.single a' 1))]
  rw [hxa, hxa', hxb', zero_smul, add_zero, one_smul]

theorem rootRadical_apply_f₂ (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hg : g ∈ rootRadical Q hi.hypPair hj.hypPair) :
    g (Pi.single b' 1) = (-((g (Pi.single a' 1)) b + polar Q (piW a a' b b' (g (Pi.single a' 1)))
      (piW a a' b b' (g (Pi.single b' 1))))) • Pi.single a 1 +
      (-Q (piW a a' b b' (g (Pi.single b' 1)))) • Pi.single b 1 + Pi.single b' 1 +
      piW a a' b b' (g (Pi.single b' 1)) := by
  obtain ⟨hxa', hxb', hya', hyb'⟩ := rootRadical_coords hi hj hd hg
  have hQy : Q (g (Pi.single b' 1)) = 0 := by rw [map_of_mem hg.1, hj.map_right]
  have hyb : (g (Pi.single b' 1)) b = -Q (piW a a' b b' (g (Pi.single b' 1))) := by
    rw [map_eq_coord hi hj hd, hya', hyb'] at hQy
    linear_combination hQy
  have hBxy : polar Q (g (Pi.single a' 1)) (g (Pi.single b' 1)) = 0 := by
    rw [polar_map_of_mem hg.1, hi.polar_right, Pi.single_eq_of_ne hd.right_ne_left.symm]
  have hya : (g (Pi.single b' 1)) a = -((g (Pi.single a' 1)) b +
      polar Q (piW a a' b b' (g (Pi.single a' 1))) (piW a a' b b' (g (Pi.single b' 1)))) := by
    rw [polar_eq_coord hi hj hd, hxa', hxb', hya', hyb'] at hBxy
    linear_combination hBxy
  conv_lhs => rw [eq_coord hd (g (Pi.single b' 1))]
  rw [hya, hya', hyb, hyb', zero_smul, add_zero, one_smul]

theorem eq_of_rootRadical_triple (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g g' : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hg : g ∈ rootRadical Q hi.hypPair hj.hypPair) (hg' : g' ∈ rootRadical Q hi.hypPair hj.hypPair)
    (h1 : piW a a' b b' (g (Pi.single a' 1)) = piW a a' b b' (g' (Pi.single a' 1)))
    (h2 : piW a a' b b' (g (Pi.single b' 1)) = piW a a' b b' (g' (Pi.single b' 1)))
    (h3 : (g (Pi.single a' 1)) b = (g' (Pi.single a' 1)) b) : g = g' := by
  have hf₁ : g (Pi.single a' 1) = g' (Pi.single a' 1) := by
    rw [rootRadical_apply_f₁ hi hj hd hg, rootRadical_apply_f₁ hi hj hd hg', h1, h3]
  have hf₂ : g (Pi.single b' 1) = g' (Pi.single b' 1) := by
    rw [rootRadical_apply_f₂ hi hj hd hg, rootRadical_apply_f₂ hi hj hd hg', h1, h2, h3]
  have h₁₂ := hi.orth hj hd
  have hm : g⁻¹ * g' ∈ rootRadical Q hi.hypPair hj.hypPair := mul_mem (inv_mem hg) hg'
  have hm' := mem_rootRadical.mp hm
  have hfix : ∀ v, g v = g' v → (g⁻¹ * g') v = v := fun v hv => by
    rw [LinearEquiv.mul_apply, ← hv, LinearEquiv.inv_apply_apply']
  have hmem : g⁻¹ * g' ∈ rootRadical Q hi.hypPair hj.hypPair ⊓ rootLevi Q hi.hypPair hj.hypPair :=
    ⟨hm, mem_rootLevi_of_fix hm'.1 hm'.2.1 (hfix _ hf₁) hm'.2.2.1 (hfix _ hf₂)⟩
  rw [rootRadical_inf_rootLevi h₁₂, mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

end Radical

section Eichler

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

theorem IsHypCoord.polar_comm_left (h : IsHypCoord Q a a') (x : Fin d → K) :
    polar Q x (Pi.single a 1) = x a' := by rw [polar_comm, h.polar_left]

theorem IsHypCoord.polar_comm_right (h : IsHypCoord Q a a') (x : Fin d → K) :
    polar Q x (Pi.single a' 1) = x a := by rw [polar_comm, h.polar_right]

@[expose] noncomputable def eichlerTriple (Q : QuadraticForm K (Fin d → K)) (a b : Fin d)
    (w₁ w₂ : Fin d → K) (c : K) : (Fin d → K) ≃ₗ[K] (Fin d → K) :=
  eichler Q (Pi.single a 1) (w₁ + c • Pi.single b 1) * eichler Q (Pi.single b 1) w₂

variable (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b') (hd : PairDisjoint a a' b b')
include hi hj hd

omit hj in
theorem polar_eichlerTriple_left {w₁ : Fin d → K} (hw₁ : w₁ ∈ subW K a a' b b') (c : K) :
    polar Q (Pi.single a 1) (w₁ + c • Pi.single b 1) = 0 := by
  rw [hi.polar_left, Pi.add_apply, Pi.smul_apply, hw₁.1.2,
    Pi.single_eq_of_ne hd.left_ne_right.symm, smul_zero, add_zero]

theorem eichlerTriple_mem_rootRadical {w₁ w₂ : Fin d → K} (hw₁ : w₁ ∈ subW K a a' b b')
    (hw₂ : w₂ ∈ subW K a a' b b') (c : K) :
    eichlerTriple Q a b w₁ w₂ c ∈ rootRadical Q hi.hypPair hj.hypPair := by
  have h₁₂ := hi.orth hj hd
  refine mul_mem (eichler_mem_rootRadical_left h₁₂ (polar_eichlerTriple_left hi hd hw₁ c) ?_)
    (eichler_mem_rootRadical_right h₁₂ ?_ ?_)
  · change polar Q (Pi.single b 1) (w₁ + c • Pi.single b 1) = 0
    rw [hj.polar_left, Pi.add_apply, Pi.smul_apply, hw₁.2.2,
      Pi.single_eq_of_ne hj.ne.symm, smul_zero, add_zero]
  · change polar Q (Pi.single a 1) w₂ = 0
    rw [hi.polar_left, hw₂.1.2]
  · change polar Q (Pi.single b 1) w₂ = 0
    rw [hj.polar_left, hw₂.2.2]

theorem piW_eichler_left {y x : Fin d → K} (hy : polar Q (Pi.single a 1) y = 0)
    (hx : polar Q x (Pi.single a 1) = 0) :
    piW a a' b b' (eichler Q (Pi.single a 1) y x) = piW a a' b b' x := by
  rw [eichler_apply hi.map_left hy, hx, zero_smul, add_zero, sub_eq_add_neg, piW_add,
    ← neg_smul, piW_smul, piW_single_of_mem (Or.inl rfl) hd hi.ne hj.ne, smul_zero, add_zero]

omit hi in
theorem piW_eichler_right (hi' : IsHypCoord Q a a') {w x : Fin d → K}
    (hw : w ∈ subW K a a' b b') :
    piW a a' b b' (eichler Q (Pi.single b 1) w x) = piW a a' b b' x +
      polar Q x (Pi.single b 1) • w := by
  rw [eichler_apply hj.map_left (by rw [hj.polar_left, hw.2.2]), sub_eq_add_neg, piW_add,
    piW_add, ← neg_smul, piW_smul, piW_smul, piW_single_of_mem (Or.inr (Or.inr (Or.inl rfl))) hd
      hi'.ne hj.ne, smul_zero, add_zero, piW_eq_self hw]

omit hj in
theorem eichlerTriple_apply_f₁ {w₁ w₂ : Fin d → K} (hw₁ : w₁ ∈ subW K a a' b b')
    (hw₂ : w₂ ∈ subW K a a' b b') (c : K) :
    eichlerTriple Q a b w₁ w₂ c (Pi.single a' 1) = Pi.single a' 1 + (w₁ + c • Pi.single b 1) -
      Q (w₁ + c • Pi.single b 1) • Pi.single a 1 := by
  have h1 : polar Q (Pi.single a' 1) (Pi.single b 1) = 0 := by
    rw [hi.polar_right, Pi.single_eq_of_ne hd.left_ne_left.symm]
  have h2 : polar Q (Pi.single a' 1) w₂ = 0 := by rw [hi.polar_right, hw₂.1.1]
  have h3 : polar Q (Pi.single a' 1) (Pi.single a 1) = 1 := by
    rw [hi.polar_right, Pi.single_eq_same]
  have h4 : polar Q (Pi.single a' 1) (w₁ + c • Pi.single b 1) = 0 := by
    rw [hi.polar_right, Pi.add_apply, Pi.smul_apply, hw₁.1.1,
      Pi.single_eq_of_ne hd.left_ne_left.symm, smul_zero, add_zero]
  rw [eichlerTriple, LinearEquiv.mul_apply, eichler_apply_of_polar_eq_zero h1 h2,
    eichler_apply hi.map_left (polar_eichlerTriple_left hi hd hw₁ c), h3, h4]
  module

theorem eichlerTriple_triple {w₁ w₂ : Fin d → K} (hw₁ : w₁ ∈ subW K a a' b b')
    (hw₂ : w₂ ∈ subW K a a' b b') (c : K) :
    piW a a' b b' (eichlerTriple Q a b w₁ w₂ c (Pi.single a' 1)) = w₁ ∧
      piW a a' b b' (eichlerTriple Q a b w₁ w₂ c (Pi.single b' 1)) = w₂ ∧
      (eichlerTriple Q a b w₁ w₂ c (Pi.single a' 1)) b = c := by
  have hz : ∀ {i : Fin d}, (i = a ∨ i = a' ∨ i = b ∨ i = b') →
      piW a a' b b' (Pi.single i (1 : K)) = 0 := fun hi' => piW_single_of_mem hi' hd hi.ne hj.ne
  refine ⟨?_, ?_, ?_⟩
  · rw [eichlerTriple_apply_f₁ hi hd hw₁ hw₂, sub_eq_add_neg, ← neg_smul, piW_add, piW_add,
      piW_add, piW_smul, piW_smul, hz (Or.inr (Or.inl rfl)), hz (Or.inr (Or.inr (Or.inl rfl))),
      hz (Or.inl rfl), piW_eq_self hw₁, smul_zero, smul_zero, zero_add, add_zero, add_zero]
  · have hE₂e₁ : eichler Q (Pi.single b 1) w₂ (Pi.single a 1) = Pi.single a 1 :=
      eichler_apply_of_polar_eq_zero (by rw [hi.polar_left, Pi.single_eq_of_ne
        hd.left_ne_right.symm]) (by rw [hi.polar_left, hw₂.1.2])
    have hx : polar Q (eichler Q (Pi.single b 1) w₂ (Pi.single b' 1)) (Pi.single a 1) = 0 := by
      rw [← hE₂e₁, polar_map_of_mem (eichler_mem_orthogonalGroup Q _ _), hj.polar_right,
        Pi.single_eq_of_ne hd.left_ne_left]
    rw [eichlerTriple, LinearEquiv.mul_apply,
      piW_eichler_left hi hj hd (polar_eichlerTriple_left hi hd hw₁ c) hx,
      piW_eichler_right hj hd hi hw₂, hz (Or.inr (Or.inr (Or.inr rfl))), zero_add,
      hj.polar_comm_left, Pi.single_eq_same, one_smul]
  · have hw₁b : w₁ b = 0 := hw₁.2.1
    rw [eichlerTriple_apply_f₁ hi hd hw₁ hw₂]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hw₁b, Pi.single_eq_same,
      Pi.single_eq_of_ne hd.left_ne_right, Pi.single_eq_of_ne hd.left_ne_left, smul_eq_mul]
    ring

end Eichler

end CFSG.SeitzReduction.OmegaPilot

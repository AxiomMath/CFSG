module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Kind
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPieces
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

section Frame

variable {K : Type} [Field K] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin m → Fin d}

@[expose] def coordFrameVec (a b : Fin m → Fin d) (k : Fin m) (s : Bool) : Fin d → K :=
  cond s (Pi.single (a k) 1) (Pi.single (b k) 1)

@[simp] theorem coordFrameVec_true (k : Fin m) :
    coordFrameVec (K := K) a b k true = Pi.single (a k) 1 := rfl

@[simp] theorem coordFrameVec_false (k : Fin m) :
    coordFrameVec (K := K) a b k false = Pi.single (b k) 1 := rfl

theorem IsHypFrame.polar_coordFrameVec (h : IsHypFrame Q a b) (k : Fin m) (s : Bool)
    (v : Fin d → K) :
    polar Q (coordFrameVec a b k s) v = cond s (v (b k)) (v (a k)) := by
  cases s
  · exact (h.hyp k).polar_right v
  · exact (h.hyp k).polar_left v

theorem IsHypFrame.coordFrameVec_apply_left (h : IsHypFrame Q a b) (k l : Fin m) (s : Bool) :
    coordFrameVec (K := K) a b k s (a l) = if s ∧ k = l then 1 else 0 := by
  cases s
  · simp [Ne.symm (h.left_ne_right l k)]
  · by_cases hkl : k = l
    · subst hkl
      simp
    · have hne : a l ≠ a k := fun e => hkl (h.left_injective e).symm
      simp [hne, hkl]

theorem IsHypFrame.coordFrameVec_apply_right (h : IsHypFrame Q a b) (k l : Fin m) (s : Bool) :
    coordFrameVec (K := K) a b k s (b l) = if s = false ∧ k = l then 1 else 0 := by
  cases s
  · by_cases hkl : k = l
    · subst hkl
      simp
    · have hne : b l ≠ b k := fun e => hkl (h.right_injective e).symm
      simp [hne, hkl]
  · simp [h.left_ne_right k l]

@[expose] noncomputable def IsHypFrame.toHypFrame (h : IsHypFrame Q a b) (z : Fin d → K)
    (hz : IsUnit (Q z)) (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0) :
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
  exists_aux i j := ⟨z, hz, fun s => by
    rw [h.polar_coordFrameVec, h.polar_coordFrameVec]
    cases s <;> simp [hza, hzb]⟩

@[simp] theorem IsHypFrame.toHypFrame_vec (h : IsHypFrame Q a b) (z : Fin d → K)
    (hz : IsUnit (Q z)) (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0) :
    (h.toHypFrame z hz hza hzb).vec = coordFrameVec a b := rfl

theorem IsHypFrame.apply_eq_zero_of_polar (h : IsHypFrame Q a b) {v : Fin d → K}
    (hv : ∀ k r, polar Q v (coordFrameVec a b k r) = 0) (k : Fin m) :
    v (a k) = 0 ∧ v (b k) = 0 := by
  have h1 := hv k false
  have h2 := hv k true
  rw [polar_comm, h.polar_coordFrameVec] at h1 h2
  exact ⟨h1, h2⟩

end Frame

section Swap

variable {K : Type} [Field K] [CharP K 2] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin m → Fin d}

omit [CharP K 2] in
theorem IsHypFrame.pairDisjoint (h : IsHypFrame Q a b) {p p' : Fin m} (hpp : p ≠ p') :
    PairDisjoint (a p) (b p) (a p') (b p') :=
  ⟨fun e => hpp (h.left_injective e).symm, h.left_ne_right p' p, (h.left_ne_right p p').symm,
    fun e => hpp (h.right_injective e).symm⟩

theorem IsHypFrame.pairSwap_coordFrameVec (h : IsHypFrame Q a b) {p p' : Fin m} (hpp : p ≠ p')
    (k : Fin m) (r : Bool) :
    pairSwap Q (a p) (b p) (a p') (b p') (coordFrameVec a b k r) =
      coordFrameVec a b (Equiv.swap p p' k) r := by
  have hd := h.pairDisjoint hpp
  by_cases hkp : k = p
  · subst hkp
    rw [Equiv.swap_apply_left]
    obtain ⟨h1, h2⟩ := pairSwap_apply_left (h.hyp k) (h.hyp p') hd
    cases r
    · exact h2
    · exact h1
  by_cases hkp' : k = p'
  · subst hkp'
    rw [Equiv.swap_apply_right, pairSwap_comm]
    obtain ⟨h1, h2⟩ := pairSwap_apply_left (h.hyp k) (h.hyp p) hd.symm
    cases r
    · exact h2
    · exact h1
  rw [Equiv.swap_apply_of_ne_of_ne hkp hkp']
  have h1 : a k ≠ a p := fun e => hkp (h.left_injective e)
  have h2 : a k ≠ a p' := fun e => hkp' (h.left_injective e)
  have h3 : b k ≠ b p := fun e => hkp (h.right_injective e)
  have h4 : b k ≠ b p' := fun e => hkp' (h.right_injective e)
  have h5 : ∀ l, a k ≠ b l := fun l => h.left_ne_right k l
  have h6 : ∀ l, b k ≠ a l := fun l e => h.left_ne_right l k e.symm
  refine eichler_apply_of_polar_eq_zero ?_ ?_
  · rw [polar_add_right, h.polar_coordFrameVec, h.polar_coordFrameVec]
    cases r
    · simp [Pi.single_apply, h1, h2]
    · simp [Pi.single_apply, h6]
  · rw [polar_add_right, h.polar_coordFrameVec, h.polar_coordFrameVec]
    cases r
    · simp [Pi.single_apply, h5]
    · simp [Pi.single_apply, h3, h4]

omit [CharP K 2] in
theorem IsHypFrame.pairSwap_apply_of_vanish (h : IsHypFrame Q a b) {p p' : Fin m} {v : Fin d → K}
    (hap : v (a p) = 0) (hbp : v (b p) = 0) (hap' : v (a p') = 0) (hbp' : v (b p') = 0) :
    pairSwap Q (a p) (b p) (a p') (b p') v = v := by
  refine eichler_apply_of_polar_eq_zero ?_ ?_
  · rw [polar_comm, polar_add_left, (h.hyp p).polar_left, (h.hyp p').polar_left, hbp, hbp',
      add_zero]
  · rw [polar_comm, polar_add_left, (h.hyp p).polar_right, (h.hyp p').polar_right, hap, hap',
      add_zero]

end Swap

section Generation

variable {K : Type} [Field K] [CharP K 2] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin m → Fin d}

omit [CharP K 2] in
theorem IsHypFrame.coordFrameVec_vanish (h : IsHypFrame Q a b) {k l : Fin m} (hkl : k ≠ l)
    (r : Bool) : coordFrameVec (K := K) a b k r (a l) = 0 ∧ coordFrameVec (K := K) a b k r (b l) = 0 := by
  rw [h.coordFrameVec_apply_left, h.coordFrameVec_apply_right]
  simp [hkl]

theorem IsHypFrame.exists_conj_plane_zero (h : IsHypFrame Q a b) (hm : 3 ≤ m)
    {H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))}
    (h01 : pairSwap Q (a ⟨0, by omega⟩) (b ⟨0, by omega⟩) (a ⟨1, by omega⟩) (b ⟨1, by omega⟩) ∈ H)
    (h12 : pairSwap Q (a ⟨1, by omega⟩) (b ⟨1, by omega⟩) (a ⟨2, by omega⟩) (b ⟨2, by omega⟩) ∈ H)
    {j : Fin m} (hj : j ≠ ⟨0, by omega⟩) :
    ∃ l : Fin m, l ≠ ⟨0, by omega⟩ ∧ l ≠ j ∧ ∃ g ∈ H,
      g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (∀ r, g (coordFrameVec a b l r) = coordFrameVec a b ⟨0, by omega⟩ r) ∧
      (∀ r, g (coordFrameVec a b j r) = coordFrameVec a b j r) ∧
      ∀ v : Fin d → K, (∀ k, v (a k) = 0 ∧ v (b k) = 0) → g v = v := by
  set i0 : Fin m := ⟨0, by omega⟩
  set i1 : Fin m := ⟨1, by omega⟩
  set i2 : Fin m := ⟨2, by omega⟩
  have h01' : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h12' : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have h02' : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  set s₀₁ := pairSwap Q (a i0) (b i0) (a i1) (b i1)
  set s₁₂ := pairSwap Q (a i1) (b i1) (a i2) (b i2)
  have hO₀₁ : s₀₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := eichler_mem_orthogonalGroup Q _ _
  have hO₁₂ : s₁₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := eichler_mem_orthogonalGroup Q _ _
  have hv₀₁ : ∀ v : Fin d → K, (∀ k, v (a k) = 0 ∧ v (b k) = 0) → s₀₁ v = v := fun v hv =>
    h.pairSwap_apply_of_vanish (hv i0).1 (hv i0).2 (hv i1).1 (hv i1).2
  have hv₁₂ : ∀ v : Fin d → K, (∀ k, v (a k) = 0 ∧ v (b k) = 0) → s₁₂ v = v := fun v hv =>
    h.pairSwap_apply_of_vanish (hv i1).1 (hv i1).2 (hv i2).1 (hv i2).2
  by_cases hj1 : j = i1
  ·
    refine ⟨i2, h02'.symm, by rw [hj1]; exact h12'.symm, s₁₂ * s₀₁ * s₁₂,
      mul_mem (mul_mem h12 h01) h12, mul_mem (mul_mem hO₁₂ hO₀₁) hO₁₂, fun r => ?_,
      fun r => ?_, fun v hv => ?_⟩
    · simp only [LinearEquiv.mul_apply, s₀₁, s₁₂]
      rw [h.pairSwap_coordFrameVec h12', Equiv.swap_apply_right, h.pairSwap_coordFrameVec h01',
        Equiv.swap_apply_right, h.pairSwap_coordFrameVec h12',
        Equiv.swap_apply_of_ne_of_ne h01' h02']
    · subst hj1
      simp only [LinearEquiv.mul_apply, s₀₁, s₁₂]
      rw [h.pairSwap_coordFrameVec h12', Equiv.swap_apply_left, h.pairSwap_coordFrameVec h01',
        Equiv.swap_apply_of_ne_of_ne h02'.symm h12'.symm, h.pairSwap_coordFrameVec h12',
        Equiv.swap_apply_right]
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hv₁₂ v hv, hv₀₁ v hv, hv₁₂ v hv]
  ·
    refine ⟨i1, h01'.symm, Ne.symm hj1, s₀₁, h01, hO₀₁, fun r => ?_, fun r => ?_, hv₀₁⟩
    · rw [h.pairSwap_coordFrameVec h01', Equiv.swap_apply_right]
    · rw [h.pairSwap_coordFrameVec h01', Equiv.swap_apply_of_ne_of_ne hj hj1]

theorem IsHypFrame.elementaryGroup_le_of_pairSwap (h : IsHypFrame Q a b) (hm : 3 ≤ m)
    (z : Fin d → K) (hz : IsUnit (Q z)) (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0)
    (hrest : ∀ v : Fin d → K, (∀ k, v (a k) = 0 ∧ v (b k) = 0) → Q v = 0 → v = 0)
    {H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))}
    (hH : ∀ u w : Fin d → K, u (a ⟨0, by omega⟩) = 0 → u (b ⟨0, by omega⟩) = 0 →
      w (a ⟨0, by omega⟩) = 0 → w (b ⟨0, by omega⟩) = 0 → eichler Q u w ∈ H)
    (h01 : pairSwap Q (a ⟨0, by omega⟩) (b ⟨0, by omega⟩) (a ⟨1, by omega⟩) (b ⟨1, by omega⟩) ∈ H) :
    elementaryGroup Q ≤ H := by
  set i0 : Fin m := ⟨0, by omega⟩
  set i1 : Fin m := ⟨1, by omega⟩
  set i2 : Fin m := ⟨2, by omega⟩
  have h01' : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h12' : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have h02' : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : pairSwap Q (a i1) (b i1) (a i2) (b i2) ∈ H := by
    have e1 : a i0 ≠ a i1 := fun e => h01' (h.left_injective e)
    have e2 : a i0 ≠ a i2 := fun e => h02' (h.left_injective e)
    have e3 : b i0 ≠ a i1 := fun e => h.left_ne_right i1 i0 e.symm
    have e4 : b i0 ≠ a i2 := fun e => h.left_ne_right i2 i0 e.symm
    have e5 : a i0 ≠ b i1 := h.left_ne_right i0 i1
    have e6 : a i0 ≠ b i2 := h.left_ne_right i0 i2
    have e7 : b i0 ≠ b i1 := fun e => h01' (h.right_injective e)
    have e8 : b i0 ≠ b i2 := fun e => h02' (h.right_injective e)
    refine hH _ _ ?_ ?_ ?_ ?_
    · simp [e1, e2]
    · simp [e3, e4]
    · simp [e5, e6]
    · simp [e7, e8]
  have hconj : ∀ g ∈ H, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q → ∀ u w,
      eichler Q u w ∈ H → eichler Q (g u) (g w) ∈ H := fun g hg hgO u w huw => by
    rw [← eichler_conj hgO]
    exact mul_mem (mul_mem hg huw) (inv_mem hg)
  set F := h.toHypFrame z hz hza hzb
  refine F.elementaryGroup_le (fun {i j} hij s t c => ?_) (fun i s v hv => ?_)
    (fun v hv hv0 => hrest v (h.apply_eq_zero_of_polar hv) hv0)
  · simp only [F, IsHypFrame.toHypFrame_vec]
    by_cases hi : i = i0
    ·
      subst hi
      obtain ⟨l, hl0, hlj, g, hg, hgO, hgl, hgj, -⟩ :=
        h.exists_conj_plane_zero hm h01 h12 (Ne.symm hij)
      have h1 := hconj g hg hgO (coordFrameVec a b j t) (c • coordFrameVec a b l s)
        (hH _ _ (h.coordFrameVec_vanish (Ne.symm hij) t).1 (h.coordFrameVec_vanish (Ne.symm hij) t).2
          (by rw [Pi.smul_apply, (h.coordFrameVec_vanish hl0 s).1, smul_zero])
          (by rw [Pi.smul_apply, (h.coordFrameVec_vanish hl0 s).2, smul_zero]))
      rwa [hgj, map_smul, hgl] at h1
    by_cases hj : j = i0
    ·
      subst hj
      obtain ⟨l, hl0, hli, g, hg, hgO, hgl, hgi, -⟩ := h.exists_conj_plane_zero hm h01 h12 hi
      have h1 := hconj g hg hgO (coordFrameVec a b l t) (c • coordFrameVec a b i s)
        (hH _ _ (h.coordFrameVec_vanish hl0 t).1 (h.coordFrameVec_vanish hl0 t).2
          (by rw [Pi.smul_apply, (h.coordFrameVec_vanish hi s).1, smul_zero])
          (by rw [Pi.smul_apply, (h.coordFrameVec_vanish hi s).2, smul_zero]))
      rwa [hgl, map_smul, hgi] at h1
    · exact hH _ _ (h.coordFrameVec_vanish hj t).1 (h.coordFrameVec_vanish hj t).2
        (by rw [Pi.smul_apply, (h.coordFrameVec_vanish hi s).1, smul_zero])
        (by rw [Pi.smul_apply, (h.coordFrameVec_vanish hi s).2, smul_zero])
  · simp only [F, IsHypFrame.toHypFrame_vec] at hv ⊢
    have hv' := h.apply_eq_zero_of_polar hv
    by_cases hi : i = i0
    · subst hi
      obtain ⟨l, hl0, -, g, hg, hgO, hgl, -, hgv⟩ := h.exists_conj_plane_zero hm h01 h12 h01'.symm
      have h1 := hconj g hg hgO (coordFrameVec a b l s) v
        (hH _ _ (h.coordFrameVec_vanish hl0 s).1 (h.coordFrameVec_vanish hl0 s).2 (hv' i0).1
          (hv' i0).2)
      rwa [hgl, hgv v hv'] at h1
    · exact hH _ _ (h.coordFrameVec_vanish hi s).1 (h.coordFrameVec_vanish hi s).2 (hv' i0).1
        (hv' i0).2

theorem IsHypFrame.eq_top_of_pairPerpOf_le [Finite K] (h : IsHypFrame Q a b) (hm : 3 ≤ m)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (z : Fin d → K) (hz : IsUnit (Q z)) (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0)
    (hrest : ∀ v : Fin d → K, (∀ k, v (a k) = 0 ∧ v (b k) = 0) → Q v = 0 → v = 0)
    {T : Subgroup (matrixProjectiveDerived Q)}
    (hD : pairPerpOf Q (a ⟨0, by omega⟩) (b ⟨0, by omega⟩) ≤ T)
    (hs : projHom Q ⟨pairSwap Q (a ⟨0, by omega⟩) (b ⟨0, by omega⟩) (a ⟨1, by omega⟩)
      (b ⟨1, by omega⟩), pairSwap_mem_orthDerived hQ hT⟩ ∈ T) :
    T = ⊤ := by
  set i0 : Fin m := ⟨0, by omega⟩
  set H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    (T.comap (projHom Q)).map (orthDerived Q).subtype with hHdef
  have hEH : elementaryGroup Q ≤ H := by
    refine h.elementaryGroup_le_of_pairSwap hm z hz hza hzb hrest
      (fun u w hu hu' hw hw' => ?_) ⟨_, hs, rfl⟩
    refine ⟨⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩, hD ?_, rfl⟩
    refine ⟨⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩, mem_subgroupOf.2
      (mem_stabSub.2 ⟨?_, ?_⟩), rfl⟩
    · exact eichler_apply_of_polar_eq_zero (by rw [(h.hyp i0).polar_left, hu'])
        (by rw [(h.hyp i0).polar_left, hw'])
    · exact eichler_apply_of_polar_eq_zero (by rw [(h.hyp i0).polar_right, hu])
        (by rw [(h.hyp i0).polar_right, hw])
  have hΩ : orthDerived Q = elementaryGroup Q :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := projHom_surjective Q x
  have hy : (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ elementaryGroup Q := hΩ ▸ y.2
  obtain ⟨y', hy', hyy⟩ := hEH hy
  have : y' = y := Subtype.ext hyy
  rw [← this]
  exact hy'

end Generation

section Levi

variable {K : Type} [Field K] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin m → Fin d}

@[expose] noncomputable def frameRootElt (Q : QuadraticForm K (Fin d → K)) (a b : Fin m → Fin d)
    (p q : Fin m) (c : K) : (Fin d → K) ≃ₗ[K] (Fin d → K) :=
  eichler Q (Pi.single (a p) 1) (c • Pi.single (b q) 1)

theorem IsHypFrame.frameRootElt_apply (h : IsHypFrame Q a b) {p q : Fin m} (hpq : p ≠ q) (c : K)
    (x : Fin d → K) :
    frameRootElt Q a b p q c x =
      x + (c * x (b p)) • Pi.single (b q) 1 - (c * x (a q)) • Pi.single (a p) 1 := by
  have hpol : polar Q (Pi.single (a p) 1) (c • Pi.single (b q) 1) = 0 := by
    rw [(h.hyp p).polar_left, Pi.smul_apply,
      Pi.single_eq_of_ne (fun e => hpq (h.right_injective e)), smul_zero]
  rw [frameRootElt, eichler_apply (h.hyp p).map_left hpol, polar_comm, (h.hyp p).polar_left,
    polar_smul_right, polar_comm, (h.hyp q).polar_right, QuadraticMap.map_smul,
    (h.hyp q).map_right, smul_zero, zero_mul, add_zero, smul_smul, smul_eq_mul, mul_comm (x (b p))]

theorem IsHypFrame.polar_frameRoot (h : IsHypFrame Q a b) {p q : Fin m} (hpq : p ≠ q) (c : K) :
    polar Q (Pi.single (a p) 1) (c • Pi.single (b q) 1) = 0 := by
  rw [(h.hyp p).polar_left, Pi.smul_apply,
    Pi.single_eq_of_ne (fun e => hpq (h.right_injective e)), smul_zero]

theorem IsHypFrame.frameRootElt_mul (h : IsHypFrame Q a b) {p q : Fin m} (hpq : p ≠ q)
    (c c' : K) : frameRootElt Q a b p q c * frameRootElt Q a b p q c' =
      frameRootElt Q a b p q (c + c') := by
  rw [frameRootElt, frameRootElt, eichler_mul (h.polar_frameRoot hpq c) (h.polar_frameRoot hpq c'),
    frameRootElt, add_smul]

theorem IsHypFrame.frameRootElt_inv (h : IsHypFrame Q a b) {p q : Fin m} (hpq : p ≠ q) (c : K) :
    (frameRootElt Q a b p q c)⁻¹ = frameRootElt Q a b p q (-c) := by
  rw [frameRootElt, eichler_inv (h.polar_frameRoot hpq c), frameRootElt, neg_smul]

theorem IsHypFrame.frameLin_single_left (h : IsHypFrame Q a b) (t : Fin m → Kˣ) (k : Fin m) :
    frameLin a b t (Pi.single (a k) 1) = ((t k : Kˣ) : K) • Pi.single (a k) 1 := by
  funext i
  rw [frameLin_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = a k
  · subst hi
    rw [h.frameEntry_left]
  · rw [Pi.single_eq_of_ne hi, mul_zero, mul_zero]

theorem IsHypFrame.frameLin_single_right (h : IsHypFrame Q a b) (t : Fin m → Kˣ) (k : Fin m) :
    frameLin a b t (Pi.single (b k) 1) = (((t k)⁻¹ : Kˣ) : K) • Pi.single (b k) 1 := by
  funext i
  rw [frameLin_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = b k
  · subst hi
    rw [h.frameEntry_right]
  · rw [Pi.single_eq_of_ne hi, mul_zero, mul_zero]

theorem IsHypFrame.frameLin_conj_frameRootElt (h : IsHypFrame Q a b) (t : Fin m → Kˣ)
    (p q : Fin m) (c : K) :
    frameLin a b t * frameRootElt Q a b p q c * (frameLin a b t)⁻¹ =
      frameRootElt Q a b p q ((t p : K) * ((t q)⁻¹ : Kˣ) * c) := by
  rw [frameRootElt, eichler_conj (h.frameLin_mem_orthogonalGroup t), map_smul,
    h.frameLin_single_left, h.frameLin_single_right, eichler_smul_left, smul_smul, smul_smul,
    frameRootElt]
  congr 2
  ring

@[expose] noncomputable def frameLeviTorus (a b : Fin m → Fin d) (p q : Fin m) :
    Kˣ →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  (frameLin a b).comp ((MonoidHom.mulSingle (fun _ : Fin m => Kˣ) p).comp (MonoidHom.id Kˣ) *
    (MonoidHom.mulSingle (fun _ : Fin m => Kˣ) q).comp (MonoidHom.id Kˣ)⁻¹)

theorem frameLeviTorus_apply (a b : Fin m → Fin d) (p q : Fin m) (μ : Kˣ) :
    frameLeviTorus (K := K) a b p q μ = frameLin a b (Pi.mulSingle p μ * Pi.mulSingle q μ⁻¹) :=
  rfl

@[expose] noncomputable def frameLeviSL (Q : QuadraticForm K (Fin d → K)) (a b : Fin m → Fin d)
    (p q : Fin m) : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  Subgroup.closure (Set.range (frameRootElt Q a b q p) ∪ Set.range (frameRootElt Q a b p q) ∪
    Set.range (frameLeviTorus a b p q))

theorem IsHypFrame.frameRootElt_apply_coord (h : IsHypFrame Q a b) {p q : Fin m} (hpq : p ≠ q)
    (c : K) (x : Fin d → K) (j : Fin d) :
    frameRootElt Q a b p q c x j =
      if j = a p then x (a p) - c * x (a q) else if j = b q then x (b q) + c * x (b p) else x j := by
  rw [h.frameRootElt_apply hpq]
  have hne : a p ≠ b q := h.left_ne_right p q
  by_cases h1 : j = a p
  · subst h1
    simp [hne]
  · by_cases h2 : j = b q
    · subst h2
      simp [Ne.symm hne]
    · simp [h1, h2]

theorem IsHypFrame.pairSwap_apply_coord [CharP K 2] (h : IsHypFrame Q a b) {p q : Fin m}
    (hpq : p ≠ q) (x : Fin d → K) (j : Fin d) :
    pairSwap Q (a p) (b p) (a q) (b q) x j =
      if j = a p then x (a q) else if j = a q then x (a p) else if j = b p then x (b q)
        else if j = b q then x (b p) else x j := by
  have hd := h.pairDisjoint hpq
  obtain ⟨hu, hw⟩ := pairSwap_hyp (h.hyp p) (h.hyp q) hd
  have hQw := pairSwap_hyp_right (h.hyp p) (h.hyp q) hd
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pairSwap, eichler_apply hu hw, hQw, zero_mul, add_zero, polar_comm, polar_add_left,
    (h.hyp p).polar_left, (h.hyp q).polar_left, polar_comm, polar_add_left, (h.hyp p).polar_right,
    (h.hyp q).polar_right]
  have e1 : a p ≠ a q := fun e => hpq (h.left_injective e)
  have e2 : b p ≠ b q := fun e => hpq (h.right_injective e)
  have e3 : ∀ k l, a k ≠ b l := h.left_ne_right
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases j1 : j = a p
  · subst j1
    simp [e1, e3]
    linear_combination (-x (a q)) * htwo
  by_cases j2 : j = a q
  · subst j2
    simp [Ne.symm e1, e3]
    linear_combination (-x (a p)) * htwo
  by_cases j3 : j = b p
  · subst j3
    simp [e2, fun k => Ne.symm (e3 k p)]
    linear_combination x (b p) * htwo
  by_cases j4 : j = b q
  · subst j4
    simp [Ne.symm e2, fun k => Ne.symm (e3 k q)]
    linear_combination x (b q) * htwo
  · simp [j1, j2, j3, j4]

theorem IsHypFrame.pairSwap_eq_frameRootElt [CharP K 2] (h : IsHypFrame Q a b) {p q : Fin m}
    (hpq : p ≠ q) :
    pairSwap Q (a p) (b p) (a q) (b q) =
      frameRootElt Q a b q p 1 * frameRootElt Q a b p q 1 * frameRootElt Q a b q p 1 := by
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  have e1 : a p ≠ a q := fun e => hpq (h.left_injective e)
  have e2 : b p ≠ b q := fun e => hpq (h.right_injective e)
  have e3 : ∀ k l, a k ≠ b l := h.left_ne_right
  refine LinearEquiv.ext fun x => funext fun j => ?_
  simp only [LinearEquiv.mul_apply, h.frameRootElt_apply_coord hpq,
    h.frameRootElt_apply_coord (Ne.symm hpq), h.pairSwap_apply_coord hpq, one_mul]
  have e4 : ∀ k l, b l ≠ a k := fun k l => Ne.symm (e3 k l)
  simp only [e1, Ne.symm e1, e2, Ne.symm e2, e3, e4, ite_false, ite_true]
  by_cases j1 : j = a p
  · subst j1
    simp only [e1, e3, ite_true, ite_false]
    linear_combination (x (a q) - x (a p)) * htwo
  by_cases j2 : j = a q
  · subst j2
    simp only [Ne.symm e1, e3, ite_true, ite_false]
    linear_combination (2 * x (a p) - x (a q)) * htwo
  by_cases j3 : j = b p
  · subst j3
    simp only [e2, e4, ite_true, ite_false]
    linear_combination (-x (b p) - x (b q)) * htwo
  by_cases j4 : j = b q
  · subst j4
    simp only [Ne.symm e2, e4, ite_true, ite_false]
    linear_combination (-x (b q)) * htwo
  · simp only [j1, j2, j3, j4, ite_false]

theorem frameRootElt_mem_frameLeviSL_left (p q : Fin m) (c : K) :
    frameRootElt Q a b q p c ∈ frameLeviSL Q a b p q :=
  Subgroup.subset_closure (Or.inl (Or.inl ⟨c, rfl⟩))

theorem frameRootElt_mem_frameLeviSL_right (p q : Fin m) (c : K) :
    frameRootElt Q a b p q c ∈ frameLeviSL Q a b p q :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨c, rfl⟩))

theorem frameLeviTorus_mem_frameLeviSL (p q : Fin m) (μ : Kˣ) :
    frameLeviTorus a b p q μ ∈ frameLeviSL Q a b p q :=
  Subgroup.subset_closure (Or.inr ⟨μ, rfl⟩)

theorem IsHypFrame.pairSwap_mem_frameLeviSL [CharP K 2] (h : IsHypFrame Q a b) {p q : Fin m}
    (hpq : p ≠ q) : pairSwap Q (a p) (b p) (a q) (b q) ∈ frameLeviSL Q a b p q := by
  rw [h.pairSwap_eq_frameRootElt hpq]
  exact mul_mem (mul_mem (frameRootElt_mem_frameLeviSL_left p q 1)
    (frameRootElt_mem_frameLeviSL_right p q 1)) (frameRootElt_mem_frameLeviSL_left p q 1)

theorem mulSingle_mul_mulSingle_inv_left {p q : Fin m} (hpq : p ≠ q) (μ : Kˣ) :
    (Pi.mulSingle p μ * Pi.mulSingle q μ⁻¹ : Fin m → Kˣ) p = μ := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hpq, mul_one]

theorem mulSingle_mul_mulSingle_inv_right {p q : Fin m} (hpq : p ≠ q) (μ : Kˣ) :
    (Pi.mulSingle p μ * Pi.mulSingle q μ⁻¹ : Fin m → Kˣ) q = μ⁻¹ := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hpq), one_mul]

theorem IsHypFrame.pairSwap_conj_frameLeviTorus [CharP K 2] (h : IsHypFrame Q a b) {p q : Fin m}
    (hpq : p ≠ q) (ν : Kˣ) :
    pairSwap Q (a p) (b p) (a q) (b q) * frameLeviTorus a b p q ν *
      (pairSwap Q (a p) (b p) (a q) (b q))⁻¹ = (frameLeviTorus a b p q ν)⁻¹ := by
  have hd := h.pairDisjoint hpq
  set s := pairSwap Q (a p) (b p) (a q) (b q)
  have h1 : s * torusLin (a p) (b p) ν * s⁻¹ = torusLin (a q) (b q) ν :=
    pairSwap_conj_torusLin (h.hyp p) (h.hyp q) hd ν
  have h2 : s * torusLin (a q) (b q) ν⁻¹ * s⁻¹ = torusLin (a p) (b p) ν⁻¹ := by
    have := pairSwap_conj_torusLin (h.hyp q) (h.hyp p) hd.symm ν⁻¹
    rwa [pairSwap_comm] at this
  have hsplit : frameLeviTorus a b p q ν = torusLin (a p) (b p) ν * torusLin (a q) (b q) ν⁻¹ := by
    rw [frameLeviTorus_apply, map_mul, frameLin_mulSingle, frameLin_mulSingle]
  have hinv : (frameLeviTorus a b p q ν)⁻¹ =
      torusLin (a q) (b q) ν * torusLin (a p) (b p) ν⁻¹ := by
    rw [frameLeviTorus_apply, ← map_inv, mul_inv, ← Pi.mulSingle_inv, ← Pi.mulSingle_inv, inv_inv,
      mul_comm, map_mul, frameLin_mulSingle, frameLin_mulSingle]
  rw [hinv, hsplit, ← h1, ← h2]
  group

theorem IsHypFrame.commutator_frameLeviSL [Finite K] [CharP K 2] (h : IsHypFrame Q a b)
    {p q : Fin m} (hpq : p ≠ q) (hK : 4 ≤ Nat.card K) :
    ⁅frameLeviSL Q a b p q, frameLeviSL Q a b p q⁆ = frameLeviSL Q a b p q := by
  set Y := frameLeviSL Q a b p q
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  obtain ⟨lam, hlam⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hK
  have hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ ⁅Y, Y⁆ := fun x hx y hy => by
    have := Subgroup.commutator_mem_commutator hx hy
    rwa [commutatorElement_def] at this
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ((⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨μ, rfl⟩)
  ·
    set μ₀ : K := ((lam⁻¹ : Kˣ) : K) * ((lam⁻¹ : Kˣ) : K) - 1 with hμ₀
    have hμ0 : μ₀ ≠ 0 := by
      intro h0
      apply hlam
      have h1 : ((lam⁻¹ * lam⁻¹ : Kˣ) : K) = 1 := by
        rw [Units.val_mul]
        linear_combination h0
      have h2 : lam⁻¹ * lam⁻¹ = 1 := Units.ext h1
      rw [← mul_inv, inv_eq_one] at h2
      exact h2
    have key : frameLeviTorus a b p q lam * frameRootElt Q a b q p (μ₀⁻¹ * c) *
        (frameLeviTorus a b p q lam)⁻¹ * (frameRootElt Q a b q p (μ₀⁻¹ * c))⁻¹ =
        frameRootElt Q a b q p c := by
      rw [frameLeviTorus_apply, h.frameLin_conj_frameRootElt, h.frameRootElt_inv (Ne.symm hpq),
        h.frameRootElt_mul (Ne.symm hpq), mulSingle_mul_mulSingle_inv_left hpq,
        mulSingle_mul_mulSingle_inv_right hpq]
      congr 1
      field_simp
      ring
    rw [← key]
    exact hcomm _ (frameLeviTorus_mem_frameLeviSL p q lam) _
      (frameRootElt_mem_frameLeviSL_left p q _)
  ·
    set μ₀ : K := (lam : K) * (lam : K) - 1 with hμ₀
    have hμ0 : μ₀ ≠ 0 := by
      intro h0
      apply hlam
      apply Units.ext
      rw [Units.val_mul, Units.val_one]
      linear_combination h0
    have key : frameLeviTorus a b p q lam * frameRootElt Q a b p q (μ₀⁻¹ * c) *
        (frameLeviTorus a b p q lam)⁻¹ * (frameRootElt Q a b p q (μ₀⁻¹ * c))⁻¹ =
        frameRootElt Q a b p q c := by
      rw [frameLeviTorus_apply, h.frameLin_conj_frameRootElt, h.frameRootElt_inv hpq,
        h.frameRootElt_mul hpq, mulSingle_mul_mulSingle_inv_left hpq,
        mulSingle_mul_mulSingle_inv_right hpq, inv_inv]
      congr 1
      field_simp
      ring
    rw [← key]
    exact hcomm _ (frameLeviTorus_mem_frameLeviSL p q lam) _
      (frameRootElt_mem_frameLeviSL_right p q _)
  ·
    obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (μ : K)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact μ.ne_zero hc
    set ν : Kˣ := Units.mk0 c hc0
    have hνμ : ν * ν = μ := Units.ext (by rw [Units.val_mul, Units.val_mk0, hc])
    have key : frameLeviTorus a b p q ν * pairSwap Q (a p) (b p) (a q) (b q) *
        (frameLeviTorus a b p q ν)⁻¹ * (pairSwap Q (a p) (b p) (a q) (b q))⁻¹ =
        frameLeviTorus a b p q μ := by
      have h1 : pairSwap Q (a p) (b p) (a q) (b q) * (frameLeviTorus a b p q ν)⁻¹ *
          (pairSwap Q (a p) (b p) (a q) (b q))⁻¹ = frameLeviTorus a b p q ν := by
        have h2 := h.pairSwap_conj_frameLeviTorus hpq ν
        have h3 : pairSwap Q (a p) (b p) (a q) (b q) * (frameLeviTorus a b p q ν)⁻¹ *
            (pairSwap Q (a p) (b p) (a q) (b q))⁻¹ = (pairSwap Q (a p) (b p) (a q) (b q) *
              frameLeviTorus a b p q ν * (pairSwap Q (a p) (b p) (a q) (b q))⁻¹)⁻¹ := by group
        rw [h3, h2, inv_inv]
      calc frameLeviTorus a b p q ν * pairSwap Q (a p) (b p) (a q) (b q) *
            (frameLeviTorus a b p q ν)⁻¹ * (pairSwap Q (a p) (b p) (a q) (b q))⁻¹
          = frameLeviTorus a b p q ν * (pairSwap Q (a p) (b p) (a q) (b q) *
            (frameLeviTorus a b p q ν)⁻¹ * (pairSwap Q (a p) (b p) (a q) (b q))⁻¹) := by group
        _ = frameLeviTorus a b p q ν * frameLeviTorus a b p q ν := by rw [h1]
        _ = frameLeviTorus a b p q μ := by rw [← map_mul, hνμ]
    rw [← key]
    exact hcomm _ (frameLeviTorus_mem_frameLeviSL p q ν) _ (h.pairSwap_mem_frameLeviSL hpq)

theorem IsHypFrame.frameLeviSL_le_centralizer (h : IsHypFrame Q a b) (p q : Fin m) :
    frameLeviSL Q a b p q ≤
      centralizer ((frameLin a b) '' {t : Fin m → Kˣ | t p = t q}) := by
  refine (Subgroup.closure_le _).2 ?_
  have hroot : ∀ p' q' : Fin m, ∀ t : Fin m → Kˣ, t p' = t q' → ∀ c : K,
      frameLin a b t * frameRootElt Q a b p' q' c = frameRootElt Q a b p' q' c * frameLin a b t := by
    intro p' q' t ht c
    have h1 := h.frameLin_conj_frameRootElt t p' q' c
    rw [ht, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
    calc frameLin a b t * frameRootElt Q a b p' q' c
        = frameLin a b t * frameRootElt Q a b p' q' c * (frameLin a b t)⁻¹ * frameLin a b t := by
          group
      _ = frameRootElt Q a b p' q' c * frameLin a b t := by rw [h1]
  rintro _ ((⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨μ, rfl⟩) <;> rw [SetLike.mem_coe, mem_centralizer_iff] <;>
    rintro _ ⟨t, ht, rfl⟩
  · exact hroot q p t ht.symm c
  · exact hroot p q t ht c
  · rw [frameLeviTorus_apply, ← map_mul, ← map_mul, mul_comm]

theorem IsHypFrame.frameLeviSL_le_orthDerived [Finite K] [CharP K 2] (h : IsHypFrame Q a b)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (p q : Fin m) : frameLeviSL Q a b p q ≤ orthDerived Q := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ((⟨c, rfl⟩ | ⟨c, rfl⟩) | ⟨μ, rfl⟩)
  · exact eichler_mem_orthDerived hQ hT _ _
  · exact eichler_mem_orthDerived hQ hT _ _
  · exact h.frameLin_mem_orthDerived _

end Levi

section Minus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (minusIndexEquiv
  coordinateQuadMinus coordinateQuadMinus_apply regular_coordinateQuadMinus)

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def minusAnisoVec (hn : 1 ≤ n) : Fin (2 * n) → K :=
  Pi.single (minusIndexEquiv n hn (.inr (.inr 0))) 1

theorem coordinateQuadMinus_minusAnisoVec (hn : 1 ≤ n) (b c : K) :
    coordinateQuadMinus n K hn b c (minusAnisoVec hn) = 1 := by
  rw [coordinateQuadMinus_apply, minusAnisoVec]
  simp [(minusIndexEquiv n hn).injective.eq_iff]

theorem minusAnisoVec_frameLeft (hn : 1 ≤ n) (k : Fin (n - 1)) :
    minusAnisoVec (K := K) hn (minusFrameLeft hn k) = 0 := by
  simp [minusAnisoVec, minusFrameLeft, (minusIndexEquiv n hn).injective.eq_iff]

theorem minusAnisoVec_frameRight (hn : 1 ≤ n) (k : Fin (n - 1)) :
    minusAnisoVec (K := K) hn (minusFrameRight hn k) = 0 := by
  simp [minusAnisoVec, minusFrameRight, (minusIndexEquiv n hn).injective.eq_iff]

theorem eq_zero_of_frame_vanish_minus (hn : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (v : Fin (2 * n) → K)
    (hv : ∀ k, v (minusFrameLeft hn k) = 0 ∧ v (minusFrameRight hn k) = 0)
    (hQ : coordinateQuadMinus n K hn b c v = 0) : v = 0 := by
  have hsum : ∑ i, v (minusIndexEquiv n hn (.inl i)) * v (minusIndexEquiv n hn (.inr (.inl i))) =
      0 := Finset.sum_eq_zero fun i _ => by
    rw [show v (minusIndexEquiv n hn (.inl i)) = 0 from (hv i).1, zero_mul]
  rw [coordinateQuadMinus_apply, hsum, zero_add] at hQ
  set x := v (minusIndexEquiv n hn (.inr (.inr 0)))
  set y := v (minusIndexEquiv n hn (.inr (.inr 1)))
  have hy : y = 0 := by
    by_contra hy
    apply hirr (x / y)
    field_simp
    linear_combination hQ
  have hx : x = 0 := by
    rw [hy] at hQ
    simpa using hQ
  funext j
  obtain ⟨i, rfl⟩ := (minusIndexEquiv n hn).surjective j
  rcases i with i | i | i
  · exact (hv i).1
  · exact (hv i).2
  · fin_cases i
    · exact hx
    · exact hy

theorem eq_top_of_minusPairPerp_le [Finite K] [CharP K 2] (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {T : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))}
    (hD : minusPairPerp (by omega) b c ⟨0, by omega⟩ ≤ T)
    (hs : projHom _ ⟨pairSwap (coordinateQuadMinus n K (by omega) b c)
      (minusFrameLeft (by omega) ⟨0, by omega⟩) (minusFrameRight (by omega) ⟨0, by omega⟩)
      (minusFrameLeft (by omega) ⟨1, by omega⟩) (minusFrameRight (by omega) ⟨1, by omega⟩),
      pairSwap_mem_orthDerived (regular_coordinateQuadMinus n K b c hn hirr).1
        (regular_coordinateQuadMinus n K b c hn hirr).2⟩ ∈ T) :
    T = ⊤ := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  exact (isHypFrame_minus K hn1 b c).eq_top_of_pairPerpOf_le (by omega) hQ hT (minusAnisoVec hn1)
    (by rw [coordinateQuadMinus_minusAnisoVec]; exact isUnit_one) (minusAnisoVec_frameLeft hn1)
    (minusAnisoVec_frameRight hn1) (eq_zero_of_frame_vanish_minus hn1 hirr) hD hs

end Minus

section LeviProj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d m : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin m → Fin d}

@[expose] noncomputable def frameLeviProj (Q : QuadraticForm K (Fin d → K)) (a b : Fin m → Fin d)
    (p q : Fin m) : Subgroup (matrixProjectiveDerived Q) :=
  ((frameLeviSL Q a b p q).subgroupOf (orthDerived Q)).map (projHom Q)

theorem IsHypFrame.commutator_frameLeviProj (h : IsHypFrame Q a b) {p q : Fin m} (hpq : p ≠ q)
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ⁅frameLeviProj Q a b p q, frameLeviProj Q a b p q⁆ = frameLeviProj Q a b p q := by
  rw [frameLeviProj, ← Subgroup.map_commutator,
    commutator_subgroupOf_eq_of_le_perfect (h.frameLeviSL_le_orthDerived hQ hT p q)
      (h.commutator_frameLeviSL hpq hK)]

theorem IsHypFrame.frameLeviProj_le_centralizer (h : IsHypFrame Q a b) {p q : Fin m}
    {J : Finset (Fin m)} (hp : p ∈ J) (hq : q ∈ J) :
    frameLeviProj Q a b p q ≤ centralizer (frameTorusOf Q a b (levelParam J) : Set _) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_iff]
  intro z hz
  rw [h.frameTorusOf_eq_map] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  rw [IsHypFrame.frameHom_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hyc := mem_centralizer_iff.1 (h.frameLeviSL_le_centralizer p q (mem_subgroupOf.1 hy))
    (frameLin a b t) ⟨t, ht p hp q hq, rfl⟩
  exact hyc

omit [Finite K] in
theorem IsHypFrame.projHom_pairSwap_mem_frameLeviProj (h : IsHypFrame Q a b) {p q : Fin m}
    (hpq : p ≠ q) (hs : pairSwap Q (a p) (b p) (a q) (b q) ∈ orthDerived Q) :
    projHom Q ⟨_, hs⟩ ∈ frameLeviProj Q a b p q :=
  ⟨⟨_, hs⟩, mem_subgroupOf.2 (h.pairSwap_mem_frameLeviSL hpq), rfl⟩

end LeviProj

end CFSG.SeitzReduction.OmegaPilot

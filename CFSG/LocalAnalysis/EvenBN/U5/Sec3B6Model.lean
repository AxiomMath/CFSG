module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3EModel

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

section Coordinates

@[expose] def crd (g : hypSU h 2 1) : Fin 2 → K := fun i => mat g (.inl i) (.inr (.inl 0))

theorem crd_of_mat {g : hypSU h 2 1} {x : Fin 2 → K} {C : Matrix (Fin 2) (Fin 2) K}
    (hg : mat g = oddUni h x C) : crd g = x :=
  funext fun i => by rw [crd, hg, oddUni_apply_ez]

theorem crd_mul {g g' : hypSU h 2 1} (hg : g ∈ Ssub h) (hg' : g' ∈ Ssub h) :
    crd (g * g') = crd g + crd g' := by
  obtain ⟨-, x, C, hgC⟩ := hg
  obtain ⟨-, x', C', hgC'⟩ := hg'
  rw [crd_of_mat (by rw [mat_mul, hgC, hgC', oddUni_mul]), crd_of_mat hgC, crd_of_mat hgC']

theorem crd_eq_zero_iff {g : hypSU h 2 1} (hg : g ∈ Ssub h) : crd g = 0 ↔ g ∈ Vsub h := by
  rw [mem_Vsub_iff hg, funext_iff]
  rfl

theorem exists_Ssub_crd (h : UnitaryFieldData 2 f K) (v : Fin 2 → K) :
    ∃ g ∈ Ssub h, crd g = v := by
  have := h.charP
  obtain ⟨c₀, hc₀⟩ := trace_surj (hK := h) (a := v 0 * h.bar (v 0))
    (by rw [map_mul, h.bar_bar, mul_comm])
  obtain ⟨c₁, hc₁⟩ := trace_surj (hK := h) (a := v 1 * h.bar (v 1))
    (by rw [map_mul, h.bar_bar, mul_comm])
  obtain ⟨g, hg, hgm⟩ := exists_mem_Ssub (hK := h) (x := v)
    (C := !![c₀, v 0 * h.bar (v 1); 0, c₁]) (by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [vecMulVec, hc₀, CharTwo.neg_eq]
      · simp [vecMulVec, CharTwo.neg_eq]
      · simp [vecMulVec, h.bar_bar, CharTwo.neg_eq, mul_comm]
      · simp [vecMulVec, hc₁, CharTwo.neg_eq])
  exact ⟨g, hg, crd_of_mat hgm⟩

theorem crd_lev (B : SpecialLinearGroup (Fin 2) K) {g : hypSU h 2 1} (hg : g ∈ Ssub h) :
    crd (lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K)
        (by rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one) * g *
        (lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K)
          (by rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one))⁻¹) =
      (B : Matrix (Fin 2) (Fin 2) K) *ᵥ crd g := by
  obtain ⟨-, x, C, hgC⟩ := hg
  rw [crd_of_mat (lev_conj _ _ hgC), crd_of_mat hgC, Matrix.SpecialLinearGroup.det_coe,
    map_one, div_one, inv_one, one_smul]

end Coordinates

section Semilinear

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

theorem isHerm_e₂₂ (h : UnitaryFieldData 2 f K) :
    IsHerm h (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) := by
  have := h.charP
  ext i j; fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

theorem oddUni_zero_row (Y : Matrix (Fin 2) (Fin 2) K) {a : HypIndex 2 1}
    (ha₁ : a ≠ ιe₁) (ha₂ : a ≠ ιe₂) (b : HypIndex 2 1) :
    oddUni h 0 Y a b = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b := by
  rcases a with i | m | i
  · fin_cases i
    · exact absurd rfl ha₁
    · exact absurd rfl ha₂
  · fin_cases m
    rcases b with j | l | j
    · simp [oddUni]
    · fin_cases l
      simp [oddUni]
    · simp [oddUni]
  · rcases b with j | l | j
    · simp [oddUni]
    · simp [oddUni]
    · simp [oddUni, Matrix.one_apply]

theorem oddUni_zero_mul_apply (Y : Matrix (Fin 2) (Fin 2) K)
    (M : Matrix (HypIndex 2 1) (HypIndex 2 1) K) {a : HypIndex 2 1} (ha₁ : a ≠ ιe₁)
    (ha₂ : a ≠ ιe₂) (b : HypIndex 2 1) : (oddUni h 0 Y * M) a b = M a b := by
  rw [Matrix.mul_apply]
  simp only [oddUni_zero_row Y ha₁ ha₂]
  rw [← Matrix.mul_apply, Matrix.one_mul]

@[expose] def pblk (x : Gam h) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => lmat x (.inl i) (.inl j)

theorem map_mat_vSU_e₂₂ (σ : K ≃+* K) :
    (mat (vSU h !![0, 0; 0, 1] (isHerm_e₂₂ h))).map σ = 1 + Matrix.single ιe₂ ιf₂ 1 := by
  rw [mat_vSU]
  ext a b
  rcases a with i | m | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;> (try fin_cases m) <;> (try fin_cases l) <;>
    simp [oddUni]

theorem lmat_col_plane {x : Gam h} (h₁ : actΓ h x (z₁SU h) ∈ Vsub h)
    (h₂ : actΓ h x (vSU h !![0, 0; 0, 1] (isHerm_e₂₂ h)) ∈ Vsub h) {a : HypIndex 2 1}
    (ha₁ : a ≠ ιe₁) (ha₂ : a ≠ ιe₂) : lmat x a ιe₁ = 0 ∧ lmat x a ιe₂ = 0 := by
  constructor
  · have hrel := congrFun (congrFun (lmat_mul_map x (z₁SU h)) a) ιf₁
    obtain ⟨-, Y, hY⟩ := h₁
    have hz : (mat (z₁SU h)).map x.1.right = 1 + Matrix.single ιe₁ ιf₁ 1 := by
      rw [mat_eq_of_mem_ZPsub z₁SU_mem_ZPsub, mat_z₁SU_e₁f₁, map_one_add_single', map_one]
    rw [hz, mul_one_add_single_apply_f₁, mul_one, hY, oddUni_zero_mul_apply Y _ ha₁ ha₂] at hrel
    linear_combination hrel
  · have hrel := congrFun (congrFun (lmat_mul_map x (vSU h !![0, 0; 0, 1] (isHerm_e₂₂ h))) a)
      ιf₂
    obtain ⟨-, Y, hY⟩ := h₂
    rw [map_mat_vSU_e₂₂, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, mul_single_apply_same,
      mul_one, hY, oddUni_zero_mul_apply Y _ ha₁ ha₂] at hrel
    linear_combination hrel

theorem det_pblk_ne_zero {x : Gam h}
    (hcol : ∀ a, a ≠ ιe₁ → a ≠ ιe₂ → lmat x a ιe₁ = 0 ∧ lmat x a ιe₂ = 0) :
    (pblk x).det ≠ 0 := by
  intro h0
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  set w : HypIndex 2 1 → K := Sum.elim u fun _ => 0 with hw
  have hAw : lmat x *ᵥ w = 0 := by
    funext a
    rw [Matrix.mulVec, dotProduct, sum_hypIndex_two]
    simp only [hw, Sum.elim_inl, Sum.elim_inr, mul_zero, add_zero, Pi.zero_apply]
    by_cases ha₁ : a = ιe₁
    · subst ha₁
      have := congrFun hu 0
      simpa [pblk, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    by_cases ha₂ : a = ιe₂
    · subst ha₂
      have := congrFun hu 1
      simpa [pblk, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    obtain ⟨c1, c2⟩ := hcol a ha₁ ha₂
    change lmat x a ιe₁ * u 0 + lmat x a ιe₂ * u 1 = 0
    rw [c1, c2, zero_mul, zero_mul, add_zero]
  have hw0 : w = 0 := by
    have hinv := (lmat_mul_inv x).2
    calc w = (((x.1.left⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *
          lmat x) *ᵥ w := by rw [hinv, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hAw, Matrix.mulVec_zero]
  apply hu0
  funext i
  have := congrFun hw0 (.inl i)
  simpa [hw] using this

theorem exists_sim_apply (x : Gam h) : ∃ μ : K, μ ≠ 0 ∧ ∀ a b : HypIndex 2 1,
    h.bar (lmat x ιf₁ a) * lmat x ιe₁ b + h.bar (lmat x ιf₂ a) * lmat x ιe₂ b +
      h.bar (lmat x ιz a) * lmat x ιz b + h.bar (lmat x ιe₁ a) * lmat x ιf₁ b +
        h.bar (lmat x ιe₂ a) * lmat x ιf₂ b = μ * hypGram 2 1 K a b := by
  obtain ⟨μ, hμ0, -, hsim⟩ := x.2
  refine ⟨μ, hμ0, fun a b => ?_⟩
  have g := congrFun (congrFun hsim a) b
  change (((lmat x).map h.bar)ᵀ * hypGram 2 1 K * lmat x) a b = _ at g
  rw [Matrix.mul_apply, sum_hypIndex_two, Matrix.smul_apply, smul_eq_mul] at g
  simpa only [mul_hypGram_apply, Matrix.transpose_apply, Matrix.map_apply, hypPartner_inl,
    hypPartner_inr_inl, hypPartner_inr_inr] using g

theorem lmat_z_plane {x : Gam h}
    (hcol : ∀ a, a ≠ ιe₁ → a ≠ ιe₂ → lmat x a ιe₁ = 0 ∧ lmat x a ιe₂ = 0) :
    lmat x ιf₁ ιz = 0 ∧ lmat x ιf₂ ιz = 0 := by
  obtain ⟨μ, -, hs⟩ := exists_sim_apply x
  have J1 : hypGram 2 1 K ιe₁ ιz = 0 := by simp [hypGram_apply]
  have J2 : hypGram 2 1 K ιe₂ ιz = 0 := by simp [hypGram_apply]
  have s1 := hs ιe₁ ιz
  have s2 := hs ιe₂ ιz
  rw [J1, mul_zero] at s1
  rw [J2, mul_zero] at s2
  obtain ⟨f1, f1'⟩ := hcol ιf₁ (by decide) (by decide)
  obtain ⟨f2, f2'⟩ := hcol ιf₂ (by decide) (by decide)
  obtain ⟨z1, z1'⟩ := hcol ιz (by decide) (by decide)
  simp only [f1, f2, z1, map_zero, zero_mul, zero_add] at s1
  simp only [f1', f2', z1', map_zero, zero_mul, zero_add] at s2
  by_contra hne
  have hv : ![lmat x ιf₁ ιz, lmat x ιf₂ ιz] ≠ 0 := by
    intro e
    apply hne
    exact ⟨by simpa using congrFun e 0, by simpa using congrFun e 1⟩
  have hdet : ((pblk x).map h.bar)ᵀ.det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hv, ?_⟩
    funext i
    fin_cases i
    · simpa [pblk, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using s1
    · simpa [pblk, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using s2
  rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    map_eq_zero_iff _ h.bar.injective] at hdet
  exact det_pblk_ne_zero hcol hdet

theorem lmat_zz_ne_zero {x : Gam h}
    (hcol : ∀ a, a ≠ ιe₁ → a ≠ ιe₂ → lmat x a ιe₁ = 0 ∧ lmat x a ιe₂ = 0) :
    lmat x ιz ιz ≠ 0 := by
  obtain ⟨μ, hμ0, hs⟩ := exists_sim_apply x
  obtain ⟨hf1, hf2⟩ := lmat_z_plane hcol
  have Jz : hypGram 2 1 K ιz ιz = 1 := by simp [hypGram_apply]
  have s := hs ιz ιz
  rw [Jz, mul_one] at s
  simp only [hf1, hf2, map_zero, zero_mul, mul_zero, zero_add, add_zero] at s
  intro h0
  rw [h0, map_zero, zero_mul] at s
  exact hμ0 s.symm

theorem crd_act {x : Gam h}
    (hcol : ∀ a, a ≠ ιe₁ → a ≠ ιe₂ → lmat x a ιe₁ = 0 ∧ lmat x a ιe₂ = 0)
    {g : hypSU h 2 1} (hg : g ∈ Ssub h) (hxg : actΓ h x g ∈ Ssub h) :
    lmat x ιz ιz • crd (actΓ h x g) = pblk x *ᵥ fun i => x.1.right (crd g i) := by
  obtain ⟨hf1, hf2⟩ := lmat_z_plane hcol
  obtain ⟨-, v, C, hgC⟩ := hg
  obtain ⟨-, v', C', hgC'⟩ := hxg
  rw [crd_of_mat hgC', crd_of_mat hgC]
  funext i
  have hrel := congrFun (congrFun (lmat_mul_map x g) (.inl i)) ιz
  rw [hgC, hgC', Matrix.mul_apply, Matrix.mul_apply, sum_hypIndex_two, sum_hypIndex_two] at hrel
  fin_cases i
  · simp [oddUni, Matrix.map_apply, hf1, hf2] at hrel
    simp [pblk, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination -hrel
  · simp [oddUni, Matrix.map_apply, hf1, hf2] at hrel
    simp [pblk, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination -hrel

theorem exists_semilinear_crd {x : Gam h} (h₁ : actΓ h x (z₁SU h) ∈ Vsub h)
    (h₂ : actΓ h x (vSU h !![0, 0; 0, 1] (isHerm_e₂₂ h)) ∈ Vsub h) :
    ∃ (c : K) (M : Matrix (Fin 2) (Fin 2) K), c ≠ 0 ∧ M.det ≠ 0 ∧
      ∀ g ∈ Ssub h, actΓ h x g ∈ Ssub h →
        crd (actΓ h x g) = c • (M *ᵥ fun i => x.1.right (crd g i)) := by
  have hcol : ∀ a, a ≠ ιe₁ → a ≠ ιe₂ → lmat x a ιe₁ = 0 ∧ lmat x a ιe₂ = 0 :=
    fun a ha₁ ha₂ => lmat_col_plane h₁ h₂ ha₁ ha₂
  have hz := lmat_zz_ne_zero hcol
  refine ⟨(lmat x ιz ιz)⁻¹, pblk x, inv_ne_zero hz, det_pblk_ne_zero hcol, fun g hg hxg => ?_⟩
  rw [← crd_act hcol hg hxg, smul_smul, inv_mul_cancel₀ hz, one_smul]

end Semilinear

end CFSG.LocalAnalysis.EvenBN.U5

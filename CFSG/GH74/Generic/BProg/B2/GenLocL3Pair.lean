module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3Good

public noncomputable section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial Matrix
  CFSG.ComponentClassification.CatalogueBHigherLinearAction GenLocL3Good
open scoped MatrixGroups commutatorElement

namespace GenLocL3Pair

variable {K : Type} [Field K]

@[expose] def blkMatB (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![g 0 0, 0, g 0 1; 0, 1, 0; g 1 0, 0, g 1 1]

theorem blkMatB_mul (g h : Matrix (Fin 2) (Fin 2) K) :
    blkMatB (g * h) = blkMatB g * blkMatB h := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [blkMatB, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blkMatB_one : blkMatB (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [blkMatB]

theorem det_blkMatB (g : Matrix (Fin 2) (Fin 2) K) : (blkMatB g).det = g.det := by
  simp [blkMatB, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def blkHomB : SL(2, K) →* SL(3, K) where
  toFun g := ⟨blkMatB (g : Matrix (Fin 2) (Fin 2) K), by rw [det_blkMatB]; exact g.2⟩
  map_one' := Subtype.ext (by simp [blkMatB_one])
  map_mul' g h := Subtype.ext (by
    change blkMatB ((g * h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      blkMatB (g : Matrix (Fin 2) (Fin 2) K) * blkMatB (h : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, blkMatB_mul])

theorem coe_blkHomB (g : SL(2, K)) :
    ((blkHomB g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = blkMatB (g : Matrix (Fin 2) (Fin 2) K) := rfl

theorem blkMatB_injective : Function.Injective (blkMatB (K := K)) := by
  intro g h hgh
  ext a b
  fin_cases a <;> fin_cases b
  · exact congrFun (congrFun hgh 0) 0
  · exact congrFun (congrFun hgh 0) 2
  · exact congrFun (congrFun hgh 2) 0
  · exact congrFun (congrFun hgh 2) 2

@[expose] def phiB : SL(2, K) →* LinearFlag.projectiveSL 3 K := (LinearFlag.proj 3 K).comp blkHomB

theorem phiB_injective : Function.Injective (phiB (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : blkHomB g ∈ LinearFlag.scalars 3 K := LinearFlag.proj_eq_one_iff.1 hg
  obtain ⟨c, -, hc⟩ := h1
  have h2 := congrFun (congrFun hc 1) 1
  rw [coe_blkHomB] at h2
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, blkMatB] at h2
  have hc1 : (c : K) = 1 := by simpa using h2.symm
  have h3 : ((blkHomB g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hc, hc1]; simp
  rw [coe_blkHomB, ← blkMatB_one] at h3
  exact Subtype.ext (blkMatB_injective h3)


theorem blkMatB_map (σ : K ≃+* K) (g : Matrix (Fin 2) (Fin 2) K) :
    (blkMatB g).map σ = blkMatB (g.map σ) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [blkMatB]

theorem blkMatB_transpose (g : Matrix (Fin 2) (Fin 2) K) :
    (blkMatB g)ᵀ = blkMatB gᵀ := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [blkMatB]

theorem fieldAut_phiB (σ : K ≃+* K) (g : SL(2, K)) :
    LinearFlag.fieldAut 3 K σ (phiB g) = phiB (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
  unfold phiB
  simp only [MonoidHom.comp_apply]
  rw [LinearFlag.fieldAut_proj]
  congr 1
  apply Subtype.ext
  change ((Matrix.SpecialLinearGroup.map σ.toRingHom (blkHomB g) : SL(3, K)) :
      Matrix (Fin 3) (Fin 3) K) =
    blkMatB ((Matrix.SpecialLinearGroup.map σ.toRingHom g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
  exact blkMatB_map σ _

theorem dualAut_phiB (g : SL(2, K)) :
    LinearFlag.dualAut 3 K (phiB g) = phiB ((g⁻¹).transpose) := by
  unfold phiB
  simp only [MonoidHom.comp_apply]
  rw [LinearFlag.dualAut_proj]
  congr 1
  apply Subtype.ext
  rw [← map_inv]
  change (((blkHomB g⁻¹ : SL(3, K)).transpose : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
    blkMatB (((g⁻¹).transpose : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_transpose, coe_blkHomB,
    blkMatB_transpose]

theorem conj_blkB (u : Fin 3 → Kˣ) (g : SL(2, K)) :
    slConjugation 3 K (diag3 u) (blkHomB g) = blkHomB
      (slConjugation 2 K (diag2 (u 0) (u 2)) g) := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, coe_blkHomB, coe_blkHomB,
    LinearFlag.coe_slConjugation, coe_diag3, coe_diag3_inv, coe_diag2, coe_diag2_inv]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blkMatB, Matrix.mul_apply, Matrix.diagonal_apply]

theorem conjAut_phiB_eq (u : Fin 3 → Kˣ) (g : SL(2, K)) :
    LinearFlag.conjAut 3 K (diag3 u) (phiB g) = phiB (slConjugation 2 K (diag2 (u 0) (u 2)) g) := by
  unfold phiB
  simp only [MonoidHom.comp_apply]
  rw [LinearFlag.conjAut_proj, conj_blkB]

theorem dualAut_phiB_eq (g : SL(2, K)) :
    LinearFlag.dualAut 3 K (phiB g) = phiB (slConjugation 2 K Jgl g) := by
  rw [dualAut_phiB, inv_transpose_eq]


theorem stable_phiB {y : MulAut (LinearFlag.projectiveSL 3 K)} (hy : y ∈ frameStab 3 K) (g : SL(2, K)) :
    y (phiB g) ∈ (phiB (K := K)).range := by
  obtain ⟨x, σ, ε, hx, hε, rfl⟩ := GenLocL3NFFrame.mem_frameStab_iff.1 hy
  obtain ⟨u, rfl⟩ := exists_diag3 hx
  have hδ : ∀ z ∈ (phiB (K := K)).range, LinearFlag.dualAut 3 K z ∈ (phiB (K := K)).range := by
    rintro _ ⟨g, rfl⟩
    rw [dualAut_phiB]
    exact ⟨_, rfl⟩
  have hf : ∀ z ∈ (phiB (K := K)).range, LinearFlag.fieldAut 3 K σ z ∈ (phiB (K := K)).range := by
    rintro _ ⟨g, rfl⟩
    rw [fieldAut_phiB]
    exact ⟨_, rfl⟩
  have hc : ∀ z ∈ (phiB (K := K)).range, LinearFlag.conjAut 3 K (diag3 u) z ∈ (phiB (K := K)).range := by
    rintro _ ⟨g, rfl⟩
    rw [conjAut_phiB_eq]
    exact ⟨_, rfl⟩
  have h1 : (LinearFlag.dualAut 3 K ^ ε) (phiB g) ∈ (phiB (K := K)).range := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · simp
    · simpa using hδ _ ⟨g, rfl⟩
  simp only [MulAut.mul_apply]
  exact hc _ (hf _ h1)

theorem exists_restB :
    ∃ ρ : frameStab 3 K →* MulAut SL(2, K), ∀ (y : frameStab 3 K) (g : SL(2, K)),
      (y : MulAut (LinearFlag.projectiveSL 3 K)) (phiB g) = phiB (ρ y g) :=
  GenLocL3Blk.exists_restrict_action phiB phiB_injective (frameStab 3 K).subtype
    fun y g => stable_phiB y.2 g

@[expose] def restB : frameStab 3 K →* MulAut SL(2, K) := Classical.choose exists_restB

theorem restB_spec (y : frameStab 3 K) (g : SL(2, K)) :
    (y : MulAut (LinearFlag.projectiveSL 3 K)) (phiB g) = phiB (restB y g) :=
  Classical.choose_spec exists_restB y g

theorem restB_eq_of_apply {y : frameStab 3 K} {τ : MulAut SL(2, K)}
    (h : ∀ g, (y : MulAut (LinearFlag.projectiveSL 3 K)) (phiB g) = phiB (τ g)) : restB y = τ := by
  refine MulEquiv.ext fun g => ?_
  apply phiB_injective
  rw [← restB_spec, h]

theorem restB_conjAut (u : Fin 3 → Kˣ) :
    restB ⟨LinearFlag.conjAut 3 K (diag3 u), GenLocL3NFAux.conjAut_mem_frameStab (isDiag_diag3 u)⟩ =
      slConjugation 2 K (diag2 (u 0) (u 2)) :=
  restB_eq_of_apply fun g => conjAut_phiB_eq u g

theorem restB_dualAut :
    restB ⟨LinearFlag.dualAut 3 K, GenLocL3NFAux.dualAut_mem_frameStab⟩ = slConjugation 2 K Jgl :=
  restB_eq_of_apply fun g => dualAut_phiB_eq g



@[expose] def rt (i j : Fin 3) (h : i ≠ j) (t : K) : LinearFlag.projectiveSL 3 K :=
  LinearFlag.proj 3 K (Matrix.SpecialLinearGroup.transvection h t)

@[expose] def FullPair (H : Subgroup (LinearFlag.projectiveSL 3 K)) (i j : Fin 3) (h : i ≠ j) : Prop :=
  (∀ t : K, rt i j h t ∈ H) ∧ ∀ t : K, rt j i h.symm t ∈ H

theorem FullPair.symm {H : Subgroup (LinearFlag.projectiveSL 3 K)} {i j : Fin 3} {h : i ≠ j}
    (hf : FullPair H i j h) : FullPair H j i h.symm := ⟨hf.2, hf.1⟩

theorem top_of_roots {H : Subgroup (LinearFlag.projectiveSL 3 K)}
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (t : K), rt i j hij t ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 K x
  have : g ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 K) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation (K := K) (n := 3)]
    exact Subgroup.mem_top g
  refine Subgroup.closure_induction (p := fun g _ => LinearFlag.proj 3 K g ∈ H) ?_ ?_ ?_ ?_ this
  · rintro _ ⟨i, j, hij, c, rfl⟩
    exact h i j hij c
  · rw [map_one]; exact H.one_mem
  · intro a b _ _ ha hb
    rw [map_mul]; exact H.mul_mem ha hb
  · intro a _ ha
    rw [map_inv]; exact H.inv_mem ha

theorem fullPair_trans {H : Subgroup (LinearFlag.projectiveSL 3 K)} {i j k : Fin 3} {hij : i ≠ j}
    {hjk : j ≠ k} (hik : i ≠ k) (h1 : FullPair H i j hij) (h2 : FullPair H j k hjk) :
    FullPair H i k hik := by
  have comm : ∀ {a b : LinearFlag.projectiveSL 3 K}, a ∈ H → b ∈ H → ⁅a, b⁆ ∈ H := fun {a b} ha hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  constructor
  · intro t
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjk hik t 1
    rw [mul_one] at h
    have : rt i k hik t = ⁅rt i j hij t, rt j k hjk 1⁆ := by
      unfold rt
      rw [← h]
      exact map_commutatorElement (LinearFlag.proj 3 K) _ _
    rw [this]
    exact comm (h1.1 t) (h2.1 1)
  · intro t
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hjk.symm hij.symm hik.symm t 1
    rw [mul_one] at h
    have : rt k i hik.symm t = ⁅rt k j hjk.symm t, rt j i hij.symm 1⁆ := by
      unfold rt
      rw [← h]
      exact map_commutatorElement (LinearFlag.proj 3 K) _ _
    rw [this]
    exact comm (h2.2 t) (h1.2 1)



theorem blkHomB_transvection_01 (t : K) :
    blkHomB (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t) =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t := by
  apply Subtype.ext
  rw [coe_blkHomB, CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection]
  ext p q; fin_cases p <;> fin_cases q <;> simp [blkMatB, Matrix.add_apply]

theorem blkHomB_transvection_10 (t : K) :
    blkHomB (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t) =
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t := by
  apply Subtype.ext
  rw [coe_blkHomB, CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection]
  ext p q; fin_cases p <;> fin_cases q <;> simp [blkMatB, Matrix.add_apply]

theorem fullPair_phi0 {H : Subgroup (LinearFlag.projectiveSL 3 K)}
    (h : ∀ g, GenLocL3Blk.phi 0 g ∈ H) : FullPair H 0 1 (by decide) := by
  constructor
  · intro t
    have := h (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t)
    unfold GenLocL3Blk.phi at this
    rw [MonoidHom.comp_apply, GenLocL3Blk.blkHom_transvection] at this
    exact this
  · intro t
    have := h (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t)
    unfold GenLocL3Blk.phi at this
    rw [MonoidHom.comp_apply, GenLocL3Blk.blkHom_transvection] at this
    exact this

theorem fullPair_phi1 {H : Subgroup (LinearFlag.projectiveSL 3 K)}
    (h : ∀ g, GenLocL3Blk.phi 1 g ∈ H) : FullPair H 1 2 (by decide) := by
  constructor
  · intro t
    have := h (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t)
    unfold GenLocL3Blk.phi at this
    rw [MonoidHom.comp_apply, GenLocL3Blk.blkHom_transvection] at this
    exact this
  · intro t
    have := h (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t)
    unfold GenLocL3Blk.phi at this
    rw [MonoidHom.comp_apply, GenLocL3Blk.blkHom_transvection] at this
    exact this

theorem fullPair_phiB {H : Subgroup (LinearFlag.projectiveSL 3 K)}
    (h : ∀ g, phiB g ∈ H) : FullPair H 0 2 (by decide) := by
  constructor
  · intro t
    have := h (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t)
    unfold phiB at this
    rw [MonoidHom.comp_apply, blkHomB_transvection_01] at this
    exact this
  · intro t
    have := h (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t)
    unfold phiB at this
    rw [MonoidHom.comp_apply, blkHomB_transvection_10] at this
    exact this

theorem top_of_fullPair_adj {H : Subgroup (LinearFlag.projectiveSL 3 K)}
    (h01 : FullPair H 0 1 (by decide)) (h12 : FullPair H 1 2 (by decide)) : H = ⊤ := by
  have h02 : FullPair H 0 2 (by decide) := fullPair_trans (by decide) h01 h12
  have h20 : FullPair H 2 0 (by decide) := h02.symm
  have h10 : FullPair H 1 0 (by decide) := h01.symm
  have h21 : FullPair H 2 1 (by decide) := h12.symm
  refine top_of_roots fun i j hij t => ?_
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01.1 t
  · exact h02.1 t
  · exact h10.1 t
  · exact absurd rfl hij
  · exact h12.1 t
  · exact h20.1 t
  · exact h21.1 t
  · exact absurd rfl hij


@[expose] def wMat (p q : Fin 3) (β : K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j =>
    if i = p ∧ j = q then β else if i = q ∧ j = p then -β⁻¹ else if i = j ∧ i ≠ p ∧ i ≠ q then 1 else 0

theorem det_wMat {p q : Fin 3} (hpq : p ≠ q) {β : K} (hβ : β ≠ 0) : (wMat p q β).det = 1 := by
  fin_cases p <;> fin_cases q <;>
    first
    | exact absurd rfl hpq
    | (simp [wMat, Matrix.det_fin_three]; field_simp)

@[expose] def wSL (p q : Fin 3) (hpq : p ≠ q) {β : K} (hβ : β ≠ 0) : SL(3, K) :=
  ⟨wMat p q β, det_wMat hpq hβ⟩

theorem wSL_mul_transvection_rs {r s q : Fin 3} (hrs : r ≠ s) (hsq : s ≠ q) (hrq : r ≠ q) {β : K}
    (hβ : β ≠ 0) (t : K) :
    wSL s q hsq hβ * Matrix.SpecialLinearGroup.transvection hrs t =
      Matrix.SpecialLinearGroup.transvection hrq (-β * t) * wSL s q hsq hβ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection]
  show wMat s q β * _ = _ * wMat s q β
  fin_cases r <;> fin_cases s <;> fin_cases q <;>
    first
    | exact absurd rfl hrs
    | exact absurd rfl hsq
    | exact absurd rfl hrq
    | (ext a b; fin_cases a <;> fin_cases b <;>
        simp [wMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply] <;> field_simp)

theorem wSL_mul_transvection_sr {r s q : Fin 3} (hrs : r ≠ s) (hsq : s ≠ q) (hrq : r ≠ q) {β : K}
    (hβ : β ≠ 0) (t : K) :
    wSL s q hsq hβ * Matrix.SpecialLinearGroup.transvection hrs.symm t =
      Matrix.SpecialLinearGroup.transvection hrq.symm (-β⁻¹ * t) * wSL s q hsq hβ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection]
  show wMat s q β * _ = _ * wMat s q β
  fin_cases r <;> fin_cases s <;> fin_cases q <;>
    first
    | exact absurd rfl hrs
    | exact absurd rfl hsq
    | exact absurd rfl hrq
    | (ext a b; fin_cases a <;> fin_cases b <;>
        simp [wMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply])


theorem fullPair_of_mono {H : Subgroup (LinearFlag.projectiveSL 3 K)} {r s q : Fin 3} {hrs : r ≠ s}
    (hsq : s ≠ q) (hrq : r ≠ q) {β : K} (hβ : β ≠ 0)
    (hw : LinearFlag.proj 3 K (wSL s q hsq hβ) ∈ H) (hf : FullPair H r s hrs) :
    FullPair H r q hrq := by
  constructor
  · intro u
    have hu : -β * (-u / β) = u := by field_simp
    have h1 := wSL_mul_transvection_rs hrs hsq hrq hβ (-u / β)
    rw [hu] at h1
    have h2 : Matrix.SpecialLinearGroup.transvection hrq u =
        wSL s q hsq hβ * Matrix.SpecialLinearGroup.transvection hrs (-u / β) * (wSL s q hsq hβ)⁻¹ :=
      eq_mul_inv_iff_mul_eq.2 h1.symm
    have h3 : rt r q hrq u = LinearFlag.proj 3 K (wSL s q hsq hβ) * rt r s hrs (-u / β) *
        (LinearFlag.proj 3 K (wSL s q hsq hβ))⁻¹ := by
      unfold rt
      rw [h2, map_mul, map_mul, map_inv]
    rw [h3]
    exact H.mul_mem (H.mul_mem hw (hf.1 _)) (H.inv_mem hw)
  · intro u
    have hu : -β⁻¹ * (-β * u) = u := by field_simp
    have h1 := wSL_mul_transvection_sr hrs hsq hrq hβ (-β * u)
    rw [hu] at h1
    have h2 : Matrix.SpecialLinearGroup.transvection hrq.symm u =
        wSL s q hsq hβ * Matrix.SpecialLinearGroup.transvection hrs.symm (-β * u) *
          (wSL s q hsq hβ)⁻¹ :=
      eq_mul_inv_iff_mul_eq.2 h1.symm
    have h3 : rt q r hrq.symm u = LinearFlag.proj 3 K (wSL s q hsq hβ) * rt s r hrs.symm (-β * u) *
        (LinearFlag.proj 3 K (wSL s q hsq hβ))⁻¹ := by
      unfold rt
      rw [h2, map_mul, map_mul, map_inv]
    rw [h3]
    exact H.mul_mem (H.mul_mem hw (hf.2 _)) (H.inv_mem hw)

theorem top_of_three {H : Subgroup (LinearFlag.projectiveSL 3 K)} {i j k : Fin 3} {hij : i ≠ j}
    {hjk : j ≠ k} {hik : i ≠ k} (h1 : FullPair H i j hij) (h2 : FullPair H j k hjk)
    (h3 : FullPair H i k hik) : H = ⊤ := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact absurd rfl hij
    | exact absurd rfl hjk
    | exact absurd rfl hik
    | exact top_of_fullPair_adj h1 h2
    | exact top_of_fullPair_adj h1 h2.symm
    | exact top_of_fullPair_adj h1.symm h2
    | exact top_of_fullPair_adj h1.symm h2.symm
    | exact top_of_fullPair_adj h1 h3
    | exact top_of_fullPair_adj h1 h3.symm
    | exact top_of_fullPair_adj h1.symm h3
    | exact top_of_fullPair_adj h1.symm h3.symm
    | exact top_of_fullPair_adj h2 h3
    | exact top_of_fullPair_adj h2 h3.symm
    | exact top_of_fullPair_adj h2.symm h3
    | exact top_of_fullPair_adj h2.symm h3.symm
    | exact top_of_fullPair_adj h2 h1
    | exact top_of_fullPair_adj h2 h1.symm
    | exact top_of_fullPair_adj h2.symm h1
    | exact top_of_fullPair_adj h2.symm h1.symm
    | exact top_of_fullPair_adj h3 h1
    | exact top_of_fullPair_adj h3 h1.symm
    | exact top_of_fullPair_adj h3.symm h1
    | exact top_of_fullPair_adj h3.symm h1.symm
    | exact top_of_fullPair_adj h3 h2
    | exact top_of_fullPair_adj h3 h2.symm

theorem top_of_two_pairs {H : Subgroup (LinearFlag.projectiveSL 3 K)} {i j k : Fin 3} {hij : i ≠ j}
    {hik : i ≠ k} (hjk : j ≠ k) (h1 : FullPair H i j hij) (h2 : FullPair H i k hik) : H = ⊤ :=
  top_of_three h1 (fullPair_trans hjk h1.symm h2) h2


@[expose] def anti {β : K} (hβ : β ≠ 0) : SL(2, K) :=
  ⟨!![0, β; -β⁻¹, 0], by simp [Matrix.det_fin_two]; field_simp⟩

theorem wMat_swap {p q : Fin 3} (hpq : p ≠ q) {β : K} :
    wMat q p (-β⁻¹) = wMat p q β := by
  ext i j
  simp only [wMat, Matrix.of_apply]
  by_cases h1 : i = q ∧ j = p
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hpq, hpq.symm]
  · by_cases h2 : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := h2
      simp [hpq, hpq.symm]
    · simp [h1, h2]
      by_cases h3 : i = j
      · simp [h3, and_comm]
      · simp [h3]

@[expose] def phiM : Fin 3 → (SL(2, K) →* LinearFlag.projectiveSL 3 K) :=
  ![GenLocL3Blk.phi 1, phiB, GenLocL3Blk.phi 0]

theorem phiM_anti_0 {β : K} (hβ : β ≠ 0) :
    phiM 0 (anti hβ) = LinearFlag.proj 3 K (wSL 1 2 (by decide) hβ) := by
  show LinearFlag.proj 3 K (GenLocL3Blk.blkHom 1 (anti hβ)) = _
  congr 1
  apply Subtype.ext
  rw [GenLocL3Blk.coe_blkHom]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [GenLocL3Blk.blkMat, anti, wSL, wMat]

theorem phiM_anti_1 {β : K} (hβ : β ≠ 0) :
    phiM 1 (anti hβ) = LinearFlag.proj 3 K (wSL 0 2 (by decide) hβ) := by
  show LinearFlag.proj 3 K (blkHomB (anti hβ)) = _
  congr 1
  apply Subtype.ext
  rw [coe_blkHomB]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blkMatB, anti, wSL, wMat]

theorem phiM_anti_2 {β : K} (hβ : β ≠ 0) :
    phiM 2 (anti hβ) = LinearFlag.proj 3 K (wSL 0 1 (by decide) hβ) := by
  show LinearFlag.proj 3 K (GenLocL3Blk.blkHom 0 (anti hβ)) = _
  congr 1
  apply Subtype.ext
  rw [GenLocL3Blk.coe_blkHom]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [GenLocL3Blk.blkMat, anti, wSL, wMat]

theorem wSL_swap {p q : Fin 3} (hpq : p ≠ q) {β : K} (hβ : β ≠ 0) :
    wSL q p hpq.symm (inv_ne_zero hβ |> neg_ne_zero.2 : -β⁻¹ ≠ 0) = wSL p q hpq hβ := by
  apply Subtype.ext
  exact wMat_swap hpq


@[expose] def crd : Fin 3 → Fin 2 → Fin 3 := ![![1, 2], ![0, 2], ![0, 1]]

@[expose] def restM : (m : Fin 3) → (frameStab 3 K →* MulAut SL(2, K)) :=
  ![rest 1, restB, rest 0]

theorem restM_spec (m : Fin 3) (y : frameStab 3 K) (g : SL(2, K)) :
    (y : MulAut (LinearFlag.projectiveSL 3 K)) (phiM m g) = phiM m (restM m y g) := by
  fin_cases m
  · exact rest_spec 1 y g
  · exact restB_spec y g
  · exact rest_spec 0 y g

theorem restM_conjAut (u : Fin 3 → Kˣ) (m : Fin 3) :
    restM m ⟨LinearFlag.conjAut 3 K (diag3 u), GenLocL3NFAux.conjAut_mem_frameStab (isDiag_diag3 u)⟩ =
      slConjugation 2 K (diag2 (u (crd m 0)) (u (crd m 1))) := by
  fin_cases m
  · exact rest_conjAut u 1
  · exact restB_conjAut u
  · exact rest_conjAut u 0

theorem restM_dualAut (m : Fin 3) :
    restM m ⟨LinearFlag.dualAut 3 K, GenLocL3NFAux.dualAut_mem_frameStab⟩ = slConjugation 2 K Jgl := by
  fin_cases m
  · exact rest_dualAut 1
  · exact restB_dualAut
  · exact rest_dualAut 0

theorem restM_fieldAut [Finite K] (σ : K ≃+* K) (m : Fin 3) :
    restM m ⟨LinearFlag.fieldAut 3 K σ, GenLocL3NFAux.fieldAut_mem_frameStab σ⟩ =
      GLS.IVK.Lifted.slFieldAut σ := by
  have key : ∀ (i : Fin 2), rest i ⟨LinearFlag.fieldAut 3 K σ, GenLocL3NFAux.fieldAut_mem_frameStab σ⟩ =
      GLS.IVK.Lifted.slFieldAut σ := fun i =>
    rest_eq_of_apply fun g => by rw [GenLocL3Blk.fieldAut_phi, GLS.IVK.Lifted.slFieldAut_apply]
  fin_cases m
  · exact key 1
  · exact restB_eq_of_apply fun g => by rw [fieldAut_phiB, GLS.IVK.Lifted.slFieldAut_apply]
  · exact key 0

theorem map_gammaAct_le {J H A : Type} [Group J] [Group H] [Group A] (α : A →* MulAut J)
    (β : A →* MulAut H) (φ : H →* J) (hφ : ∀ (a : A) (x : H), α a (φ x) = φ (β a x)) :
    (gammaAct β).map φ ≤ gammaAct α := by
  rw [gammaAct, Subgroup.map_iSup]
  refine iSup_le fun E => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hE => ?_
  rintro _ ⟨x, hx, rfl⟩
  refine le_gammaAct α hE ?_
  rw [GenLocBasic.mem_fixedIn_map]
  intro a ha
  rw [hφ, (GenLocBasic.mem_fixedIn_map _ _ _).1 hx a ha]

theorem blockFull_of_good {A : Type} [Group A] (α : A →* MulAut (LinearFlag.projectiveSL 3 K))
    (hα : α.range ≤ frameStab 3 K) (m : Fin 3)
    (h : gammaAct ((restM m).comp (toFrame α hα)) = ⊤) (g : SL(2, K)) : phiM m g ∈ gammaAct α := by
  have := map_gammaAct_le α ((restM m).comp (toFrame α hα)) (phiM m)
    (fun a x => restM_spec m (toFrame α hα a) x) 
  rw [h] at this
  exact this ⟨g, Subgroup.mem_top g, rfl⟩

theorem top_of_two_blocks {H : Subgroup (LinearFlag.projectiveSL 3 K)} {m m' : Fin 3} (hmm' : m ≠ m')
    (h : ∀ g, phiM m g ∈ H) (h' : ∀ g, phiM m' g ∈ H) : H = ⊤ := by
  have e0 : (∀ g, phiM 0 g ∈ H) → FullPair H 1 2 (by decide) := fun h => fullPair_phi1 h
  have e1 : (∀ g, phiM 1 g ∈ H) → FullPair H 0 2 (by decide) := fun h => fullPair_phiB h
  have e2 : (∀ g, phiM 2 g ∈ H) → FullPair H 0 1 (by decide) := fun h => fullPair_phi0 h
  fin_cases m <;> fin_cases m'
  · exact absurd rfl hmm'
  · exact top_of_two_pairs (i := 2) (j := 1) (k := 0) (by decide) (e0 h).symm (e1 h').symm
  · exact top_of_fullPair_adj (e2 h') (e0 h)
  · exact top_of_two_pairs (i := 2) (j := 0) (k := 1) (by decide) (e1 h).symm (e0 h').symm
  · exact absurd rfl hmm'
  · exact top_of_two_pairs (i := 0) (j := 2) (k := 1) (by decide) (e1 h) (e2 h')
  · exact top_of_fullPair_adj (e2 h) (e0 h')
  · exact top_of_two_pairs (i := 0) (j := 1) (k := 2) (by decide) (e2 h) (e1 h')
  · exact absurd rfl hmm'

theorem top_of_full_mono {H : Subgroup (LinearFlag.projectiveSL 3 K)} {a b : Fin 3} (hab : a ≠ b)
    (ha : ∀ g, phiM a g ∈ H) {β : K} (hβ : β ≠ 0) (hb : phiM b (anti hβ) ∈ H) : H = ⊤ := by
  have e0 : (∀ g, phiM 0 g ∈ H) → FullPair H 1 2 (by decide) := fun h => fullPair_phi1 h
  have e1 : (∀ g, phiM 1 g ∈ H) → FullPair H 0 2 (by decide) := fun h => fullPair_phiB h
  have e2 : (∀ g, phiM 2 g ∈ H) → FullPair H 0 1 (by decide) := fun h => fullPair_phi0 h
  have hβ' : -β⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hβ)
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  ·
    have hw : LinearFlag.proj 3 K (wSL 2 0 (by decide) hβ') ∈ H := by
      have := wSL_swap (p := (0 : Fin 3)) (q := 2) (by decide) hβ
      rw [this, ← phiM_anti_1 hβ]; exact hb
    have := fullPair_of_mono (r := 1) (s := 2) (q := 0) (by decide) (by decide) hβ' hw (e0 ha)
    exact top_of_two_pairs (i := 1) (j := 2) (k := 0) (by decide) (e0 ha) this
  ·
    have hw : LinearFlag.proj 3 K (wSL 1 0 (by decide) hβ') ∈ H := by
      have := wSL_swap (p := (0 : Fin 3)) (q := 1) (by decide) hβ
      rw [this, ← phiM_anti_2 hβ]; exact hb
    have := fullPair_of_mono (r := 2) (s := 1) (q := 0) (by decide) (by decide) hβ' hw (e0 ha).symm
    exact top_of_two_pairs (i := 2) (j := 1) (k := 0) (by decide) (e0 ha).symm this
  ·
    have hw : LinearFlag.proj 3 K (wSL 2 1 (by decide) hβ') ∈ H := by
      have := wSL_swap (p := (1 : Fin 3)) (q := 2) (by decide) hβ
      rw [this, ← phiM_anti_0 hβ]; exact hb
    have := fullPair_of_mono (r := 0) (s := 2) (q := 1) (by decide) (by decide) hβ' hw (e1 ha)
    exact top_of_two_pairs (i := 0) (j := 2) (k := 1) (by decide) (e1 ha) this
  · exact absurd rfl hab
  ·
    have hw : LinearFlag.proj 3 K (wSL 0 1 (by decide) hβ) ∈ H := by
      rw [← phiM_anti_2 hβ]; exact hb
    have := fullPair_of_mono (r := 2) (s := 0) (q := 1) (by decide) (by decide) hβ hw (e1 ha).symm
    exact top_of_two_pairs (i := 2) (j := 0) (k := 1) (by decide) (e1 ha).symm this
  ·
    have hw : LinearFlag.proj 3 K (wSL 1 2 (by decide) hβ) ∈ H := by
      rw [← phiM_anti_0 hβ]; exact hb
    have := fullPair_of_mono (r := 0) (s := 1) (q := 2) (by decide) (by decide) hβ hw (e2 ha)
    exact top_of_two_pairs (i := 0) (j := 1) (k := 2) (by decide) (e2 ha) this
  ·
    have hw : LinearFlag.proj 3 K (wSL 0 2 (by decide) hβ) ∈ H := by
      rw [← phiM_anti_1 hβ]; exact hb
    have := fullPair_of_mono (r := 1) (s := 0) (q := 2) (by decide) (by decide) hβ hw (e2 ha).symm
    exact top_of_two_pairs (i := 1) (j := 0) (k := 2) (by decide) (e2 ha).symm this
  · exact absurd rfl hab

theorem gammaAct_eq_top_of_two_good {A : Type} [Group A]
    (α : A →* MulAut (LinearFlag.projectiveSL 3 K)) (hα : α.range ≤ frameStab 3 K) {m m' : Fin 3}
    (hmm' : m ≠ m') (h : gammaAct ((restM m).comp (toFrame α hα)) = ⊤)
    (h' : gammaAct ((restM m').comp (toFrame α hα)) = ⊤) : gammaAct α = ⊤ :=
  top_of_two_blocks hmm' (blockFull_of_good α hα m h) (blockFull_of_good α hα m' h')

theorem gammaAct_eq_top_of_good_mono {A : Type} [Group A]
    (α : A →* MulAut (LinearFlag.projectiveSL 3 K)) (hα : α.range ≤ frameStab 3 K) {a b : Fin 3}
    (hab : a ≠ b) (h : gammaAct ((restM a).comp (toFrame α hα)) = ⊤) {β : K} (hβ : β ≠ 0)
    (hw : phiM b (anti hβ) ∈ gammaAct α) : gammaAct α = ⊤ :=
  top_of_full_mono hab (blockFull_of_good α hα a h) hβ hw

end GenLocL3Pair

end CFSG.GH74.Generic.BProg.B2

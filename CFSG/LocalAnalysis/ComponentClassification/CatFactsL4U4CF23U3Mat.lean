module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23U3Desc
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OutU

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem au_bijective (A : GL (Fin n) K) :
    Function.Bijective (antiunitaryMap h (A : Matrix (Fin n) (Fin n) K)) := by
  have hAi : (↑A⁻¹ : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAi' : (A : Matrix (Fin n) (Fin n) K) * (↑A⁻¹ : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · intro v w hvw
    rw [antiunitaryMap_apply, antiunitaryMap_apply] at hvw
    have e := congrArg (fun x => (↑A⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ x) hvw
    simp only [Matrix.mulVec_mulVec, hAi, Matrix.one_mulVec] at e
    funext i
    exact (RingHom.injective h.bar) (congrFun e i)
  · intro w
    refine ⟨fun i => h.bar (((↑A⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ w) i), ?_⟩
    rw [antiunitaryMap_apply]
    simp only [h.bar_bar]
    change (A : Matrix (Fin n) (Fin n) K) *ᵥ ((↑A⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, hAi', Matrix.one_mulVec]

theorem bar_mulVec (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (fun i => h.bar ((M *ᵥ v) i)) = M.map h.bar *ᵥ fun i => h.bar (v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem au_form {A : GL (Fin n) K}
    (hAu : uStar h (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1)
    (v w : Fin n → K) :
    stdHermForm h n (antiunitaryMap h (A : Matrix (Fin n) (Fin n) K) v)
      (antiunitaryMap h (A : Matrix (Fin n) (Fin n) K) w) = h.bar (stdHermForm h n v w) := by
  rw [antiunitaryMap_apply, antiunitaryMap_apply, stdHermForm_eq_gramForm, gramForm_mulVec,
    Matrix.mul_one]
  change gramForm h (uStar h (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K))
    _ _ = _
  rw [hAu, gramForm_apply, gramForm_apply]
  simp only [Matrix.one_mulVec, dotProduct, map_sum, map_mul, h.bar_bar]

theorem au_sq (A : Matrix (Fin n) (Fin n) K) {c : K} (hc : A * A.map h.bar = c • 1)
    (v : Fin n → K) : antiunitaryMap h A (antiunitaryMap h A v) = c • v := by
  rw [antiunitaryMap_apply, antiunitaryMap_apply]
  have e : (fun i => h.bar ((A *ᵥ fun i => h.bar (v i)) i)) = A.map h.bar *ᵥ v := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, h.bar_bar]
  rw [e, Matrix.mulVec_mulVec, hc, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem ne_zero_of_mul_bar {A : GL (Fin n) K} {c : K}
    (hAA : (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K).map h.bar = c • 1)
    (hn : 1 ≤ n) : c ≠ 0 := by
  intro hc
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [hc, zero_smul] at hAA
  have h1 := congrArg Matrix.det hAA
  rw [det_mul, det_zero, show
    (A : Matrix (Fin n) (Fin n) K).map h.bar = h.bar.mapMatrix (A : Matrix (Fin n) (Fin n) K)
    from rfl, ← RingHom.map_det] at h1
  have hA0 : (A : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  exact mul_ne_zero hA0 (fun h0 => hA0 ((map_eq_zero h.bar).1 h0)) h1

theorem exists_su_conj_three (hp2 : p ≠ 2) {A A' : GL (Fin 3) K}
    (hAu : uStar h (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1)
    (hA'u : uStar h (A' : Matrix (Fin 3) (Fin 3) K) * (A' : Matrix (Fin 3) (Fin 3) K) = 1)
    {c c' : K}
    (hAA : (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K).map h.bar = c • 1)
    (hA'A' : (A' : Matrix (Fin 3) (Fin 3) K) * (A' : Matrix (Fin 3) (Fin 3) K).map h.bar =
      c' • 1)
    (hdet : (A' : Matrix (Fin 3) (Fin 3) K).det = (A : Matrix (Fin 3) (Fin 3) K).det) :
    ∃ G : unitarySU p f K 3,
      ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) *
        ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = A' := by
  classical
  have : Finite K := h.finite
  have hc0 := ne_zero_of_mul_bar h hAA (by norm_num)
  have hc0' := ne_zero_of_mul_bar h hA'A' (by norm_num)
  obtain ⟨hμ1, hμ1', g, c₁, hc₁, hgH, hgτ⟩ := exists_conj_antiunitary h hp2
    (by rw [Module.finrank_fin_fun]) (stdHermForm_isSymm h 3) (stdHermForm_separatingLeft h 3)
    (antiunitaryMap h (A : Matrix (Fin 3) (Fin 3) K))
    (antiunitaryMap h (A' : Matrix (Fin 3) (Fin 3) K)) (au_bijective h A) (au_bijective h A')
    (au_form h hAu) (au_form h hA'u) (Units.mk0 c hc0) (Units.mk0 c' hc0') (au_sq h _ hAA)
    (au_sq h _ hA'A')
  have hc1 : c = 1 := by simpa using congrArg Units.val hμ1
  have hc1' : c' = 1 := by simpa using congrArg Units.val hμ1'
  set Gm := LinearMap.toMatrix' (g : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) with hGm
  have hGv : ∀ v, Gm *ᵥ v = g v := fun v => by
    rw [hGm, LinearMap.toMatrix'_mulVec]
    rfl
  have hGu : uStar h Gm * Gm = 1 := by
    have h1 := (gramForm_isometry_iff h (1 : Matrix (Fin 3) (Fin 3) K) Gm).mp (fun x y => by
      rw [← stdHermForm_eq_gramForm, hGv, hGv, hgH])
    rw [Matrix.mul_one] at h1
    exact h1
  have hGu' : Gm * uStar h Gm = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (Fin 3) (Fin 3) K rfl).mp hGu
  have hGA : Gm * (A : Matrix (Fin 3) (Fin 3) K) =
      c₁ • ((A' : Matrix (Fin 3) (Fin 3) K) * Gm.map h.bar) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    have e1 := hgτ (fun i => h.bar (u i))
    rw [antiunitaryMap_apply, antiunitaryMap_apply, ← hGv, ← hGv, bar_mulVec] at e1
    have e2 : (fun i => h.bar (h.bar (u i))) = u := funext fun i => h.bar_bar (u i)
    rw [e2] at e1
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, e1, Matrix.smul_mulVec,
      Matrix.mulVec_mulVec]
  set d := Gm.det with hd
  have hdbar : h.bar d * d = 1 := by
    have h1 := congrArg Matrix.det hGu
    rw [det_mul, CatFactsL4U4.UnitaryOut.uStar, det_transpose, show Gm.map h.bar =
      h.bar.mapMatrix Gm from rfl, ← RingHom.map_det, det_one] at h1
    exact h1
  have hd0 : d ≠ 0 := fun h0 => by rw [h0, mul_zero] at hdbar; exact zero_ne_one hdbar
  have hA0 : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hd2 : d ^ 2 = c₁ ^ 3 := by
    have h1 := congrArg Matrix.det hGA
    rw [det_mul, det_smul, det_mul, hdet, Fintype.card_fin, show Gm.map h.bar =
      h.bar.mapMatrix Gm from rfl, ← RingHom.map_det] at h1
    have h2 : d = c₁ ^ 3 * h.bar d := by
      apply mul_right_cancel₀ hA0
      rw [h1]
      ring
    have h3 : d * d = c₁ ^ 3 * (h.bar d * d) := by rw [← mul_assoc, ← h2]
    rw [hdbar, mul_one] at h3
    rw [sq]
    exact h3
  have hmm : ∀ M : Matrix (Fin 3) (Fin 3) K, (M.map h.bar).map h.bar = M := fun M => by
    ext i j
    simp [h.bar_bar]
  have hsm : ∀ (a : K) (M : Matrix (Fin 3) (Fin 3) K), (a • M).map h.bar = h.bar a • M.map h.bar :=
    fun a M => by
      ext i j
      simp
  have hGAbar : Gm.map h.bar * (A : Matrix (Fin 3) (Fin 3) K).map h.bar =
      h.bar c₁ • ((A' : Matrix (Fin 3) (Fin 3) K).map h.bar * Gm) := by
    have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M.map h.bar) hGA
    simp only [Matrix.map_mul, hsm, hmm] at h1
    exact h1
  have hNc : c₁ * h.bar c₁ = 1 := by
    have h1 : Gm * ((A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K).map h.bar) =
        (c₁ * h.bar c₁) • (((A' : Matrix (Fin 3) (Fin 3) K) *
          (A' : Matrix (Fin 3) (Fin 3) K).map h.bar) * Gm) := by
      rw [← Matrix.mul_assoc, hGA, Matrix.smul_mul, Matrix.mul_assoc, hGAbar, Matrix.mul_smul,
        smul_smul, Matrix.mul_assoc]
    rw [hAA, hA'A', hc1, hc1', one_smul, Matrix.mul_one, Matrix.one_mul] at h1
    have h2 : (1 - c₁ * h.bar c₁) • Gm = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact (sub_eq_zero.mp h3).symm
    · exfalso
      apply hd0
      rw [hd, h3, det_zero]
  set ν := d / c₁ with hν
  have hν0 : ν ≠ 0 := div_ne_zero hd0 hc₁
  have hν2 : ν ^ 2 = c₁ := by
    rw [hν, div_pow, hd2]
    field_simp
  have hν3 : ν ^ 3 = d := by
    rw [hν, div_pow, show d ^ 3 = d ^ 2 * d by ring, hd2]
    field_simp
  have hNν : h.bar ν * ν = 1 := by
    rw [hν, map_div₀, div_mul_div_comm, hdbar, mul_comm (h.bar c₁), hNc, div_one]
  have hνbar : h.bar ν = ν⁻¹ := eq_inv_of_mul_eq_one_left hNν
  have hu1 : (ν⁻¹ • Gm) * (ν • uStar h Gm) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hν0, one_smul, hGu']
  have hu2 : (ν • uStar h Gm) * (ν⁻¹ • Gm) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hν0, one_smul, hGu]
  set G' : GL (Fin 3) K := ⟨ν⁻¹ • Gm, ν • uStar h Gm, hu1, hu2⟩ with hG'
  have hG'mem : G' ∈ unitarySU p f K 3 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · change (ν⁻¹ • Gm).det = 1
      rw [det_smul, Fintype.card_fin, inv_pow, hν3, ← hd, inv_mul_cancel₀ hd0]
    · change ((ν⁻¹ • Gm).map h.bar)ᵀ * (ν⁻¹ • Gm) = 1
      rw [hsm, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_inv₀, hνbar,
        inv_inv, mul_inv_cancel₀ hν0, one_smul]
      exact hGu
  refine ⟨⟨G', hG'mem⟩, ?_⟩
  have hGT : Gm.map h.bar * Gmᵀ = 1 := by
    have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M.map h.bar) hGu'
    simp only [Matrix.map_mul, CatFactsL4U4.UnitaryOut.uStar, Matrix.transpose_map, hmm,
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar)] at h1
    exact h1
  change (ν⁻¹ • Gm) * (A : Matrix (Fin 3) (Fin 3) K) * (ν • uStar h Gm).map h.bar = A'
  rw [hsm, CatFactsL4U4.UnitaryOut.uStar, Matrix.transpose_map, hmm, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.mul_smul, hGA, Matrix.smul_mul, Matrix.mul_assoc, hGT, Matrix.mul_one,
    smul_smul, smul_smul, hνbar, ← hν2]
  rw [show ν⁻¹ * ν⁻¹ * ν ^ 2 = 1 by field_simp, one_smul]

end CFSG.ComponentClassification.GSThmB.CF23I

module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpU4

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut UnitaryConj HBlocks
  ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.LinearGroups
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry PSpL StabU

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem exists_real_frame_alt (hp2 : p ≠ 2) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -1) :
    ∃ (R : Matrix (Fin 4) (Fin 4) K) (t l : K), t ≠ 0 ∧ h.bar t = -t ∧ l ≠ 0 ∧
      uStar h R * R = t • omg ∧ l • ((A : Matrix (Fin 4) (Fin 4) K) * R.map h.bar) = R := by
  classical
  have : Finite K := h.finite
  set τ₀ := antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) with hτ₀
  have hμ : ∀ v, τ₀ (τ₀ v) = ((-1 : Kˣ) : K) • v := fun v => by
    rw [Units.val_neg, Units.val_one]
    exact antiunitaryMap_sq h _ (by rw [hAA, neg_one_smul]) v
  obtain ⟨-, ⟨b, hbN⟩, ⟨t, ht⟩, hmain⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    (h.prime.odd_of_ne_two hp2) (by rw [Module.finrank_fin_fun]; norm_num)
    (stdHermForm_isSymm h 4) (stdHermForm_separatingLeft h 4) τ₀ (antiunitaryMap_bijective h A)
    (stdHermForm_antiunitaryMap h hAu) (-1) hμ
  obtain ⟨-, hfinW, -, -, halt⟩ := hmain b t hbN ht
  obtain ⟨B, hBv, hBalt, hBnd, -, -⟩ := halt rfl
  obtain ⟨m, bW, hm, hb1, hb2, hb3⟩ := exists_blueprint_symplectic_basis B hBalt hBnd
  rw [hfinW, Module.finrank_fin_fun] at hm
  obtain rfl : m = 2 := by omega
  set bas : Fin 4 → conjFixed h ((b : K) • τ₀) :=
    ![bW (Sum.inl 0), bW (Sum.inl 1), bW (Sum.inr 0), bW (Sum.inr 1)] with hbas
  have hgram : ∀ j k : Fin 4, ((B (bas j) (bas k) : h.fixedField) : K) = omg j k := by
    have e3 := fun i j => congrArg (fun z : h.fixedField => (z : K)) (hb3 i j)
    have e1 := fun i j => congrArg (fun z : h.fixedField => (z : K)) (hb1 i j)
    have e2 := fun i j => congrArg (fun z : h.fixedField => (z : K)) (hb2 i j)
    have e4 : ∀ i j : Fin 2, ((B (bW (Sum.inr j)) (bW (Sum.inl i)) : h.fixedField) : K) =
        -(if i = j then 1 else 0) := by
      intro i j
      rw [← hBalt.neg_eq, Subfield.coe_neg, hb3]
      split_ifs <;> simp
    intro j k
    fin_cases j <;> fin_cases k <;>
      simp [hbas, omg, e1, e2, e3, e4]
  have hherm : ∀ j k : Fin 4, stdHermForm h 4 (bas j) (bas k) = t * omg j k := by
    intro j k
    rw [← hgram j k, hBv]
    field_simp
  have hfix : ∀ j : Fin 4, (b : K) • ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ
      fun i => h.bar ((bas j : Fin 4 → K) i)) = bas j := by
    intro j
    have := (mem_conjFixed.1 (bas j).2)
    rw [LinearMap.smul_apply] at this
    exact this
  set R : Matrix (Fin 4) (Fin 4) K := Matrix.of fun i j => (bas j : Fin 4 → K) i with hR
  have hR1 : uStar h R * R = (t : K) • omg := by
    ext j k
    rw [Matrix.smul_apply, smul_eq_mul, ← hherm j k, stdHermForm_apply]
    simp [uStar, Matrix.mul_apply, hR]
  refine ⟨R, t, b, Units.ne_zero t, ht, Units.ne_zero b, hR1, ?_⟩
  ext i j
  have := congrFun (hfix j) i
  rw [Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  change _ = (bas j : Fin 4 → K) i
  rw [← this]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hR, Matrix.of_apply]

include h in
theorem exists_real_frame_symm (hp2 : p ≠ 2) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = 1) :
    ∃ (R : Matrix (Fin 4) (Fin 4) K) (G : Matrix (Fin 4) (Fin 4) h.fixedField) (l : K),
      Gᵀ = G ∧ G.det ≠ 0 ∧ l ≠ 0 ∧ uStar h R * R = G.map h.fixedField.subtype ∧
      l • ((A : Matrix (Fin 4) (Fin 4) K) * R.map h.bar) = R := by
  classical
  have : Finite K := h.finite
  set τ₀ := antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) with hτ₀
  have hμ : ∀ v, τ₀ (τ₀ v) = ((1 : Kˣ) : K) • v := fun v => by
    rw [Units.val_one]
    exact antiunitaryMap_sq h _ (by rw [hAA, one_smul]) v
  obtain ⟨-, ⟨b, hbN⟩, ⟨t, ht⟩, hmain⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    (h.prime.odd_of_ne_two hp2) (by rw [Module.finrank_fin_fun]; norm_num)
    (stdHermForm_isSymm h 4) (stdHermForm_separatingLeft h 4) τ₀ (antiunitaryMap_bijective h A)
    (stdHermForm_antiunitaryMap h hAu) 1 hμ
  obtain ⟨-, hfinW, -, hsymm, -⟩ := hmain b t hbN ht
  obtain ⟨B, hBv, hBs, hBnd, -⟩ := hsymm rfl
  have : Module.Finite h.fixedField (conjFixed h ((b : K) • τ₀)) := finite_conjFixed
  have hfin4 : Module.finrank h.fixedField (conjFixed h ((b : K) • τ₀)) = 4 := by
    rw [hfinW, Module.finrank_fin_fun]
  set bW := Module.finBasisOfFinrankEq h.fixedField (conjFixed h ((b : K) • τ₀)) hfin4 with hbW
  set G : Matrix (Fin 4) (Fin 4) h.fixedField := Matrix.of fun i j => B (bW i) (bW j) with hG
  have hGt : Gᵀ = G := by
    ext i j
    simp only [hG, Matrix.transpose_apply, Matrix.of_apply]
    rw [hBs.eq (bW j) (bW i)]
  have hGdet : G.det ≠ 0 := by
    have h1 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bW).mp hBnd
    have e : LinearMap.BilinForm.toMatrix bW B = G := by
      ext i j
      rw [LinearMap.BilinForm.toMatrix_apply]
      rfl
    rwa [e] at h1
  have hfix : ∀ j : Fin 4, (b : K) • ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ
      fun i => h.bar ((bW j : Fin 4 → K) i)) = bW j := by
    intro j
    have := (mem_conjFixed.1 (bW j).2)
    rw [LinearMap.smul_apply] at this
    exact this
  set R : Matrix (Fin 4) (Fin 4) K := Matrix.of fun i j => (bW j : Fin 4 → K) i with hR
  have hR1 : uStar h R * R = G.map h.fixedField.subtype := by
    ext j k
    rw [Matrix.map_apply, hG, Matrix.of_apply, Subfield.coe_subtype, hBv, stdHermForm_apply]
    simp [uStar, Matrix.mul_apply, hR]
  refine ⟨R, G, b, hGt, hGdet, Units.ne_zero b, hR1, ?_⟩
  ext i j
  have := congrFun (hfix j) i
  rw [Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  change _ = (bW j : Fin 4 → K) i
  rw [← this]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hR, Matrix.of_apply]

include h in
theorem conj_glIncl_mem {R : GL (Fin 4) K} {t : K}
    (hR1' : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • omg)
    (M : StatedSp 2 h.fixedField) :
    R * glIncl h (spGL h.fixedField M) * R⁻¹ ∈ unitarySU p f K 4 := by
  have hRR : (R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hι₀v : ((R * glIncl h (spGL h.fixedField M) * R⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = (R : Matrix (Fin 4) (Fin 4) K) *
        ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    rw [Units.val_mul, Units.val_mul]
  have hspec :
      ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * omg *
          ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = omg ∧
        ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    obtain ⟨h1, h2⟩ := spGL_spec h.fixedField M
    rw [coe_glIncl]
    refine ⟨?_, ?_⟩
    · rw [← omg_map h.fixedField.subtype, ← Matrix.transpose_map, ← Matrix.map_mul,
        ← Matrix.map_mul, h1]
    · rw [show ((spGL h.fixedField M : GL (Fin 4) h.fixedField) :
          Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype =
          h.fixedField.subtype.mapMatrix ((spGL h.fixedField M : GL (Fin 4) h.fixedField) :
            Matrix (Fin 4) (Fin 4) h.fixedField) from rfl, ← RingHom.map_det, h2, map_one]
  rw [mem_unitarySU_iff h]
  obtain ⟨hs, hd⟩ := hspec
  refine ⟨?_, ?_⟩
  · rw [hι₀v, det_mul, det_mul, hd, mul_one, ← det_mul, hRR, det_one]
  · change uStar h _ * _ = 1
    have hX : uStar h ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) =
        ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ := by
      rw [uStar, map_bar_glIncl]
    have hRi : uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * uStar h (R : Matrix (Fin 4) (Fin 4) K)
        = 1 := by rw [← uStar_mul, hRR, uStar_one]
    rw [hι₀v, uStar_mul, uStar_mul, hX]
    calc uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          (((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
          uStar h (R : Matrix (Fin 4) (Fin 4) K)) *
          ((R : Matrix (Fin 4) (Fin 4) K) *
            ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
        uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          (((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
            (uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K)) *
            ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
      _ = uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          (uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K)) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
          rw [hR1', Matrix.mul_smul, Matrix.smul_mul, hs]
      _ = 1 := by
          rw [← Matrix.mul_assoc, hRi, Matrix.one_mul, hRR]

end CFSG.ComponentClassification.GSThmB.P211

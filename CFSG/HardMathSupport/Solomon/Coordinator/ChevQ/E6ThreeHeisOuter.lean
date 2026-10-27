module

public import CFSG.LieType.SeitzGeneration.OuterHeisWords
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.LieType.SeitzGeneration

variable {F : Type*} [Field F]

@[expose] def rowSL (s s' : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; s, 1, s'; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem rowSL_mul (s s' t t' : F) : rowSL s s' * rowSL t t' = rowSL (s + t) (s' + t') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowSL, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem rowSL_zero : (rowSL 0 0 : SpecialLinearGroup (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowSL]

theorem rowSL_inv (s s' : F) : (rowSL s s')⁻¹ = rowSL (-s) (-s') :=
  inv_eq_of_mul_eq_one_right (by rw [rowSL_mul]; simp [rowSL_zero])

theorem diagSL_mul_rowSL (a b d : F) (h : a * b * d = 1) (s s' : F) :
    diagSL a b d h * rowSL s s' = rowSL (b / a * s) (b / d * s') * diagSL a b d h := by
  have ha : a ≠ 0 := by rintro rfl; simp at h
  have hd : d ≠ 0 := by rintro rfl; simp at h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, rowSL, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem rowSL_mem_of_scale {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K) {g : F} (hg0 : g ≠ 0)
    (hg3 : g ^ 3 ≠ 1) {w₀ w₁ : F} (hw0 : w₀ ≠ 0) (hw1 : w₁ ≠ 0) (hw : rowSL w₀ w₁ ∈ K)
    (s s' : F) : rowSL s s' ∈ K := by
  let V : AddSubgroup (F × F) :=
    { carrier := {p | rowSL p.1 p.2 ∈ K}
      zero_mem' := by simp [rowSL_zero]
      add_mem' := fun {a b} ha hb => by simpa [rowSL_mul] using K.mul_mem ha hb
      neg_mem' := fun {a} ha => by simpa [rowSL_inv] using K.inv_mem ha }
  have hmemV : ∀ p : F × F, p ∈ V ↔ rowSL p.1 p.2 ∈ K := fun p => Iff.rfl
  have hscale : ∀ p ∈ V, ∀ ρ k : F, ρ ≠ 0 → k ≠ 0 → (ρ * p.1, k ^ 3 / ρ * p.2) ∈ V := by
    intro p hp ρ k hρ hk
    have hδ : k / ρ * k * (ρ / k ^ 2) = 1 := by field_simp
    have h := diagSL_mul_rowSL (k / ρ) k (ρ / k ^ 2) hδ p.1 p.2
    have h1 : k / (k / ρ) = ρ := by field_simp
    have h2 : k / (ρ / k ^ 2) = k ^ 3 / ρ := by field_simp
    rw [h1, h2] at h
    rw [hmemV]
    have : rowSL (ρ * p.1) (k ^ 3 / ρ * p.2) =
        diagSL (k / ρ) k (ρ / k ^ 2) hδ * rowSL p.1 p.2 *
          (diagSL (k / ρ) k (ρ / k ^ 2) hδ)⁻¹ := by
      rw [h, mul_inv_cancel_right]
    show rowSL (ρ * p.1) (k ^ 3 / ρ * p.2) ∈ K
    rw [this]
    exact K.mul_mem (K.mul_mem (hdiag _ _ _ _) hp) (K.inv_mem (hdiag _ _ _ _))
  have hwV : (w₀, w₁) ∈ V := hw
  have hx0 : ((1 - g ^ 3) * w₀, 0) ∈ V := by
    have h1 := hscale _ hwV (-g ^ 3) g (neg_ne_zero.2 (pow_ne_zero 3 hg0)) hg0
    have h2 := V.add_mem hwV h1
    have : ((w₀, w₁) + (-g ^ 3 * (w₀, w₁).1, g ^ 3 / -g ^ 3 * (w₀, w₁).2) : F × F) =
        ((1 - g ^ 3) * w₀, 0) := by
      ext
      · simp only [Prod.fst_add]; ring
      · simp only [Prod.snd_add]
        have : g ^ 3 / -g ^ 3 = -1 := by field_simp
        rw [this]; ring
    rwa [this] at h2
  have hy0 : (0, (1 - g ^ 3) * w₁) ∈ V := by
    have h1 := hscale _ hwV (-1) g (by norm_num) hg0
    have h2 := V.add_mem hwV h1
    have : ((w₀, w₁) + (-1 * (w₀, w₁).1, g ^ 3 / -1 * (w₀, w₁).2) : F × F) =
        (0, (1 - g ^ 3) * w₁) := by
      ext
      · simp only [Prod.fst_add]; ring
      · simp only [Prod.snd_add]; ring
    rwa [this] at h2
  have ha0 : (1 - g ^ 3) * w₀ ≠ 0 := mul_ne_zero (sub_ne_zero.2 (Ne.symm hg3)) hw0
  have hb0 : (1 - g ^ 3) * w₁ ≠ 0 := mul_ne_zero (sub_ne_zero.2 (Ne.symm hg3)) hw1
  have hX : ∀ x : F, (x, 0) ∈ V := by
    intro x
    by_cases hx : x = 0
    · subst hx; exact V.zero_mem
    · have := hscale _ hx0 (x / ((1 - g ^ 3) * w₀)) 1 (div_ne_zero hx ha0) one_ne_zero
      simp only [mul_zero] at this
      rwa [div_mul_cancel₀ _ ha0] at this
  have hY : ∀ y : F, (0, y) ∈ V := by
    intro y
    by_cases hy : y = 0
    · subst hy; exact V.zero_mem
    · have := hscale _ hy0 ((1 - g ^ 3) * w₁ / y) 1 (div_ne_zero hb0 hy) one_ne_zero
      simp only [mul_zero] at this
      have h3 : (1 : F) ^ 3 / ((1 - g ^ 3) * w₁ / y) * ((1 - g ^ 3) * w₁) = y := by
        field_simp
      rwa [h3] at this
  have h := V.add_mem (hX s) (hY s')
  have h' : (s, s') ∈ V := by simpa using h
  exact (hmemV (s, s')).1 h'

theorem rowSL_mem_of_transvection {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K)
    {T : SpecialLinearGroup (Fin 3) F} {κ : F}
    (hT : (T : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec ![1, 1, 1] ![3 * κ, 0, -(3 * κ)])
    (hTK : T ∈ K) {ξ : F} (hξ0 : ξ ≠ 0) :
    rowSL (3 * κ * (1 - (ξ ^ 3)⁻¹)) (-(3 * κ * (1 - (ξ ^ 3)⁻¹))) ∈ K := by
  have hδ : ξ * (ξ ^ 2)⁻¹ * ξ = 1 := by field_simp
  set s : F := 3 * κ * (1 - (ξ ^ 3)⁻¹) with hs
  have hTm : (T : Matrix (Fin 3) (Fin 3) F) =
      !![1 + 3 * κ, 0, -(3 * κ); 3 * κ, 1, -(3 * κ); 3 * κ, 0, 1 - 3 * κ] := by
    rw [hT]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply, Matrix.one_apply] <;> ring
  have e : rowSL s (-s) * (diagSL ξ (ξ ^ 2)⁻¹ ξ hδ * T) = T * diagSL ξ (ξ ^ 2)⁻¹ ξ hδ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hTm]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [rowSL, diagSL, hs] <;> field_simp <;> ring
  have h2 : rowSL s (-s) = T * diagSL ξ (ξ ^ 2)⁻¹ ξ hδ * (diagSL ξ (ξ ^ 2)⁻¹ ξ hδ * T)⁻¹ :=
    eq_mul_inv_of_mul_eq e
  rw [h2]
  exact K.mul_mem (K.mul_mem hTK (hdiag _ _ _ _)) (K.inv_mem (K.mul_mem (hdiag _ _ _ _) hTK))

theorem eq_top_of_comap_conjUnit' {K : Subgroup (SpecialLinearGroup (Fin 3) F)} (P : GL (Fin 3) F)
    (h : K.comap (conjUnit P) = ⊤) : K = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [← conjUnit_conjUnit_inv P g]
  exact Subgroup.mem_comap.1 (h ▸ Subgroup.mem_top (conjUnit P⁻¹ g))

theorem rowSL_coe (s s' : F) :
    ((rowSL s s' : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + vecMulVec (Pi.single 1 1) ![s, 0, s'] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowSL, vecMulVec_apply, Matrix.one_apply, Pi.single_apply]

theorem eq_top_of_rowSL {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hrow : ∀ s s' : F, rowSL s s' ∈ K) {m₁ m₂ : SpecialLinearGroup (Fin 3) F} (h₁ : m₁ ∈ K)
    (h₂ : m₂ ∈ K)
    (hdet : (m₁ : Matrix (Fin 3) (Fin 3) F) 0 1 * (m₂ : Matrix (Fin 3) (Fin 3) F) 2 1 ≠
      (m₂ : Matrix (Fin 3) (Fin 3) F) 0 1 * (m₁ : Matrix (Fin 3) (Fin 3) F) 2 1) : K = ⊤ := by
  classical
  set G : Matrix (Fin 3) (Fin 3) F :=
    !![0, (m₁ : Matrix (Fin 3) (Fin 3) F) 0 1, (m₂ : Matrix (Fin 3) (Fin 3) F) 0 1;
      1, (m₁ : Matrix (Fin 3) (Fin 3) F) 1 1, (m₂ : Matrix (Fin 3) (Fin 3) F) 1 1;
      0, (m₁ : Matrix (Fin 3) (Fin 3) F) 2 1, (m₂ : Matrix (Fin 3) (Fin 3) F) 2 1] with hGdef
  have hG : G.det ≠ 0 := by
    rw [hGdef, Matrix.det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons]
    intro h
    apply hdet
    linear_combination -h
  set g : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero G hG with hgdef
  have hg : (g : Matrix (Fin 3) (Fin 3) F) = G := rfl
  set Gi : Matrix (Fin 3) (Fin 3) F := ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hGi
  have hGiG : Gi * G = 1 := by rw [hGi, ← hg]; exact Units.inv_mul g
  have hGGi : G * Gi = 1 := by rw [hGi, ← hg]; exact Units.mul_inv g
  let mm : Fin 3 → SpecialLinearGroup (Fin 3) F := ![1, m₁, m₂]
  have hmm : ∀ i, mm i ∈ K := by
    intro i; fin_cases i
    exacts [K.one_mem, h₁, h₂]
  have hcol : ∀ i r, (mm i : Matrix (Fin 3) (Fin 3) F) r 1 = G r i := by
    intro i r; fin_cases i <;> fin_cases r <;> simp [mm, G]
  have key : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F),
      conjUnit g (SpecialLinearGroup.transvection hij c) ∈ K := by
    intro i j hij c
    set Mi : Matrix (Fin 3) (Fin 3) F := (mm i : Matrix (Fin 3) (Fin 3) F) with hMi
    set s : F := c * (Gi * Mi) j 0 with hs
    set s' : F := c * (Gi * Mi) j 2 with hs'
    have hj1 : (Gi * Mi) j 1 = 0 := by
      have : (Gi * Mi) j 1 = (Gi * G) j i := by
        simp only [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun b _ => by rw [hMi, hcol]
      rw [this, hGiG, Matrix.one_apply_ne (Ne.symm hij)]
    have hw : c • ((Pi.single j 1 : Fin 3 → F) ᵥ* (Gi * Mi)) = ![s, 0, s'] := by
      rw [Matrix.single_one_vecMul]
      ext l
      fin_cases l
      · simp [hs]
      · simp [hj1]
      · simp [hs']
    have hcolv : Mi.mulVec (Pi.single 1 1) = G.mulVec (Pi.single i 1) := by
      ext r
      simp only [Matrix.mulVec_single_one]
      exact hcol i r
    have e : conjUnit g (SpecialLinearGroup.transvection hij c) * mm i = mm i * rowSL s s' := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, conjUnit_coe,
        SpecialLinearGroup.transvection_coe, rowSL_coe, ← hMi, hg, ← hGi]
      have hs1 : (Matrix.single i j c : Matrix (Fin 3) (Fin 3) F) =
          c • vecMulVec (Pi.single i 1) (Pi.single j 1) := by
        rw [← Matrix.single_eq_single_vecMulVec_single, Matrix.smul_single, smul_eq_mul, mul_one]
      calc G * (1 + Matrix.single i j c) * Gi * Mi
          = (G * Gi) * Mi + G * Matrix.single i j c * Gi * Mi := by noncomm_ring
        _ = Mi + G * Matrix.single i j c * Gi * Mi := by rw [hGGi, Matrix.one_mul]
        _ = Mi + vecMulVec (G.mulVec (Pi.single i 1))
              (c • ((Pi.single j 1 : Fin 3 → F) ᵥ* (Gi * Mi))) := by
          rw [hs1, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_vecMulVec,
            Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul,
            Matrix.vecMulVec_smul]
        _ = Mi * (1 + vecMulVec (Pi.single 1 1) ![s, 0, s']) := by
          rw [hw, Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, hcolv]
    have h3 : conjUnit g (SpecialLinearGroup.transvection hij c) = mm i * rowSL s s' * (mm i)⁻¹ :=
      eq_mul_inv_of_mul_eq (by rw [e])
    rw [h3]
    exact K.mul_mem (K.mul_mem (hmm i) (hrow s s')) (K.inv_mem (hmm i))
  have htop : K.comap (conjUnit g) = ⊤ := by
    have h := (Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (K := F) (ι := Fin 3))
    rw [eq_top_iff, ← h, Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    exact key t.i t.j t.hij t.c
  exact eq_top_of_comap_conjUnit' g htop

theorem commute_conjUnit_of_intertwine {P : GL (Fin 3) F} {M N : Matrix (Fin 3) (Fin 3) F}
    {k : SpecialLinearGroup (Fin 3) F} (hMN : M * (P : Matrix (Fin 3) (Fin 3) F) = P * N)
    (hk : (k : Matrix (Fin 3) (Fin 3) F) * N = N * k) :
    (conjUnit P k : Matrix (Fin 3) (Fin 3) F) * M = M * conjUnit P k := by
  have hPP : (P : Matrix (Fin 3) (Fin 3) F) * ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 := Units.mul_inv P
  have hPP' : ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (P : Matrix (Fin 3) (Fin 3) F) =
      1 := Units.inv_mul P
  have hPi : ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M =
      N * ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    calc ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M
        = ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M *
          ((P : Matrix (Fin 3) (Fin 3) F) * ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
          rw [hPP, Matrix.mul_one]
      _ = ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (M * (P : Matrix (Fin 3) (Fin 3) F)) *
          ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by simp only [Matrix.mul_assoc]
      _ = ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((P : Matrix (Fin 3) (Fin 3) F) * N) *
          ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by rw [hMN]
      _ = N * ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
          rw [← Matrix.mul_assoc ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hPP',
            Matrix.one_mul]
  rw [conjUnit_coe]
  calc (P : Matrix (Fin 3) (Fin 3) F) * k * ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M
      = (P : Matrix (Fin 3) (Fin 3) F) * k *
          (((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M) := by simp only [Matrix.mul_assoc]
    _ = (P : Matrix (Fin 3) (Fin 3) F) * k *
          (N * ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by rw [hPi]
    _ = (P : Matrix (Fin 3) (Fin 3) F) * ((k : Matrix (Fin 3) (Fin 3) F) * N) *
          ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by simp only [Matrix.mul_assoc]
    _ = (P : Matrix (Fin 3) (Fin 3) F) * (N * (k : Matrix (Fin 3) (Fin 3) F)) *
          ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by rw [hk]
    _ = ((P : Matrix (Fin 3) (Fin 3) F) * N) * k *
          ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by simp only [Matrix.mul_assoc]
    _ = (M * (P : Matrix (Fin 3) (Fin 3) F)) * k *
          ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by rw [hMN]
    _ = M * ((P : Matrix (Fin 3) (Fin 3) F) * k *
          ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by simp only [Matrix.mul_assoc]

theorem heisC_mul_diag {c b : F} (hb : b ≠ 0) (hbb : b⁻¹ * 1 * b = 1) :
    heisC c * (diagSL b⁻¹ 1 b hbb : Matrix (Fin 3) (Fin 3) F) =
      (diagSL b⁻¹ 1 b hbb : Matrix (Fin 3) (Fin 3) F) * (b⁻¹ • heisC (c * b ^ 3)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, diagSL, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem diagSL_mul_mul_diagSL_apply (a b d a' b' d' : F) (h : a * b * d = 1)
    (h' : a' * b' * d' = 1) (m : SpecialLinearGroup (Fin 3) F) (i j : Fin 3) :
    ((diagSL a b d h * m * diagSL a' b' d' h' : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) i j =
      ![a, b, d] i * (m : Matrix (Fin 3) (Fin 3) F) i j * ![a', b', d'] j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [diagSL]

theorem eq_top_of_torus_centralizer_noncube [Finite F] {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    {ω c : F} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hc : ¬ ∃ μ : F, μ ^ 3 = c)
    (h4 : 4 < Nat.card F) (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K)
    (hcent : ∀ k : SpecialLinearGroup (Fin 3) F,
      (k : Matrix (Fin 3) (Fin 3) F) * heisC c = heisC c * k → k ∈ K) : K = ⊤ := by
  have h3 : (3 : F) ≠ 0 := by
    intro h
    apply hω1
    have h2 : (ω - 1) ^ 2 = 0 := by linear_combination hω - ω * h
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h]; norm_num⟩
  have hc1 : c - 1 ≠ 0 := fun h => hc ⟨1, by linear_combination (-1 : F) * h⟩
  obtain ⟨b, hb0, hb3⟩ := exists_pow_three_ne_one h4
  have hcb : c * b ^ 3 - 1 ≠ 0 := by
    intro h
    apply hc
    refine ⟨b⁻¹, ?_⟩
    field_simp
    linear_combination (-1 : F) * h
  have hb31 : b ^ 3 - 1 ≠ 0 := sub_ne_zero.2 hb3
  have hγ₁ : (-(ω + 2)) ^ 2 + 3 * (-(ω + 2)) + 3 = 0 := by linear_combination hω
  have hγ₂ : (-(ω ^ 2 + 2)) ^ 2 + 3 * (-(ω ^ 2 + 2)) + 3 = 0 := by
    linear_combination (ω ^ 2 - ω + 1) * hω
  have hsum : -(ω + 2) + -(ω ^ 2 + 2) = -3 := by linear_combination (-1 : F) * hω
  set κ : F := 1 / (c - 1) - 1 / (c * b ^ 3 - 1) with hκdef
  have hκ : κ ≠ 0 := by
    have : κ = c * (b ^ 3 - 1) / ((c - 1) * (c * b ^ 3 - 1)) := by
      rw [hκdef]; field_simp; ring
    rw [this]
    exact div_ne_zero (mul_ne_zero hc0 hb31) (mul_ne_zero hc1 hcb)
  have hbb : b⁻¹ * 1 * b = 1 := by field_simp
  have hY : ∀ (γ : F) (hγ : γ ^ 2 + 3 * γ + 3 = 0), outerYSL hγ (γ / (c - 1)) ∈ K := by
    intro γ hγ
    have hs : (c - 1) * (γ / (c - 1)) = γ := by field_simp
    exact hcent _ (outerY_comm hs)
  have hY' : ∀ (γ : F) (hγ : γ ^ 2 + 3 * γ + 3 = 0),
      outerYSL hγ (γ / (c * b ^ 3 - 1)) ∈ K := by
    intro γ hγ
    have hs' : (c * b ^ 3 - 1) * (γ / (c * b ^ 3 - 1)) = γ := by field_simp
    have hP : diagSL b⁻¹ 1 b hbb ∈ K := hdiag _ _ _ _
    have hcomm := commute_conjUnit_of_intertwine
      (P := SpecialLinearGroup.toGL (diagSL b⁻¹ 1 b hbb)) (M := heisC c)
      (N := b⁻¹ • heisC (c * b ^ 3)) (k := outerYSL hγ (γ / (c * b ^ 3 - 1)))
      (by rw [SpecialLinearGroup.coe_GL_coe_matrix]; exact heisC_mul_diag hb0 hbb)
      (by
        show outerY γ (γ / (c * b ^ 3 - 1)) * (b⁻¹ • heisC (c * b ^ 3)) =
          (b⁻¹ • heisC (c * b ^ 3)) * outerY γ (γ / (c * b ^ 3 - 1))
        rw [Matrix.mul_smul, Matrix.smul_mul, outerY_comm hs'])
    rw [conjUnit_toGL] at hcomm
    have hk := hcent _ hcomm
    have e : outerYSL hγ (γ / (c * b ^ 3 - 1)) =
        (diagSL b⁻¹ 1 b hbb)⁻¹ * (diagSL b⁻¹ 1 b hbb * outerYSL hγ (γ / (c * b ^ 3 - 1)) *
          (diagSL b⁻¹ 1 b hbb)⁻¹) * diagSL b⁻¹ 1 b hbb := by group
    rw [e]
    exact K.mul_mem (K.mul_mem (K.inv_mem hP) hk) hP
  have htau : ∀ (γ : F) (hγ : γ ^ 2 + 3 * γ + 3 = 0), outerTauSL γ κ ∈ K := by
    intro γ hγ
    have e : outerTauSL γ κ =
        outerYSL hγ (γ / (c - 1)) * (outerYSL hγ (γ / (c * b ^ 3 - 1)))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      apply Subtype.ext
      have h1 : γ / (c - 1) = γ / (c * b ^ 3 - 1) + κ * γ := by
        rw [hκdef]; field_simp; ring
      have h2 := outerY_eq_tau hγ (γ / (c * b ^ 3 - 1)) κ
      rw [← h1] at h2
      exact h2.symm
    rw [e]
    exact K.mul_mem (hY γ hγ) (K.inv_mem (hY' γ hγ))
  have hT0K : outerTauSL (-(ω + 2)) κ * outerTauSL (-(ω ^ 2 + 2)) κ ∈ K :=
    K.mul_mem (htau _ hγ₁) (htau _ hγ₂)
  have hT0m : ((outerTauSL (-(ω + 2)) κ * outerTauSL (-(ω ^ 2 + 2)) κ :
      SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + vecMulVec ![1, 1, 1] ![3 * κ, 0, -(3 * κ)] := outerTau_mul hsum κ
  have hs0 : 3 * κ * (1 - (b ^ 3)⁻¹) ≠ 0 := by
    have : 1 - (b ^ 3)⁻¹ ≠ 0 := by
      intro h
      apply hb3
      field_simp at h
      linear_combination h
    exact mul_ne_zero (mul_ne_zero h3 hκ) this
  have hrow : ∀ s s' : F, rowSL s s' ∈ K :=
    rowSL_mem_of_scale hdiag hb0 hb3 hs0 (neg_ne_zero.2 hs0)
      (rowSL_mem_of_transvection hdiag hT0m hT0K hb0)
  obtain ⟨e, he0, he1, he2, -⟩ := exists_ne_four h4 0 1 (-1) 0
  have he0' : e ≠ 0 := he0
  have hee : e ^ 2 ≠ 1 := by
    intro h
    have : (e - 1) * (e + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact he1 (sub_eq_zero.1 h1)
    · exact he2 (eq_neg_of_add_eq_zero_left h1)
  have hee' : e⁻¹ * 1 * e = 1 := by field_simp
  have hee'' : e * 1 * e⁻¹ = 1 := by field_simp
  set γ₁ : F := -(ω + 2) with hγ₁def
  have hγ0 : γ₁ ≠ 0 := by
    intro h
    rw [h] at hγ₁
    apply h3
    linear_combination hγ₁
  set Y : SpecialLinearGroup (Fin 3) F := outerYSL hγ₁ (γ₁ / (c - 1)) with hYdef
  have hYK : Y ∈ K := hY γ₁ hγ₁
  have hm₂K : diagSL e⁻¹ 1 e hee' * Y * diagSL e 1 e⁻¹ hee'' ∈ K :=
    K.mul_mem (K.mul_mem (hdiag _ _ _ _) hYK) (hdiag _ _ _ _)
  refine eq_top_of_rowSL hrow hYK hm₂K ?_
  have hs1 : γ₁ / (c - 1) ≠ 0 := div_ne_zero hγ0 hc1
  have hs2 : γ₁ / (c - 1) + γ₁ ≠ 0 := by
    have : γ₁ / (c - 1) + γ₁ = γ₁ * c / (c - 1) := by field_simp; ring
    rw [this]
    exact div_ne_zero (mul_ne_zero hγ0 hc0) hc1
  have hsub : e - e⁻¹ ≠ 0 := by
    intro h
    apply hee
    field_simp at h
    linear_combination h
  rw [diagSL_mul_mul_diagSL_apply, diagSL_mul_mul_diagSL_apply]
  have hY01 : (Y : Matrix (Fin 3) (Fin 3) F) 0 1 = -(γ₁ / (c - 1)) - γ₁ := by
    simp [hYdef, outerYSL, outerY]
  have hY21 : (Y : Matrix (Fin 3) (Fin 3) F) 2 1 = -(γ₁ / (c - 1)) := by
    simp [hYdef, outerYSL, outerY]
  rw [hY01, hY21]
  intro h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  have h' : γ₁ / (c - 1) * (γ₁ / (c - 1) + γ₁) * (e - e⁻¹) = 0 := by linear_combination h
  exact mul_ne_zero (mul_ne_zero hs1 hs2) hsub h'

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end

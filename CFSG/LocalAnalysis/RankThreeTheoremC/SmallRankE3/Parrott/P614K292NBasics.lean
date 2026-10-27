module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292N

open CFSG.Open Subgroup Matrix
open CFSG.RankThree.PartTwo.Sec4 hiding diagHom coe_diagHom diagHom_injective
open CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292

variable {K : Type} [Field K]

@[expose] noncomputable def conjTorus (n : ℕ) (P : GL (Fin 3) K) : Subgroup (GL (Fin 3) K) :=
  (torus3 (rootsOfUnity n K)).map (MulAut.conj P).toMonoidHom

theorem mem_conjTorus {n : ℕ} {P g : GL (Fin 3) K} :
    g ∈ conjTorus n P ↔ P⁻¹ * g * P ∈ torus3 (rootsOfUnity n K) := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ht
  · intro h
    exact ⟨P⁻¹ * g * P, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem diagHom_apply_self (d : Fin 3 → Kˣ) (i : Fin 3) :
    ((diagHom 3 d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i = d i := by
  rw [coe_diagHom, diagonal_apply_eq]

theorem isDiag_of_mem_torus3 {M : Subgroup Kˣ} {t : GL (Fin 3) K} (ht : t ∈ torus3 M) :
    (t : Matrix (Fin 3) (Fin 3) K).IsDiag := by
  obtain ⟨d, -, -, rfl⟩ := (mem_torus3 M).1 ht
  rw [coe_diagHom]
  exact isDiag_diagonal _

theorem det_of_mem_torus3 {M : Subgroup Kˣ} {t : GL (Fin 3) K} (ht : t ∈ torus3 M) :
    (t : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  obtain ⟨d, -, hd, rfl⟩ := (mem_torus3 M).1 ht
  rw [det_diagHom_three, ← Units.val_mul, ← Units.val_mul, hd, Units.val_one]

theorem pow_eq_one_of_mem_torus3 {n : ℕ} {t : GL (Fin 3) K}
    (ht : t ∈ torus3 (rootsOfUnity n K)) : t ^ n = 1 := by
  obtain ⟨d, hdM, -, rfl⟩ := (mem_torus3 _).1 ht
  rw [← map_pow]
  have : d ^ n = 1 := funext fun i => (mem_rootsOfUnity _ _).1 (hdM i)
  rw [this, map_one]

theorem mem_torus3_of_isDiag {n : ℕ} (hn : n ≠ 0) {t : GL (Fin 3) K}
    (hd : (t : Matrix (Fin 3) (Fin 3) K).IsDiag) (hdet : (t : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hpow : t ^ n = 1) : t ∈ torus3 (rootsOfUnity n K) := by
  set c : Fin 3 → K := fun i => (t : Matrix (Fin 3) (Fin 3) K) i i
  have ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal c := hd.diagonal_diag.symm
  have hprod : c 0 * c 1 * c 2 = 1 := by
    rw [← hdet, ht, det_diagonal, Fin.prod_univ_three]
  have h0 : c 0 * c 1 * c 2 ≠ 0 := by
    rw [hprod]
    exact one_ne_zero
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i
    fin_cases i
    · exact left_ne_zero_of_mul (left_ne_zero_of_mul h0)
    · exact right_ne_zero_of_mul (left_ne_zero_of_mul h0)
    · exact right_ne_zero_of_mul h0
  have hpow' : ∀ i, c i ^ n = 1 := by
    intro i
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) i i) hpow
    simp only [Units.val_pow_eq_pow_val, ht, diagonal_pow, Units.val_one] at h
    simpa [diagonal_apply_eq] using h
  set d : Fin 3 → Kˣ := fun i => Units.mk0 (c i) (hc0 i)
  refine (mem_torus3 _).2 ⟨d, fun i => ?_, Units.ext ?_, Units.ext ?_⟩
  · rw [mem_rootsOfUnity]
    exact Units.ext (by simp [d, hpow' i])
  · simp [d, hprod]
  · rw [coe_diagHom, ht]
    rfl

theorem commute_of_mem_torus3 {M : Subgroup Kˣ} {s t : GL (Fin 3) K} (hs : s ∈ torus3 M)
    (ht : t ∈ torus3 M) : s * t = t * s :=
  torus3_comm M hs ht

theorem diagHom_mul_comm_of_mem_torus3 {M : Subgroup Kˣ} (d : Fin 3 → Kˣ) {t : GL (Fin 3) K}
    (ht : t ∈ torus3 M) : diagHom 3 d * t = t * diagHom 3 d := by
  obtain ⟨e, -, -, rfl⟩ := (mem_torus3 M).1 ht
  rw [← map_mul, ← map_mul, mul_comm]

theorem card_torus3_three {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) : Nat.card (torus3 (rootsOfUnity 3 K)) = 9 := by
  have := hK.finite
  rw [card_torus3, card_rootsOfUnity_three hK hq]
  norm_num

theorem card_conjTorus (n : ℕ) (P : GL (Fin 3) K) :
    Nat.card (conjTorus n P) = Nat.card (torus3 (rootsOfUnity n K)) :=
  card_map_of_injective (MulAut.conj P).injective

theorem commute_of_mem_conjTorus {n : ℕ} {P s t : GL (Fin 3) K} (hs : s ∈ conjTorus n P)
    (ht : t ∈ conjTorus n P) : s * t = t * s := by
  rw [mem_conjTorus] at hs ht
  have h := commute_of_mem_torus3 hs ht
  calc s * t = P * ((P⁻¹ * s * P) * (P⁻¹ * t * P)) * P⁻¹ := by group
    _ = P * ((P⁻¹ * t * P) * (P⁻¹ * s * P)) * P⁻¹ := by rw [h]
    _ = t * s := by group

theorem pow_eq_one_of_mem_conjTorus {n : ℕ} {P g : GL (Fin 3) K} (hg : g ∈ conjTorus n P) :
    g ^ n = 1 := by
  rw [mem_conjTorus] at hg
  have h := pow_eq_one_of_mem_torus3 hg
  have e : (P⁻¹ * g * P) ^ n = P⁻¹ * g ^ n * P := by
    rw [show P⁻¹ * g * P = (MulAut.conj P⁻¹) g by simp [MulAut.conj_apply], ← map_pow]
    simp [MulAut.conj_apply]
  rw [e] at h
  calc g ^ n = P * (P⁻¹ * g ^ n * P) * P⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem conjTorus_mul_diagHom (n : ℕ) (P : GL (Fin 3) K) (d : Fin 3 → Kˣ) :
    conjTorus n (P * diagHom 3 d) = conjTorus n P := by
  ext g
  rw [mem_conjTorus, mem_conjTorus]
  have e : (P * diagHom 3 d)⁻¹ * g * (P * diagHom 3 d) =
      (diagHom 3 d)⁻¹ * (P⁻¹ * g * P) * diagHom 3 d := by group
  rw [e]
  set D := diagHom 3 d
  set X := P⁻¹ * g * P
  constructor
  · intro h
    have h' := diagHom_mul_comm_of_mem_torus3 d h
    have hX : X = D⁻¹ * X * D := by
      calc X = D * (D⁻¹ * X * D) * D⁻¹ := by group
        _ = (D⁻¹ * X * D) * D * D⁻¹ := by rw [h']
        _ = D⁻¹ * X * D := by group
    rw [hX]
    exact h
  · intro h
    have h' := diagHom_mul_comm_of_mem_torus3 d h
    have hX : D⁻¹ * X * D = X := by
      rw [mul_assoc, ← h', ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hX]
    exact h

theorem exists_sep_torus3_three {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (i j : Fin 3)
    (hij : i ≠ j) : ∃ u ∈ torus3 (rootsOfUnity 3 K),
      (u : Matrix (Fin 3) (Fin 3) K) i i ≠ (u : Matrix (Fin 3) (Fin 3) K) j j := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  set t : Kˣ := Units.mk0 τ hτ0
  have ht3 : t ^ 3 = 1 := Units.ext (by simp [t, hτ])
  refine ⟨diagHom 3 ![1, t, t ^ 2], (mem_torus3 _).2 ⟨_, fun k => ?_, ?_, rfl⟩, ?_⟩
  · rw [mem_rootsOfUnity]
    fin_cases k
    · simp
    · simpa using ht3
    · change (t ^ 2) ^ 3 = 1
      rw [← pow_mul, mul_comm, pow_mul, ht3, one_pow]
  · change 1 * t * t ^ 2 = 1
    rw [one_mul, ← pow_succ', ht3]
  · rw [diagHom_apply_self, diagHom_apply_self]
    have e : ∀ k, ((![1, t, t ^ 2] k : Kˣ) : K) = ![1, τ, τ ^ 2] k := by
      intro k
      fin_cases k <;> simp [t]
    rw [e, e]
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | simp [hτ1, hτ2, hττ2, Ne.symm hτ1, Ne.symm hτ2, Ne.symm hττ2]

theorem exists_sep_torus3_two (h2 : (2 : K) ≠ 0) (i j : Fin 3) (hij : i ≠ j) :
    ∃ u ∈ torus3 (rootsOfUnity 2 K),
      (u : Matrix (Fin 3) (Fin 3) K) i i ≠ (u : Matrix (Fin 3) (Fin 3) K) j j := by
  have hne : (1 : K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have hmem : ∀ e : Fin 3 → Kˣ, (∀ k, e k = 1 ∨ e k = -1) → e 0 * e 1 * e 2 = 1 →
      diagHom 3 e ∈ torus3 (rootsOfUnity 2 K) := by
    intro e he hprod
    refine (mem_torus3 _).2 ⟨e, fun k => ?_, hprod, rfl⟩
    rw [mem_rootsOfUnity]
    rcases he k with h | h <;> rw [h] <;> simp
  have key : ∀ i : Fin 3, ∃ e : Fin 3 → Kˣ, diagHom 3 e ∈ torus3 (rootsOfUnity 2 K) ∧
      ((e i : Kˣ) : K) = 1 ∧ ∀ j, j ≠ i → ((e j : Kˣ) : K) = -1 := by
    intro i
    fin_cases i
    · refine ⟨![1, -1, -1], hmem _ (fun k => by fin_cases k <;> simp) (by simp), by simp,
        fun j hj => ?_⟩
      fin_cases j
      · exact absurd rfl hj
      · simp
      · simp
    · refine ⟨![-1, 1, -1], hmem _ (fun k => by fin_cases k <;> simp) (by simp), by simp,
        fun j hj => ?_⟩
      fin_cases j
      · simp
      · exact absurd rfl hj
      · simp
    · refine ⟨![-1, -1, 1], hmem _ (fun k => by fin_cases k <;> simp) (by simp), by simp,
        fun j hj => ?_⟩
      fin_cases j
      · simp
      · simp
      · exact absurd rfl hj
  obtain ⟨e, he, hei, hej⟩ := key i
  refine ⟨diagHom 3 e, he, ?_⟩
  rw [diagHom_apply_self, diagHom_apply_self, hei, hej j (Ne.symm hij)]
  exact hne

theorem colMat_mulVec_single (b : Fin 3 → Fin 3 → K) (i : Fin 3) :
    colMat b *ᵥ Pi.single i 1 = b i := by
  ext r
  simp [colMat, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem frameGroupOf_eq_conjTorus {n : ℕ} (hn : n ≠ 0) {b : Fin 3 → Fin 3 → K}
    {P : GL (Fin 3) K} (hP : (P : Matrix (Fin 3) (Fin 3) K) = colMat b) :
    frameGroupOf n b = conjTorus n P := by
  ext g
  rw [mem_frameGroupOf, mem_conjTorus]
  constructor
  · rintro ⟨hdet, hg⟩
    choose c hc hgc using hg
    have hgP : (g : Matrix (Fin 3) (Fin 3) K) * P = P * diagonal c := by
      rw [hP]
      exact mul_colMat_eq hgc
    have hdiag : ((P⁻¹ * g * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal c := by
      rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hgP, ← Matrix.mul_assoc,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    refine mem_torus3_of_isDiag hn (by rw [hdiag]; exact isDiag_diagonal _) ?_ ?_
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, hdiag, diagonal_pow, Units.val_one, ← diagonal_one]
      congr 1
      funext i
      exact hc i
  · intro h
    obtain ⟨d, hdM, hd, hdg⟩ := (mem_torus3 _).1 h
    have hg : g = P * diagHom 3 d * P⁻¹ := by
      rw [← hdg]
      group
    subst hg
    refine ⟨?_, fun i => ⟨d i, ?_, ?_⟩⟩
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one, one_mul, det_diagHom_three,
        ← Units.val_mul, ← Units.val_mul, hd, Units.val_one]
    · have := (mem_rootsOfUnity _ _).1 (hdM i)
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    · have hbi : b i = (P : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single i 1 := by
        rw [hP, colMat_mulVec_single]
      rw [hbi, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.mul_assoc, ← Units.val_mul P⁻¹ P, inv_mul_cancel, Units.val_one, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, coe_diagHom, diagonal_mulVec_single, mul_one,
        ← Matrix.mulVec_smul]
      congr 1
      ext r
      by_cases hr : r = i
      · subst hr
        simp
      · simp [Pi.single_apply, hr]

theorem conj_mem_frameGroupOf {n : ℕ} {b : Fin 3 → Fin 3 → K} {g e : GL (Fin 3) K}
    (he : e ∈ frameGroupOf n b)
    (hg : ∀ i, ∃ j, ∃ c : K, b i = c • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ b j)) :
    g * e * g⁻¹ ∈ frameGroupOf n b := by
  obtain ⟨hdet, he⟩ := he
  refine ⟨?_, fun i => ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
  · obtain ⟨j, c, hc⟩ := hg i
    obtain ⟨d, hd, hed⟩ := he j
    refine ⟨d, hd, ?_⟩
    have key : ((g * e * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ b j) = d • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ b j) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul,
        ← Matrix.mulVec_mulVec, hed, Matrix.mulVec_smul]
    rw [hc, Matrix.mulVec_smul, key, smul_comm]

section Frame

variable {π : Bool} {p f : ℕ}

theorem linearIndependent_yFrame (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) {v : Fin 3 → K} (hv : v ≠ 0) :
    LinearIndependent K (yFrame y v) := by
  obtain ⟨ℓ, hℓ, hcube⟩ := hT.not_cube hK hq
  rw [yFrame_eq]
  exact linearIndependent_cyclic hcube hℓ hv

theorem yFrame_eq_smul_mulVec (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) (v : Fin 3 → K) (i : Fin 3) :
    ∃ j, ∃ c : K, yFrame y v i = c • ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ yFrame y v j) := by
  obtain ⟨ℓ, hℓ, -⟩ := hT.not_cube hK hq
  have h2 : (y : Matrix (Fin 3) (Fin 3) K) *ᵥ ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      ((y : Matrix (Fin 3) (Fin 3) K) ^ 2) *ᵥ v := by
    rw [Matrix.mulVec_mulVec, sq]
  have h3 : (y : Matrix (Fin 3) (Fin 3) K) *ᵥ (((y : Matrix (Fin 3) (Fin 3) K) ^ 2) *ᵥ v) =
      (ℓ : K) • v := by
    rw [Matrix.mulVec_mulVec, ← pow_succ', hℓ, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [yFrame_eq]
  fin_cases i
  · refine ⟨2, (ℓ : K)⁻¹, ?_⟩
    show v = (ℓ : K)⁻¹ • ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((y : Matrix (Fin 3) (Fin 3) K) ^ 2) *ᵥ v))
    rw [h3, smul_smul, inv_mul_cancel₀ ℓ.ne_zero, one_smul]
  · refine ⟨0, 1, ?_⟩
    show (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v = (1 : K) • ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
    rw [one_smul]
  · refine ⟨1, 1, ?_⟩
    show ((y : Matrix (Fin 3) (Fin 3) K) ^ 2) *ᵥ v =
      (1 : K) • ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ v))
    rw [one_smul, h2]

theorem exists_mul_diagHom_mem_glPi (hU : UnitaryFieldData p f K) {b : Fin 3 → Fin 3 → K}
    {P : GL (Fin 3) K} (hP : (P : Matrix (Fin 3) (Fin 3) K) = colMat b)
    (horth : ∀ i j : Fin 3, i ≠ j → ∑ k, b i k ^ p ^ f * b j k = 0) :
    ∃ d : Fin 3 → Kˣ, P * diagHom 3 d ∈ glPi false 3 (p ^ f) K := by
  set G : Matrix (Fin 3) (Fin 3) K :=
    ((P : Matrix (Fin 3) (Fin 3) K).map hU.bar)ᵀ * (P : Matrix (Fin 3) (Fin 3) K) with hG
  have hGij : ∀ i j, G i j = ∑ k, b i k ^ p ^ f * b j k := by
    intro i j
    simp [hG, hP, Matrix.mul_apply, colMat, hU.bar_apply]
  have hGdiag : G.IsDiag := fun i j hij => (hGij i j).trans (horth i j hij)
  have hPdet : (P : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := P.det_ne_zero
  have hGdet : G.det ≠ 0 := by
    have hmap : ((P : Matrix (Fin 3) (Fin 3) K).map hU.bar).det =
        hU.bar (P : Matrix (Fin 3) (Fin 3) K).det :=
      (RingHom.map_det hU.bar _).symm
    rw [hG, det_mul, det_transpose, hmap]
    exact mul_ne_zero ((hU.bar_eq_zero_iff).not.mpr hPdet) hPdet
  have hGii : ∀ i, G i i ≠ 0 := by
    intro i h0
    apply hGdet
    rw [← hGdiag.diagonal_diag, det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  have hGfix : ∀ i, hU.bar (G i i) = G i i := by
    intro i
    rw [hGij, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← hU.bar_apply (b i k), hU.bar_bar, mul_comm]
  have hfix : ∀ i, (G i i)⁻¹ ∈ hU.fixedField := fun i => by
    rw [hU.mem_fixedField, map_inv₀, hGfix]
  choose c hc using fun i => hU.normHom_surjective ⟨(G i i)⁻¹, hfix i⟩
  have hc' : ∀ i, c i * hU.bar (c i) = (G i i)⁻¹ := fun i => by
    have := congrArg Subtype.val (hc i)
    rwa [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] at this
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h0
    have := hc' i
    rw [h0, zero_mul] at this
    exact inv_ne_zero (hGii i) this.symm
  refine ⟨fun i => Units.mk0 (c i) (hc0 i), ?_⟩
  rw [mem_glPi_false hU, Units.val_mul, coe_diagHom, Matrix.map_mul, Matrix.transpose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc _ (P : Matrix (Fin 3) (Fin 3) K), ← hG,
    ← hGdiag.diagonal_diag, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  simp only [Units.val_mk0, Matrix.diag_apply]
  calc hU.bar (c i) * (G i i * c i) = (c i * hU.bar (c i)) * G i i := by ring
    _ = 1 := by rw [hc' i, inv_mul_cancel₀ (hGii i)]

theorem exists_glPi_frame (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {y : GL (Fin 3) K}
    (hT : IsTypeThree π (p ^ f) K y) {v : Fin 3 → K} (hv : v ≠ 0)
    (horth : π = false → YFrameOrth (p ^ f) y v) :
    ∃ P ∈ glPi π 3 (p ^ f) K, ∀ n : ℕ, n ≠ 0 → frameGroupOf n (yFrame y v) = conjTorus n P := by
  have hli := linearIndependent_yFrame hK hq hT hv
  set P₀ : GL (Fin 3) K := (isUnit_colMat hli).unit
  have hP₀b : (P₀ : Matrix (Fin 3) (Fin 3) K) = colMat (yFrame y v) := (isUnit_colMat hli).unit_spec
  cases π
  · obtain ⟨d, hd⟩ := exists_mul_diagHom_mem_glPi hK.unitary hP₀b (horth rfl)
    refine ⟨P₀ * diagHom 3 d, hd, fun n hn => ?_⟩
    rw [conjTorus_mul_diagHom]
    exact frameGroupOf_eq_conjTorus hn hP₀b
  · exact ⟨P₀, mem_glPi_true _ _, fun n hn => frameGroupOf_eq_conjTorus hn hP₀b⟩

theorem torus3_three_le_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    torus3 (rootsOfUnity 3 K) ≤ slPi π 3 (p ^ f) K := by
  intro t ht
  have hdet := det_of_mem_torus3 ht
  cases π
  · have h := hK.unitary
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    obtain ⟨d, hdM, -, rfl⟩ := (mem_torus3 _).1 ht
    rw [coe_diagHom, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have h3 : ((d i : Kˣ) : K) ^ 3 = 1 := by
      have := (mem_rootsOfUnity _ _).1 (hdM i)
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    rw [h.bar_apply, ← pow_succ]
    exact pow_succ_eq_one_of_modThree hq h3
  · rw [mem_slPi_true]
    exact hdet

theorem conjTorus_le_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {P : GL (Fin 3) K}
    (hP : P ∈ glPi π 3 (p ^ f) K) : conjTorus 3 P ≤ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rintro _ ⟨t, ht, rfl⟩
  exact conj_mem_slPi hπ hP (torus3_three_le_slPi hK hq ht)

theorem threeFrame_mem_frameCands (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) {v : Fin 3 → K} (hv : v ≠ 0)
    (horth : π = false → YFrameOrth (p ^ f) y v) :
    threeFrame y v ∈ frameCands π (p ^ f) y := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨P, hP, hPn⟩ := exists_glPi_frame hK hq hT hv horth
  have h3 : threeFrame y v = conjTorus 3 P := hPn 3 (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, fun e he => ?_⟩
  · rw [h3]
    exact conjTorus_le_slPi hK hq hP
  · rw [h3]
    exact ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (commute_of_mem_conjTorus a.2 b.2),
      fun x hx => pow_eq_one_of_mem_conjTorus hx⟩
  · rw [h3, card_conjTorus, card_torus3_three hK hq]
  · rintro g ⟨⟨c, rfl⟩, hg⟩
    refine ⟨((mem_slPi_iff hπ).1 hg).2, fun i => ⟨c, ?_, ?_⟩⟩
    · have hdet := ((mem_slPi_iff hπ).1 hg).2
      have h1 : ((Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.scalar (Fin 3) c) : Kˣ) : K) = 1 := by
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        exact hdet
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
        Units.val_pow_eq_pow_val] at h1
      exact h1
    · rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
        Matrix.smul_mulVec, Matrix.one_mulVec]
  · exact conj_mem_frameGroupOf he (yFrame_eq_smul_mulVec hK hq hT v)

end Frame

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292N

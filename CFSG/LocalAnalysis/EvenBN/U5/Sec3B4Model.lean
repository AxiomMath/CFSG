module

public import CFSG.LocalAnalysis.EvenBN.U5.ModelLevi
public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylow

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section Flag

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

@[expose] def IsFlagUni (e f : ι) (M : Matrix ι ι R) : Prop :=
  (∀ c b, c ≠ e → b ≠ f → M c b = (1 : Matrix ι ι R) c b) ∧ M f f = 1 ∧ M e e = 1

omit [Fintype ι] in
theorem IsFlagUni.map {e f : ι} {M : Matrix ι ι R} (hM : IsFlagUni e f M) {σ : R → R}
    (h0 : σ 0 = 0) (h1 : σ 1 = 1) : IsFlagUni e f (M.map σ) := by
  refine ⟨fun c b hc hb => ?_, ?_, ?_⟩
  · rw [Matrix.map_apply, hM.1 c b hc hb, ← Matrix.map_apply (f := σ),
      Matrix.map_one σ h0 h1]
  · rw [Matrix.map_apply, hM.2.1, h1]
  · rw [Matrix.map_apply, hM.2.2, h1]

theorem flag_inv_entries {e f : ι} {M N : Matrix ι ι R} (hMN : M * N = 1) (hNM : N * M = 1)
    (hMe : ∀ c, c ≠ e → M c e = 0) (hMf : ∀ k, k ≠ f → M f k = 0) :
    N e e * M e e = 1 ∧ (∀ c, c ≠ e → N c e = 0) ∧ M f f * N f f = 1 ∧
      ∀ b, b ≠ f → N f b = 0 := by
  have hNe : ∀ c, N c e * M e e = (1 : Matrix ι ι R) c e := fun c => by
    rw [← hNM, Matrix.mul_apply, Finset.sum_eq_single e (fun k _ hk => by rw [hMe k hk, mul_zero])
      (by simp)]
  have hMf' : ∀ b, M f f * N f b = (1 : Matrix ι ι R) f b := fun b => by
    rw [← hMN, Matrix.mul_apply, Finset.sum_eq_single f (fun k _ hk => by rw [hMf k hk, zero_mul])
      (by simp)]
  have h1 : N e e * M e e = 1 := by rw [hNe, one_apply_eq]
  have h2 : M f f * N f f = 1 := by rw [hMf', one_apply_eq]
  refine ⟨h1, fun c hc => ?_, h2, fun b hb => ?_⟩
  · have := hNe c
    rw [one_apply_ne hc] at this
    calc N c e = N c e * (M e e * N e e) := by rw [mul_comm (M e e), h1, mul_one]
      _ = 0 := by rw [← mul_assoc, this, zero_mul]
  · have := hMf' b
    rw [one_apply_ne (Ne.symm hb)] at this
    calc N f b = (N f f * M f f) * N f b := by rw [mul_comm (N f f), h2, one_mul]
      _ = 0 := by rw [mul_assoc, this, mul_zero]

theorem isFlagUni_mul_mul {e f : ι} (hef : e ≠ f) {M N a : Matrix ι ι R} (hMN : M * N = 1)
    (hNM : N * M = 1) (hMe : ∀ c, c ≠ e → M c e = 0) (hMf : ∀ k, k ≠ f → M f k = 0)
    (ha : IsFlagUni e f a) : IsFlagUni e f (M * a * N) := by
  obtain ⟨hN1, hNe, hN2, hNf⟩ := flag_inv_entries hMN hNM hMe hMf
  have haN : ∀ k b, k ≠ e → b ≠ f → (a * N) k b = N k b := by
    intro k b hk hb
    conv_rhs => rw [← Matrix.one_mul N]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = f
    · rw [hl, hNf b hb, mul_zero, mul_zero]
    · rw [ha.1 k l hk hl]
  refine ⟨fun c b hc hb => ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← hMN, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = e
    · rw [hk, hMe c hc, zero_mul, zero_mul]
    · rw [haN k b hk hb]
  · rw [Matrix.mul_assoc, Matrix.mul_apply,
      Finset.sum_eq_single f (fun k _ hk => by rw [hMf k hk, zero_mul]) (by simp)]
    have : (a * N) f f = N f f := by
      conv_rhs => rw [← Matrix.one_mul N]
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : l = f
      · rw [hl, ha.2.1, one_apply_eq]
      · rw [ha.1 f l (Ne.symm hef) hl]
    rw [this, hN2]
  · rw [Matrix.mul_apply, Finset.sum_eq_single e (fun l _ hl => by rw [hNe l hl, mul_zero])
      (by simp)]
    have : (M * a) e e = M e e := by
      conv_rhs => rw [← Matrix.mul_one M]
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k = e
      · rw [hk, ha.2.2, one_apply_eq]
      · rw [ha.1 k e hk hef]
    rw [this, mul_comm, hN1]

theorem isFlagUni_conj_diagonal {e f : ι} {M N : Matrix ι ι R} (hMN : M * N = 1)
    (hNM : N * M = 1) (hMe : ∀ c, c ≠ e → M c e = 0) (hMf : ∀ k, k ≠ f → M f k = 0)
    {d d' : ι → R} (hd : ∀ k, d k * d' k = 1) (hd1 : ∀ k, k ≠ e → k ≠ f → d k = 1) :
    IsFlagUni e f (M * diagonal d * N * diagonal d') := by
  obtain ⟨hN1, hNe, hN2, hNf⟩ := flag_inv_entries hMN hNM hMe hMf
  have hentry : ∀ c b, (M * diagonal d * N * diagonal d') c b =
      (∑ k, M c k * d k * N k b) * d' b := by
    intro c b
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal]
  refine ⟨fun c b hc hb => ?_, ?_, ?_⟩
  · rw [hentry]
    have hsum : ∑ k, M c k * d k * N k b = ∑ k, M c k * N k b := by
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hke : k = e
      · rw [hke, hMe c hc, zero_mul, zero_mul]
      · by_cases hkf : k = f
        · rw [hkf, hNf b hb, mul_zero, mul_zero]
        · rw [hd1 k hke hkf, mul_one]
    rw [hsum, ← Matrix.mul_apply, hMN]
    by_cases hcb : c = b
    · rw [hcb, one_apply_eq, one_mul]
      have := hd b
      rw [hd1 b (hcb ▸ hc) hb, one_mul] at this
      exact this
    · rw [one_apply_ne hcb, zero_mul]
  · rw [hentry, Finset.sum_eq_single f (fun k _ hk => by rw [hMf k hk, zero_mul, zero_mul])
      (by simp)]
    calc M f f * d f * N f f * d' f = (M f f * N f f) * (d f * d' f) := by ring
      _ = 1 := by rw [hN2, hd, one_mul]
  · rw [hentry, Finset.sum_eq_single e (fun k _ hk => by rw [hNe k hk, mul_zero]) (by simp)]
    calc M e e * d e * N e e * d' e = (N e e * M e e) * (d e * d' e) := by ring
      _ = 1 := by rw [hN1, hd, one_mul]

end Flag

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem ιe₁_ne_ιf₁ : (ιe₁ : HypIndex 2 1) ≠ ιf₁ := by decide

theorem mem_A₂sub_iff {g : hypSU h 2 1} : g ∈ A₂sub h ↔ IsFlagUni ιe₁ ιf₁ (mat g) := by
  constructor
  · intro hg
    obtain ⟨hgU, a1, a2, a3⟩ := mem_A₂sub.1 hg
    obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩⟩ := U_entries hgU
    refine ⟨fun c b hc hb => ?_, d4, d1⟩
    rcases c with i | k | j <;> rcases b with i' | k' | j' <;> (try fin_cases i) <;>
      (try fin_cases i') <;> (try fin_cases k) <;> (try fin_cases k') <;> (try fin_cases j) <;>
      (try fin_cases j') <;> simp_all [one_apply]
  · rintro ⟨h1, h2, h3⟩
    have hlow : ∀ a b : HypIndex 2 1, fullPos b < fullPos a → mat g a b = 0 := by
      intro a b hab
      have ha : a ≠ ιe₁ := by
        rintro rfl
        simp at hab
      have hb : b ≠ ιf₁ := by
        rintro rfl
        have := fullPos_lt a
        simp at hab
        omega
      rw [h1 a b ha hb, one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hab
    have hdiag : ∀ a : HypIndex 2 1, mat g a a = 1 := by
      intro a
      by_cases ha : a = ιe₁
      · rw [ha, h3]
      · by_cases hb : a = ιf₁
        · rw [hb, h2]
        · rw [h1 a a ha hb, one_apply_eq]
    refine mem_A₂sub.2 ⟨mem_hypUnitriangular.2 ⟨fun a b hab => hlow a b hab, hdiag⟩, ?_, ?_, ?_⟩
    · rw [h1 _ _ (by decide) (by decide), one_apply_ne (by decide)]
    · rw [h1 _ _ (by decide) (by decide), one_apply_ne (by decide)]
    · rw [h1 _ _ (by decide) (by decide), one_apply_ne (by decide)]

theorem mat_eq_of_mem_ZPsub {z : hypSU h 2 1} (hz : z ∈ ZPsub h) :
    mat z = 1 + Matrix.single ιe₁ ιf₁ (mat z ιe₁ ιf₁) := by
  obtain ⟨hzU, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := mem_ZPsub.1 hz
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩⟩ := U_entries hzU
  ext a b
  rcases a with i | k | j <;> rcases b with i' | k' | j' <;> (try fin_cases i) <;>
    (try fin_cases i') <;> (try fin_cases k) <;> (try fin_cases k') <;> (try fin_cases j) <;>
    (try fin_cases j') <;> simp_all [one_apply]

theorem map_one_add_single (σ : K ≃+* K) {c : K} (hc : σ c = c) :
    (1 + Matrix.single ιe₁ ιf₁ c : Matrix (HypIndex 2 1) (HypIndex 2 1) K).map σ =
      1 + Matrix.single ιe₁ ιf₁ c := by
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, one_apply, Matrix.single_apply]
  split_ifs <;> simp [hc]

theorem lmat_col_e₁ {x : Gam h} (hz : act h x (z₁SU h) ∈ ZPsub h) (a : HypIndex 2 1)
    (ha : a ≠ ιe₁) : lmat x a ιe₁ = 0 := by
  have hrel := lmat_mul_map x (z₁SU h)
  rw [mat_eq_of_mem_ZPsub hz, mat_eq_of_mem_ZPsub z₁SU_mem_ZPsub, mat_z₁SU_e₁f₁,
    map_one_add_single _ (map_one _)] at hrel
  have e := congrFun (congrFun hrel a) ιf₁
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply,
    mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ ha, mul_one, add_zero] at e
  linear_combination e

theorem lmat_e₁e₁_ne_zero {x : Gam h} (hcol : ∀ a, a ≠ ιe₁ → lmat x a ιe₁ = 0) :
    lmat x ιe₁ ιe₁ ≠ 0 := by
  have h1 : ((x.1.left⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *
      lmat x = 1 := by
    rw [lmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e := congrFun (congrFun h1 ιe₁) ιe₁
  rw [Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun k _ hk => by rw [hcol k hk, mul_zero])
    (by simp), one_apply_eq] at e
  exact right_ne_zero_of_mul_eq_one e

theorem lmat_row_f₁ {x : Gam h} (hcol : ∀ a, a ≠ ιe₁ → lmat x a ιe₁ = 0) (b : HypIndex 2 1)
    (hb : b ≠ ιf₁) : lmat x ιf₁ b = 0 := by
  obtain ⟨μ, -, -, hgram⟩ := x.2
  change ((lmat x).map h.bar)ᵀ * hypGram 2 1 K * lmat x = μ • hypGram 2 1 K at hgram
  have e := congrFun (congrFun hgram ιe₁) b
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single ιe₁ (fun k _ hk => by
      rw [Matrix.transpose_apply, Matrix.map_apply, hcol k hk, map_zero, zero_mul]) (by simp),
    hypGram_mul_apply, Matrix.smul_apply, hypGram_apply, Matrix.transpose_apply,
    Matrix.map_apply] at e
  simp only [hypPartner_inl, hb, ite_false, smul_zero] at e
  rcases mul_eq_zero.1 e with h0 | h0
  · exact absurd ((map_eq_zero h.bar).1 h0) (lmat_e₁e₁_ne_zero hcol)
  · exact h0

theorem mat_act (x : Gam h) (g : hypSU h 2 1) :
    mat (act h x g) = lmat x * (mat g).map x.1.right *
      ((x.1.left⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) := by
  change ((x.1.left * glAut x.1.right (g : GL (HypIndex 2 1) K) * x.1.left⁻¹ :
    GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = _
  rw [Units.val_mul, Units.val_mul, coe_glAut]
  rfl

theorem lmat_mul_inv (x : Gam h) :
    lmat x * ((x.1.left⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = 1 ∧
      ((x.1.left⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *
        lmat x = 1 :=
  ⟨by rw [lmat, ← Units.val_mul, mul_inv_cancel, Units.val_one],
    by rw [lmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]⟩

theorem act_mem_A₂sub {x : Gam h} (hcol : ∀ a, a ≠ ιe₁ → lmat x a ιe₁ = 0)
    (hrow : ∀ b, b ≠ ιf₁ → lmat x ιf₁ b = 0) {v : hypSU h 2 1} (hv : v ∈ A₂sub h) :
    act h x v ∈ A₂sub h := by
  rw [mem_A₂sub_iff] at hv ⊢
  rw [mat_act]
  exact isFlagUni_mul_mul ιe₁_ne_ιf₁ (lmat_mul_inv x).1 (lmat_mul_inv x).2 hcol hrow
    (hv.map (map_zero _) (map_one _))

theorem act_mul_inv_mem_A₂sub {x : Gam h} (hcol : ∀ a, a ≠ ιe₁ → lmat x a ιe₁ = 0)
    (hrow : ∀ b, b ≠ ιf₁ → lmat x ιf₁ b = 0) {j : hypSU h 2 1} (hj : j ∈ hypTorus h 2 1)
    (hj1 : mat j ιe₂ ιe₂ = 1 ∧ mat j ιz ιz = 1 ∧ mat j ιf₂ ιf₂ = 1)
    (hσ : (mat j).map x.1.right = mat j) : act h x j * j⁻¹ ∈ A₂sub h := by
  rw [mem_A₂sub_iff, mat_mul, mat_act, hσ, torus_mat hj, torus_mat (inv_mem hj)]
  refine isFlagUni_conj_diagonal (lmat_mul_inv x).1 (lmat_mul_inv x).2 hcol hrow
    (fun k => by rw [torus_inv_apply hj, mul_inv_cancel₀ (torus_ne_zero hj k)]) fun k hk1 hk2 => ?_
  rcases k with i | k | i <;> (try fin_cases i) <;> (try fin_cases k)
  · exact absurd rfl hk1
  · exact hj1.1
  · exact hj1.2.1
  · exact absurd rfl hk2
  · exact hj1.2.2

end Model

section Levi

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem patSub_sI₂_le_N₂sub : patSub h sI₂ isPattern_sI₂ ≤ N₂sub h := by
  intro g hg
  obtain ⟨hgU, z1, z2, z3, z4, z5, z6, z7⟩ := mem_patSub_sI₂.1 hg
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩⟩ := U_entries hgU
  refine mem_N₂sub.2 ⟨fun a => ?_, fun a => ?_⟩ <;>
    rcases a with i | k | j <;> (try fin_cases i) <;> (try fin_cases k) <;> (try fin_cases j) <;>
    simp_all [one_apply]

theorem patSub_sI₆_le_N₂sub : patSub h sI₆ isPattern_sI₆ ≤ N₂sub h := by
  intro g hg
  obtain ⟨hgU, z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := mem_patSub_sI₆.1 hg
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩⟩ := U_entries hgU
  refine mem_N₂sub.2 ⟨fun a => ?_, fun a => ?_⟩ <;>
    rcases a with i | k | j <;> (try fin_cases i) <;> (try fin_cases k) <;> (try fin_cases j) <;>
    simp_all [one_apply]

theorem N₂sub_comm_ZPsub {n z : hypSU h 2 1} (hn : n ∈ N₂sub h) (hz : z ∈ ZPsub h) :
    n * z = z * n := by
  obtain ⟨hc1, hc2⟩ := mem_N₂sub.1 hn
  apply mat_injective
  rw [mat_mul, mat_mul, mat_eq_of_mem_ZPsub hz, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul]
  congr 1
  ext a b
  by_cases ha : a = ιe₁ <;> by_cases hb : b = ιf₁
  · subst ha
    subst hb
    rw [mul_single_apply_same, single_mul_apply_same, hc1, (N₂sub_rows hn _).2, one_apply_eq,
      one_apply_eq, mul_one, one_mul]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hb, ha, single_mul_apply_same, (N₂sub_rows hn _).2,
      one_apply_ne (Ne.symm hb), mul_zero]
  · rw [hb, mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ ha, hc1, one_apply_ne ha,
      zero_mul]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hb, single_mul_apply_of_ne _ _ _ _ _ ha]

theorem mem_A₂sub_of_conj_s {g : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1)
    (hs : sSU h * g * (sSU h)⁻¹ ∈ hypUnitriangular h 2 1) : g ∈ A₂sub h := by
  have e1 := U_lower hs (a := ιz) (b := ιe₂) (by decide)
  have e2 := U_lower hs (a := ιf₂) (b := ιe₂) (by decide)
  have e3 := U_lower hs (a := ιf₂) (b := ιz) (by decide)
  rw [conj_sSU_apply] at e1 e2 e3
  exact mem_A₂sub.2 ⟨hg, e3, e1, e2⟩

theorem exists_jSU (h : UnitaryFieldData 2 f K) {a : K} (ha : a ≠ 0) (hab : h.bar a = a) :
    ∃ j ∈ hypTorus h 2 1, mat j ιe₁ ιe₁ = a ∧ mat j ιe₂ ιe₂ = 1 ∧ mat j ιz ιz = 1 ∧
      mat j ιf₁ ιf₁ = a⁻¹ ∧ mat j ιf₂ ιf₂ = 1 := by
  obtain ⟨j, hj, e1, e2, e3, e4, e5⟩ := exists_torus h ha one_ne_zero
  refine ⟨j, hj, e1, e2, ?_, ?_, ?_⟩
  · rw [e3, hab, map_one, mul_one, div_self ha]
  · rw [e4, hab]
  · rw [e5, map_one, inv_one]

theorem jSU_conj_ZPsub {j z : hypSU h 2 1} (hj : j ∈ hypTorus h 2 1) {a : K}
    (hj1 : mat j ιe₁ ιe₁ = a) (hj4 : mat j ιf₁ ιf₁ = a⁻¹) (hz : z ∈ ZPsub h) :
    j * z * j⁻¹ ∈ ZPsub h ∧ mat (j * z * j⁻¹) ιe₁ ιf₁ = a * a * mat z ιe₁ ιf₁ := by
  refine ⟨torus_conj_mem_patSub isPattern_sZP hj hz, ?_⟩
  rw [torus_conj_apply hj, hj1, hj4, inv_inv]
  ring

end Levi

section Aut

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem map_one_add_single' (σ : K ≃+* K) (c : K) :
    (1 + Matrix.single ιe₁ ιf₁ c : Matrix (HypIndex 2 1) (HypIndex 2 1) K).map σ =
      1 + Matrix.single ιe₁ ιf₁ (σ c) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem act_ZPsub_entry {x : Gam h} {z : hypSU h 2 1} (hz : z ∈ ZPsub h)
    (hxz : act h x z ∈ ZPsub h) :
    lmat x ιe₁ ιe₁ * x.1.right (mat z ιe₁ ιf₁) =
      mat (act h x z) ιe₁ ιf₁ * lmat x ιf₁ ιf₁ := by
  have hrel := lmat_mul_map x z
  rw [mat_eq_of_mem_ZPsub hz, map_one_add_single', mat_eq_of_mem_ZPsub hxz] at hrel
  have e := congrFun (congrFun hrel ιe₁) ιf₁
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply,
    mul_single_apply_same, single_mul_apply_same] at e
  linear_combination e

theorem right_apply_eq_of_centralizes {x : Gam h} (hZ : ∀ z ∈ ZPsub h, act h x z = z) {c : K}
    (hc : h.bar c = c) : x.1.right c = c := by
  have hcol := lmat_col_e₁ (by rw [hZ _ z₁SU_mem_ZPsub]; exact z₁SU_mem_ZPsub) (x := x)
  have h1 := act_ZPsub_entry z₁SU_mem_ZPsub (by rw [hZ _ z₁SU_mem_ZPsub]; exact z₁SU_mem_ZPsub)
    (x := x)
  rw [hZ _ z₁SU_mem_ZPsub, mat_z₁SU_e₁f₁, map_one, mul_one, one_mul] at h1
  obtain ⟨g, hg, hgc⟩ := exists_rootZP h hc
  have h2 := act_ZPsub_entry hg (by rw [hZ g hg]; exact hg) (x := x)
  rw [hZ g hg, hgc, ← h1] at h2
  exact mul_left_cancel₀ (lmat_e₁e₁_ne_zero hcol) (h2.trans (mul_comm _ _))

theorem exists_scalar_act_ZPsub {x : Gam h} (hσ : x.1.right = 1)
    (hZ : ∀ z ∈ ZPsub h, act h x z ∈ ZPsub h) :
    ∃ l : K, l ≠ 0 ∧ h.bar l = l ∧
      ∀ z ∈ ZPsub h, mat (act h x z) ιe₁ ιf₁ = l * mat z ιe₁ ιf₁ := by
  have := h.charP
  have hcol := lmat_col_e₁ (hZ _ z₁SU_mem_ZPsub) (x := x)
  have hrow := lmat_row_f₁ hcol
  obtain ⟨-, -, hff, -⟩ := flag_inv_entries (lmat_mul_inv x).1 (lmat_mul_inv x).2 hcol hrow
  have hf0 : lmat x ιf₁ ιf₁ ≠ 0 := left_ne_zero_of_mul_eq_one hff
  have he0 := lmat_e₁e₁_ne_zero hcol
  have key : ∀ z ∈ ZPsub h,
      mat (act h x z) ιe₁ ιf₁ = lmat x ιe₁ ιe₁ / lmat x ιf₁ ιf₁ * mat z ιe₁ ιf₁ := by
    intro z hz
    have e := act_ZPsub_entry hz (hZ z hz)
    rw [hσ] at e
    change lmat x ιe₁ ιe₁ * mat z ιe₁ ιf₁ = _ at e
    field_simp
    linear_combination e.symm
  refine ⟨lmat x ιe₁ ιe₁ / lmat x ιf₁ ιf₁, div_ne_zero he0 hf0, ?_, key⟩
  have h1 := key _ z₁SU_mem_ZPsub
  rw [mat_z₁SU_e₁f₁, mul_one] at h1
  rw [← h1]
  obtain ⟨hU, z1, -, z3, -, -, -, z7, -, -⟩ := mem_ZPsub.1 (hZ _ z₁SU_mem_ZPsub)
  have r := (U_rel hU).2.2.2.2.2
  rw [z1, z3, z7] at r
  simp only [map_zero, mul_zero, add_zero] at r
  exact bar_eq_of_add_eq_zero h r

theorem A₂sub_mul_apply {v : hypSU h 2 1} (hv : v ∈ A₂sub h)
    (M : Matrix (HypIndex 2 1) (HypIndex 2 1) K) {i : HypIndex 2 1} (hi1 : i ≠ ιe₁)
    (hi2 : i ≠ ιf₁) (b : HypIndex 2 1) :
    (mat v * M) i b = M i b + mat v i ιf₁ * M ιf₁ b := by
  have hV := (mem_A₂sub_iff.1 hv).1
  rw [Matrix.mul_apply, Fintype.sum_eq_add_sum_compl ιf₁, add_comm]
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [hV i i hi1 hi2, one_apply_eq, one_mul]
  · intro l hl hli
    rw [hV i l hi1 (by simpa using hl), one_apply_ne (Ne.symm hli), zero_mul]
  · intro hi
    exact absurd (by simpa using hi2) hi

theorem right_eq_one_of_act_N₂ {x : Gam h} (hcol : ∀ a, a ≠ ιe₁ → lmat x a ιe₁ = 0)
    (hrow : ∀ b, b ≠ ιf₁ → lmat x ιf₁ b = 0)
    (hN : ∀ n ∈ N₂sub h, n ∈ hypUnitriangular h 2 1 → ∃ v ∈ A₂sub h, act h x n = v * n) :
    x.1.right = 1 := by
  have := h.charP
  set A := lmat x with hAdef
  set σ := x.1.right with hσdef
  have key : ∀ n ∈ N₂sub h, n ∈ hypUnitriangular h 2 1 → ∀ i j : HypIndex 2 1,
      i ≠ ιe₁ → i ≠ ιf₁ → j ≠ ιf₁ → (A * (mat n).map σ) i j = (mat n * A) i j := by
    intro n hn hnU i j hi1 hi2 hj
    obtain ⟨v, hv, hvn⟩ := hN n hn hnU
    have hrel := lmat_mul_map x n
    rw [hvn, mat_mul, Matrix.mul_assoc] at hrel
    rw [hrel, A₂sub_mul_apply hv _ hi1 hi2]
    have : (mat n * A) ιf₁ j = 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single ιf₁ (fun k _ hk => by
        rw [(N₂sub_rows hn k).2, one_apply_ne (Ne.symm hk), zero_mul]) (by simp),
        (N₂sub_rows hn _).2, one_apply_eq, one_mul, hrow j hj]
    rw [this, mul_zero, add_zero]
  obtain ⟨n₁, hn₁, hn₁e⟩ := exists_rootI₆ h (map_one h.bar)
  have hn₁N := patSub_sI₆_le_N₂sub hn₁
  obtain ⟨hn₁U, -, a2, a3, a4, a5, a6, a7, a8, -⟩ := mem_patSub_sI₆.1 hn₁
  obtain ⟨⟨-, d2, d3, -, d5⟩, ⟨l1, l2, l3, -, l5, l6, -, l8, l9, l10⟩⟩ := U_entries hn₁U
  have k1 := key n₁ hn₁N hn₁U ιe₂ ιz (by decide) (by decide) (by decide)
  have k2 := key n₁ hn₁N hn₁U ιz ιf₂ (by decide) (by decide) (by decide)
  have k3 := key n₁ hn₁N hn₁U ιf₂ ιf₂ (by decide) (by decide) (by decide)
  simp only [Matrix.mul_apply, sum_hypIndex_two, Matrix.map_apply, a2, a3, a4, a5, a6, a7,
    a8, d2, d3, d5, l1, l2, l3, l5, l6, l8, l9, l10, hn₁e, map_zero,
    map_one, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add] at k1 k2 k3
  have hfz : A ιf₂ ιz = 0 := by linear_combination k1.symm
  have hze : A ιz ιe₂ = 0 := by linear_combination k2
  have hfe : A ιf₂ ιe₂ = 0 := by linear_combination k3
  have hu : ∀ u : K, A ιe₂ ιe₂ * σ u = u * A ιz ιz := by
    intro u
    obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := u * h.bar u)
      (by rw [map_mul, h.bar_bar, mul_comm])
    obtain ⟨n, hn, hnu, hnc⟩ := exists_rootI₂ h hc
    have hnN := patSub_sI₂_le_N₂sub hn
    obtain ⟨hnU, -, -, b3, -, -, b6, -⟩ := mem_patSub_sI₂.1 hn
    obtain ⟨⟨-, e2, e3, -, -⟩, ⟨m1, -, -, -, -, -, -, m8, m9, -⟩⟩ := U_entries hnU
    have k := key n hnN hnU ιe₂ ιz (by decide) (by decide) (by decide)
    simp only [Matrix.mul_apply, sum_hypIndex_two, Matrix.map_apply, b3, b6,
      e2, e3, m1, m8, m9, hnu, hnc, hfz, map_zero,
      map_one, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add] at k
    linear_combination k
  have hez : A ιe₂ ιe₂ = A ιz ιz := by simpa using hu 1
  have he2 : A ιe₂ ιe₂ ≠ 0 := by
    obtain ⟨-, hNe, -, -⟩ := flag_inv_entries (lmat_mul_inv x).1 (lmat_mul_inv x).2 hcol hrow
    have e := congrFun (congrFun (lmat_mul_inv x).2 ιe₂) ιe₂
    rw [Matrix.mul_apply, sum_hypIndex_two, hNe ιe₂ (by decide), ← hAdef, hze, hfe,
      hrow ιe₂ (by decide), one_apply_eq] at e
    simp only [zero_mul, mul_zero, zero_add, add_zero] at e
    exact right_ne_zero_of_mul_eq_one e
  apply RingEquiv.ext
  intro u
  have := hu u
  rw [← hez] at this
  exact mul_left_cancel₀ he2 (this.trans (mul_comm _ _))

end Aut

end CFSG.LocalAnalysis.EvenBN.U5

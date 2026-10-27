module

public import CFSG.LieType.SpinGeom.Simple
public import CFSG.LieType.SpinGeom.FrameVec

public section

namespace CFSG.LieType.SpinGeom

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData QuadraticMap
open scoped Matrix

section Unipotent

variable {K : Type} [Field K]

theorem matrix_eq_of_mulVec_eq {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using h v)

theorem gl_eq_of_mulVec_eq {n : ℕ} {a b : GL (Fin n) K}
    (h : ∀ v, (a : Matrix (Fin n) (Fin n) K) *ᵥ v = (b : Matrix (Fin n) (Fin n) K) *ᵥ v) :
    a = b :=
  Units.ext (matrix_eq_of_mulVec_eq h)

theorem matrix_eq_one_of_single {g : Matrix (Fin 3) (Fin 3) K}
    (h : ∀ j : Fin 3, g *ᵥ (Pi.single j 1 : Fin 3 → K) = Pi.single j 1) : g = 1 := by
  ext i j
  have h1 := congrFun (h j) i
  rw [Matrix.mulVec_single_one] at h1
  have h2 : g i j = (Pi.single j (1 : K) : Fin 3 → K) i := h1
  rw [h2, Matrix.one_apply, Pi.single_apply]

theorem eq_zero_of_altMat_single {m : Fin 3 → K}
    (h : ∀ j : Fin 3, altMat K m *ᵥ (Pi.single j 1 : Fin 3 → K) = 0) : m = 0 := by
  funext i
  fin_cases i
  · have := congrFun (h 2) 1
    simpa [altMat, Matrix.mulVec_single_one] using this
  · have := congrFun (h 2) 0
    simpa [altMat, Matrix.mulVec_single_one] using this
  · have := congrFun (h 1) 0
    simpa [altMat, Matrix.mulVec_single_one] using this

theorem eq_alpha_of_line {c m : Fin 3 → K} {g : Matrix (Fin 3) (Fin 3) K}
    (h7 : ∀ x : Fin (2 * 4) → K, coordY K x 0 = 0 → ∃ t : K,
      spinElt K c m g x - x = t • frameE K 0) : g = 1 ∧ m = 0 := by
  have key : ∀ j : Fin 3, g *ᵥ (Pi.single j 1 : Fin 3 → K) = Pi.single j 1 ∧
      altMat K m *ᵥ (g *ᵥ (Pi.single j 1 : Fin 3 → K)) = 0 := by
    intro j
    obtain ⟨t, ht⟩ := h7 (frameVec K 0 (Pi.single j 1) 0 0) (coordY_frameVec_zero _ _ _ _)
    rw [spinElt_frameVec, sub_eq_iff_eq_add, frameE_zero_eq, frameVec_smul, frameVec_add] at ht
    obtain ⟨-, hx, hy, -⟩ := frameVec_inj ht
    refine ⟨by simpa using hx, by simpa using hy⟩
  have hg : g = 1 := matrix_eq_one_of_single fun j => (key j).1
  refine ⟨hg, eq_zero_of_altMat_single fun j => ?_⟩
  have := (key j).2
  rwa [hg, Matrix.one_mulVec] at this

end Unipotent


section FourCase

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem eq_one_of_four {c m : Fin 3 → K} {g : Matrix (Fin 3) (Fin 3) K} (hg : g.det = 1)
    (h8 : ∀ y : Fin 3 → K, ∃ t : K,
      spinElt K c m g (frameVec K 0 0 y 0) - frameVec K 0 0 y 0 = t • frameE K 0) : g = 1 := by
  have key : ∀ j : Fin 3, (g.adjugate)ᵀ *ᵥ (Pi.single j 1 : Fin 3 → K) = Pi.single j 1 := by
    intro j
    obtain ⟨t, ht⟩ := h8 (Pi.single j 1)
    rw [spinElt_frameVec, sub_eq_iff_eq_add, frameE_zero_eq, frameVec_smul, frameVec_add] at ht
    obtain ⟨-, -, hy, -⟩ := frameVec_inj ht
    simpa using hy
  have hG : (g.adjugate)ᵀ = 1 := matrix_eq_one_of_single key
  have hadj : g.adjugate = 1 := by
    have := congrArg Matrix.transpose hG
    simpa using this
  have h2 := Matrix.adjugate_adjugate g (by simp)
  rw [hadj, Matrix.adjugate_one, hg] at h2
  simpa using h2.symm

theorem transvection_mul_self (i j : Fin 3) (hij : i ≠ j) (r : K) :
    Matrix.transvection i j r * Matrix.transvection i j r = 1 := by
  rw [Matrix.transvection_mul_transvection_same i j hij, CharTwo.add_self_eq_zero,
    Matrix.transvection_zero]

theorem conj_transvection (i j : Fin 3) (hij : i ≠ j) (r : K) (c m : Fin 3 → K)
    (v : Fin (2 * 4) → K) :
    spinElt K 0 0 (Matrix.transvection i j r) (spinElt K c m 1
        (spinElt K 0 0 (Matrix.transvection i j r) v)) =
      spinElt K ((Matrix.transvection i j r).adjugateᵀ *ᵥ c) (Matrix.transvection i j r *ᵥ m) 1
        v := by
  have h1 : spinElt K c m 1 (spinElt K 0 0 (Matrix.transvection i j r) v) =
      spinElt K c m (Matrix.transvection i j r) v := by
    rw [spinElt_comp c m 1 Matrix.det_one 0 0 (Matrix.transvection i j r) v]
    simp [altMat_zero]
  rw [h1, spinElt_comp 0 0 _ (Matrix.det_transvection_of_ne i j hij r) c m _ v,
    transvection_mul_self i j hij r]
  simp

end FourCase


section FourMain

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem mulVec_mul_u {a b : GL (Fin (2 * 4)) K} {c m c' m' : Fin 3 → K}
    (ha : ∀ v, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c m 1 v)
    (hb : ∀ v, (b : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c' m' 1 v) (v) :
    ((a * b : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
      spinElt K (c + c' + altMat K m' *ᵥ m) (m + m') 1 v := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb, ha, spinElt_one_comp]

omit [Finite K] in
theorem conj_act (i j : Fin 3) (hij : i ≠ j) (r : K) {M a : GL (Fin (2 * 4)) K} {c m : Fin 3 → K}
    (hM : ∀ v, (M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
      spinElt K 0 0 (Matrix.transvection i j r) v)
    (ha : ∀ v, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c m 1 v) (v) :
    ((M * a * M⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
      spinElt K ((Matrix.transvection i j r).adjugateᵀ *ᵥ c)
        (Matrix.transvection i j r *ᵥ m) 1 v := by
  have hMM : ∀ w, (M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
      ((M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w) = w := by
    intro w
    rw [hM, hM, spinElt_zero_zero_comp _ _ (Matrix.det_transvection_of_ne i j hij r) w,
      transvection_mul_self i j hij r, spinElt_one]
  have hinv : ((M⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
      (M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v := by
    calc ((M⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v
        = ((M⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
            ((M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
              ((M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v)) := by rw [hMM]
      _ = (M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v := by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, hM, ha,
    hM]
  exact conj_transvection i j hij r c m v

private def Mpar (A : Subgroup (GL (Fin (2 * 4)) K)) : AddSubgroup (Fin 3 → K) where
  carrier := {m | ∃ a ∈ A, ∃ c : Fin 3 → K,
    ∀ v, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c m 1 v}
  zero_mem' := ⟨1, A.one_mem, 0, fun v => by simp [spinElt_one]⟩
  add_mem' := by
    rintro m m' ⟨a, ha, c, hc⟩ ⟨b, hb, c', hc'⟩
    exact ⟨a * b, A.mul_mem ha hb, c + c' + altMat K m' *ᵥ m, mulVec_mul_u hc hc'⟩
  neg_mem' := by
    rintro m ⟨a, ha, c, hc⟩
    have : -m = m := by
      ext i
      exact CharTwo.neg_eq (m i)
    rw [this]
    exact ⟨a, ha, c, hc⟩

private def Cpar (A : Subgroup (GL (Fin (2 * 4)) K)) : AddSubgroup (Fin 3 → K) where
  carrier := {c | ∃ a ∈ A, ∀ v,
    (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c 0 1 v}
  zero_mem' := ⟨1, A.one_mem, fun v => by simp [spinElt_one]⟩
  add_mem' := by
    rintro c c' ⟨a, ha, hc⟩ ⟨b, hb, hc'⟩
    refine ⟨a * b, A.mul_mem ha hb, fun v => ?_⟩
    have := mulVec_mul_u hc hc' v
    simpa [altMat_zero] using this
  neg_mem' := by
    rintro c ⟨a, ha, hc⟩
    have : -c = c := by
      ext i
      exact CharTwo.neg_eq (c i)
    rw [this]
    exact ⟨a, ha, hc⟩

omit [Finite K] in
private theorem Mpar_transvection {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hconj : ∀ i j : Fin 3, i ≠ j → ∀ r : K, ∃ M : GL (Fin (2 * 4)) K,
      (∀ v, (M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
        spinElt K 0 0 (Matrix.transvection i j r) v) ∧ ∀ a ∈ A, M * a * M⁻¹ ∈ A) :
    ∀ i j : Fin 3, i ≠ j → ∀ (r : K) (m : Fin 3 → K), m ∈ Mpar A →
      (Matrix.transvection i j r *ᵥ m) ∈ Mpar A := by
  rintro i j hij r m ⟨a, ha, c, hc⟩
  obtain ⟨M, hM, hMA⟩ := hconj i j hij r
  exact ⟨M * a * M⁻¹, hMA a ha, _, conj_act i j hij r hM hc⟩

omit [Finite K] in
private theorem Cpar_transvection {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hconj : ∀ i j : Fin 3, i ≠ j → ∀ r : K, ∃ M : GL (Fin (2 * 4)) K,
      (∀ v, (M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
        spinElt K 0 0 (Matrix.transvection i j r) v) ∧ ∀ a ∈ A, M * a * M⁻¹ ∈ A) :
    ∀ i j : Fin 3, i ≠ j → ∀ (r : K) (c : Fin 3 → K), c ∈ Cpar A →
      (Matrix.transvection i j r *ᵥ c) ∈ Cpar A := by
  rintro i j hij r c ⟨a, ha, hc⟩
  obtain ⟨M, hM, hMA⟩ := hconj j i hij.symm r
  refine ⟨M * a * M⁻¹, hMA a ha, fun v => ?_⟩
  have := conj_act j i hij.symm r hM hc v
  rw [adjugate_transvection j i hij.symm, transvection_transpose, Matrix.mulVec_zero] at this
  exact this

omit [Finite K] in
theorem altMat_mulVec_self (m : Fin 3 → K) : altMat K m *ᵥ m = 0 := by
  rw [altMat_mulVec_eq_crossS]
  ext i
  fin_cases i <;> simp [crossS] <;> ring

theorem case_four_false {s : ℕ} {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hα : ∀ a ∈ A, ∃ c m : Fin 3 → K,
      ∀ v, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c m 1 v)
    (hconj : ∀ i j : Fin 3, i ≠ j → ∀ r : K, ∃ M : GL (Fin (2 * 4)) K,
      (∀ v, (M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
        spinElt K 0 0 (Matrix.transvection i j r) v) ∧ ∀ a ∈ A, M * a * M⁻¹ ∈ A)
    (h9 : ∀ y : Fin 3 → K, (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
      frameVec K 0 0 y 0 = frameVec K 0 0 y 0) → y = 0)
    (hcount : Nat.card A * Nat.card K ^ 4 = Nat.card K ^ (2 * 4 - 1 + 2 * s)) : False := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hMtop : Mpar A = ⊤ := by
    rcases addSubgroup_eq_bot_or_top_of_transvection (Mpar A) (Mpar_transvection hconj) with h | h
    · exfalso
      have hy := h9 (Pi.single 0 1) fun a ha => by
        obtain ⟨c, m, hv⟩ := hα a ha
        have hm : m = 0 := by
          have hmem : m ∈ Mpar A := ⟨a, ha, c, hv⟩
          rw [h] at hmem
          exact (AddSubgroup.mem_bot).1 hmem
        rw [hv, hm, spinElt_frameVec]
        simp only [Matrix.adjugate_one, Matrix.transpose_one, Matrix.one_mulVec, Matrix.mulVec_zero,
          dotProduct_zero, zero_dotProduct, zero_mul, smul_zero, zero_smul, add_zero, altMat_zero]
      have := congrFun hy 0
      simp at this
    · exact h
  have hmem_top : ∀ m : Fin 3 → K, ∃ a ∈ A, ∃ c : Fin 3 → K,
      ∀ v, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c m 1 v := by
    intro m
    have : m ∈ Mpar A := by
      rw [hMtop]
      trivial
    exact this
  rcases addSubgroup_eq_bot_or_top_of_transvection (Cpar A) (Cpar_transvection hconj) with hC | hC
  ·
    have huniq : ∀ (a b : GL (Fin (2 * 4)) K), a ∈ A → b ∈ A → ∀ c c' m : Fin 3 → K,
        (∀ v, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c m 1 v) →
        (∀ v, (b : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c' m 1 v) → c = c' := by
      intro a b ha hb c c' m hac hbc
      have hab := mulVec_mul_u hac hbc
      have h0 : m + m = 0 := by
        ext i
        exact CharTwo.add_self_eq_zero (m i)
      have hab' : ∀ v, ((a * b : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
          spinElt K (c + c') 0 1 v := by
        intro v
        rw [hab v, h0, altMat_mulVec_self, add_zero]
      have hmem : c + c' ∈ Cpar A := ⟨a * b, A.mul_mem ha hb, hab'⟩
      rw [hC] at hmem
      have hz : c + c' = 0 := (AddSubgroup.mem_bot).1 hmem
      have hneg : -c' = c' := by
        ext i
        exact CharTwo.neg_eq (c' i)
      rw [← hneg]
      exact eq_neg_of_add_eq_zero_left hz
    obtain ⟨a₀, ha₀, c₀, h₀⟩ := hmem_top (Pi.single 0 1)
    obtain ⟨a₁, ha₁, c₁, h₁⟩ := hmem_top (Pi.single 1 1)
    obtain ⟨M, hM, hMA⟩ := hconj 0 1 (by decide) 1
    have e1 : Matrix.transvection (0 : Fin 3) 1 (1 : K) *ᵥ (Pi.single 1 1 : Fin 3 → K) =
        Pi.single 0 1 + Pi.single 1 1 := by
      ext l
      rw [transvection_mulVec_apply]
      fin_cases l <;> simp
    have hp := mulVec_mul_u h₀ h₁
    have hq := conj_act 0 1 (by decide) 1 hM h₁
    rw [e1] at hq
    have hc1 := huniq (a₀ * a₁) (M * a₁ * M⁻¹) (A.mul_mem ha₀ ha₁) (hMA a₁ ha₁) _ _ _ hp hq
    have hc1' := congrFun hc1 2
    rw [adjugate_transvection 0 1 (by decide), transvection_transpose,
      transvection_mulVec_apply] at hc1'
    simp [altMat] at hc1'
    obtain ⟨M', hM', hMA'⟩ := hconj 2 1 (by decide) 1
    have e2 : Matrix.transvection (2 : Fin 3) 1 (1 : K) *ᵥ (Pi.single 0 1 : Fin 3 → K) =
        Pi.single 0 1 := by
      ext l
      rw [transvection_mulVec_apply]
      fin_cases l <;> simp
    have hq' := conj_act 2 1 (by decide) 1 hM' h₀
    rw [e2] at hq'
    have hc2 := huniq a₀ (M' * a₀ * M'⁻¹) ha₀ (hMA' a₀ ha₀) _ _ _ h₀ hq'
    have hc2' := congrFun hc2 1
    rw [adjugate_transvection 2 1 (by decide), transvection_transpose] at hc2'
    simp [transvection_mulVec_apply] at hc2'
    exact one_ne_zero (by linear_combination hc1' - hc2')
  ·
    have hCmem : ∀ c : Fin 3 → K, ∃ b ∈ A, ∀ v,
        (b : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c 0 1 v := by
      intro c
      have : c ∈ Cpar A := by
        rw [hC]
        trivial
      exact this
    choose a ha ca hca using hmem_top
    choose b hb hbc using hCmem
    let φ : (Fin 3 → K) × (Fin 3 → K) → A := fun p => ⟨a p.2 * b p.1, A.mul_mem (ha p.2) (hb p.1)⟩
    have hφ : Function.Injective φ := by
      intro p p' h
      have hv : ∀ v, spinElt K (ca p.2 + p.1 + altMat K 0 *ᵥ p.2) (p.2 + 0) 1 v =
          spinElt K (ca p'.2 + p'.1 + altMat K 0 *ᵥ p'.2) (p'.2 + 0) 1 v := by
        intro v
        have hh : ((a p.2 * b p.1 : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
            v = ((a p'.2 * b p'.1 : GL (Fin (2 * 4)) K) :
              Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v :=
          congrArg (fun x : A => ((x : GL (Fin (2 * 4)) K) :
            Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) h
        rw [← mulVec_mul_u (hca p.2) (hbc p.1) v, ← mulVec_mul_u (hca p'.2) (hbc p'.1) v]
        exact hh
      obtain ⟨hc, hm, -⟩ := spinElt_injective hv
      have hm' : p.2 = p'.2 := by simpa using hm
      refine Prod.ext ?_ hm'
      rw [← hm'] at hc
      simpa [altMat_zero] using hc
    choose cc mm hcc using fun x : A => hα x x.2
    have hψ : Function.Injective fun x : A => (cc x, mm x) := by
      intro x y h
      have hc : cc x = cc y := congrArg Prod.fst h
      have hm : mm x = mm y := congrArg Prod.snd h
      refine Subtype.ext (gl_eq_of_mulVec_eq fun v => ?_)
      rw [hcc x v, hcc y v, hc, hm]
    have hle1 := Nat.card_le_card_of_injective φ hφ
    have hle2 := Nat.card_le_card_of_injective _ hψ
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin] at hle1 hle2
    have hA : Nat.card A = Nat.card K ^ 3 * Nat.card K ^ 3 := le_antisymm hle2 hle1
    rw [hA, ← pow_add, ← pow_add] at hcount
    have h10 := Nat.pow_right_injective hq2 hcount
    omega

omit [CharP K 2] in
theorem card_le_of_alpha {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hα : ∀ a ∈ A, ∃ c : Fin 3 → K,
      ∀ v, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c 0 1 v) :
    Nat.card A ≤ Nat.card K ^ 3 := by
  choose c hc using fun x : A => hα x x.2
  have hinj : Function.Injective c := by
    intro x y h
    refine Subtype.ext (gl_eq_of_mulVec_eq fun v => ?_)
    rw [hc x v, hc y v, h]
  have := Nat.card_le_card_of_injective c hinj
  rwa [Nat.card_fun, Nat.card_fin] at this

end FourMain

end CFSG.LieType.SpinGeom

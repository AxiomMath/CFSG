module

public import CFSG.HardMathSupport.Dickson.Bal207.UniNormalAut
public import CFSG.HardMathSupport.Dickson.Bal207.FCBlock
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUBlock
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
open CFSG.ComponentClassification.Burgoyne.PSL (blockOn blockOn_one blockOn_mul det_blockOn
  blockOn_apply_mem blockOn_apply_not_mem)
open CFSG.ComponentClassification.Burgoyne.U (blockGL coe_blockGL blockOn_map blockOn_transpose)

theorem uni_conj_inl_inr_left {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    (d : N) (σ : G) (m : N) :
    ((SemidirectProduct.inl d * SemidirectProduct.inr σ : N ⋊[φ] G) * SemidirectProduct.inl m *
      (SemidirectProduct.inl d * SemidirectProduct.inr σ)⁻¹).left = d * φ σ m * d⁻¹ := by
  rw [uni_conj_inl_left]
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
    map_one, MulAut.one_apply, mul_one, one_mul]

section Matrix

variable {n : ℕ} {F : Type} [Field F] (I : Finset (Fin n))

theorem uni_blockOn_injective : Function.Injective (blockOn F I) := by
  intro X Y hXY
  ext a b
  have h1 := congrFun (congrFun hXY (I.equivFin.symm a)) (I.equivFin.symm b)
  rw [blockOn_apply_mem I _ (I.equivFin.symm a).2 (I.equivFin.symm b).2,
    blockOn_apply_mem I _ (I.equivFin.symm a).2 (I.equivFin.symm b).2] at h1
  simpa using h1

theorem uni_diagonal_commute_blockOn {r : Fin n → F} (hr : ∀ j ∈ I, ∀ k ∈ I, r j = r k)
    (N : Matrix (Fin I.card) (Fin I.card) F) :
    diagonal r * blockOn F I N = blockOn F I N * diagonal r := by
  ext j k
  rw [diagonal_mul, mul_diagonal]
  by_cases hj : j ∈ I <;> by_cases hk : k ∈ I
  · rw [hr j hj k hk, mul_comm]
  · rw [blockOn_apply_not_mem I N (Or.inr hk)]
    have hjk : j ≠ k := fun h' => hk (h' ▸ hj)
    rw [if_neg hjk, mul_zero, zero_mul]
  · rw [blockOn_apply_not_mem I N (Or.inl hj)]
    have hjk : j ≠ k := fun h' => hj (h' ▸ hk)
    rw [if_neg hjk, mul_zero, zero_mul]
  · rw [blockOn_apply_not_mem I N (Or.inl hj)]
    by_cases hjk : j = k
    · rw [if_pos hjk, hjk, mul_one, one_mul]
    · rw [if_neg hjk, mul_zero, zero_mul]

theorem uni_blockOn_diagonal_mul (d : Fin n → F) :
    blockOn F I (diagonal fun a => d (I.equivFin.symm a)) *
      diagonal (fun j => if j ∈ I then 1 else d j) = diagonal d := by
  ext j k
  rw [mul_diagonal]
  by_cases hk : k ∈ I
  · rw [if_pos hk, mul_one]
    by_cases hj : j ∈ I
    · rw [blockOn_apply_mem I _ hj hk, diagonal_apply, diagonal_apply]
      by_cases hjk : j = k
      · subst hjk
        simp
      · have hne : I.equivFin ⟨j, hj⟩ ≠ I.equivFin ⟨k, hk⟩ := fun h' =>
          hjk (by simpa using I.equivFin.injective h')
        rw [if_neg hne, if_neg hjk]
    · rw [blockOn_apply_not_mem I _ (Or.inl hj), diagonal_apply]
      have hjk : j ≠ k := fun h' => hj (h' ▸ hk)
      rw [if_neg hjk, if_neg hjk]
  · rw [if_neg hk, blockOn_apply_not_mem I _ (Or.inr hk), diagonal_apply]
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos hjk, one_mul, hjk]
    · rw [if_neg hjk, if_neg hjk, zero_mul]

theorem uni_blockOn_eq {g : Matrix (Fin n) (Fin n) F}
    (hoff : ∀ j k, (j ∉ I ∨ k ∉ I) → g j k = if j = k then 1 else 0) :
    blockOn F I (Matrix.of fun a b => g (I.equivFin.symm a) (I.equivFin.symm b)) = g := by
  ext j k
  by_cases hj : j ∈ I <;> by_cases hk : k ∈ I
  · rw [blockOn_apply_mem I _ hj hk, of_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · rw [blockOn_apply_not_mem I _ (Or.inr hk), hoff j k (Or.inr hk)]
  · rw [blockOn_apply_not_mem I _ (Or.inl hj), hoff j k (Or.inl hj)]
  · rw [blockOn_apply_not_mem I _ (Or.inl hj), hoff j k (Or.inl hj)]

end Matrix

section Block

variable {f n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F) (I : Finset (Fin n))

theorem uni_blockGL_mem {M : GL (Fin I.card) F}
    (hM : M ∈ primeFormUnitary h (oneGram F I.card)) :
    blockGL F I M ∈ primeFormUnitary h (oneGram F n) := by
  have hM' : ((M : Matrix (Fin I.card) (Fin I.card) F).map h.bar)ᵀ * M = 1 := by
    have h1 : ((M : Matrix (Fin I.card) (Fin I.card) F).map h.bar)ᵀ * 1 * M = 1 := hM
    rwa [Matrix.mul_one] at h1
  show ((blockOn F I (M : Matrix (Fin I.card) (Fin I.card) F)).map h.bar)ᵀ * 1 *
    blockOn F I (M : Matrix (Fin I.card) (Fin I.card) F) = 1
  rw [Matrix.mul_one, blockOn_map, blockOn_transpose, ← blockOn_mul, hM', blockOn_one]

@[expose] noncomputable def uniBlk :
    primeFormUnitary h (oneGram F I.card) →* primeFormUnitary h (oneGram F n) :=
  ((blockGL F I).comp (primeFormUnitary h (oneGram F I.card)).subtype).codRestrict _
    fun M => uni_blockGL_mem h I M.2

theorem coe_uniBlk (M : primeFormUnitary h (oneGram F I.card)) :
    (((uniBlk h I M : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) =
      blockOn F I ((M : GL (Fin I.card) F) : Matrix (Fin I.card) (Fin I.card) F) := rfl

theorem uniBlk_injective : Function.Injective (uniBlk h I) := fun M N hMN =>
  Subtype.ext (Units.ext (uni_blockOn_injective I (by rw [← coe_uniBlk, ← coe_uniBlk, hMN])))

theorem det_uniBlk (M : primeFormUnitary h (oneGram F I.card)) :
    (((uniBlk h I M : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F).det =
      ((M : GL (Fin I.card) F) : Matrix (Fin I.card) (Fin I.card) F).det :=
  det_blockOn I _

theorem uniBlk_apply_off (M : primeFormUnitary h (oneGram F I.card)) {j k : Fin n}
    (hjk : j ∉ I ∨ k ∉ I) :
    (((uniBlk h I M : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) j k = if j = k then 1 else 0 :=
  blockOn_apply_not_mem I _ hjk

theorem uni_exists_uniBlk {g : GL (Fin n) F} (hg : g ∈ primeFormUnitary h (oneGram F n))
    (hoff : ∀ j k, (j ∉ I ∨ k ∉ I) →
      (g : Matrix (Fin n) (Fin n) F) j k = if j = k then 1 else 0) :
    ∃ M : primeFormUnitary h (oneGram F I.card),
      ((uniBlk h I M : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) = g := by
  set X : Matrix (Fin I.card) (Fin I.card) F := Matrix.of fun a b =>
    (g : Matrix (Fin n) (Fin n) F) (I.equivFin.symm a) (I.equivFin.symm b) with hX
  have hXg : blockOn F I X = (g : Matrix (Fin n) (Fin n) F) := uni_blockOn_eq I hoff
  have hdet : X.det ≠ 0 := by
    rw [← det_blockOn I X, hXg]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hXU : (X.map h.bar)ᵀ * X = 1 := by
    apply uni_blockOn_injective I
    have h1 : ((g : Matrix (Fin n) (Fin n) F).map h.bar)ᵀ * 1 * g = 1 := hg
    rw [Matrix.mul_one] at h1
    rw [blockOn_mul, ← blockOn_transpose, ← blockOn_map, hXg, h1, blockOn_one]
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero X hdet, ?_⟩, Units.ext hXg⟩
  show (X.map h.bar)ᵀ * 1 * X = 1
  rw [Matrix.mul_one, hXU]

theorem uniBlk_fieldU (σ : F ≃+* F) (M : primeFormUnitary h (oneGram F I.card)) :
    primeFormFieldU h uni_isPrimeFormGram_one σ (uniBlk h I M) =
      uniBlk h I (primeFormFieldU h uni_isPrimeFormGram_one σ M) := by
  apply Subtype.ext
  apply Units.ext
  show (blockOn F I ((M : GL (Fin I.card) F) : Matrix (Fin I.card) (Fin I.card) F)).map σ =
    blockOn F I (((M : GL (Fin I.card) F) : Matrix (Fin I.card) (Fin I.card) F).map σ)
  exact blockOn_map I (σ : F →+* F) _

theorem uni_bar_mul_diag {D : primeFormUnitary h (oneGram F n)}
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (j : Fin n) :
    h.bar (((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j) *
      ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = 1 := by
  have h1 : (((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map h.bar)ᵀ * 1 *
      ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := D.2
  have h2 := congrFun (congrFun h1 j) j
  rw [← hD.diagonal_diag, diagonal_map (map_zero _), diagonal_transpose, Matrix.mul_one,
    diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at h2
  exact h2

theorem uni_exists_restr (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) :
    ∃ D' : primeFormUnitary h (oneGram F I.card),
      ((D' : GL (Fin I.card) F) : Matrix (Fin I.card) (Fin I.card) F).IsDiag ∧
      ∀ (σ : F ≃+* F) (g : primeFormUnitary h (oneGram F I.card)),
        ((SemidirectProduct.inl D * SemidirectProduct.inr σ : UniGamma h n) *
            SemidirectProduct.inl (uniBlk h I g) *
            (SemidirectProduct.inl D * SemidirectProduct.inr σ)⁻¹).left =
          uniBlk h I ((SemidirectProduct.inl D' * SemidirectProduct.inr σ :
            blockGamma h I.card) * SemidirectProduct.inl g *
              (SemidirectProduct.inl D' * SemidirectProduct.inr σ)⁻¹).left := by
  classical
  set d : Fin n → F := Matrix.diag ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hd
  have hDd : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal d :=
    hD.diagonal_diag.symm
  have hu : ∀ j, h.bar (d j) * d j = 1 := uni_bar_mul_diag h hD
  have hne : ∀ j, d j ≠ 0 := fun j h0 => by
    have h1 := hu j
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  set e : Fin I.card → Fin n := fun a => (I.equivFin.symm a : Fin n) with he
  let D'GL : GL (Fin I.card) F := ⟨diagonal fun a => d (e a), diagonal fun a => (d (e a))⁻¹,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext a
      exact mul_inv_cancel₀ (hne _),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext a
      exact inv_mul_cancel₀ (hne _)⟩
  have hD'U : D'GL ∈ primeFormUnitary h (oneGram F I.card) := by
    show ((diagonal fun a => d (e a)).map h.bar)ᵀ * 1 * diagonal (fun a => d (e a)) = 1
    rw [diagonal_map (map_zero _), diagonal_transpose, Matrix.mul_one, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext a
    exact hu _
  refine ⟨⟨D'GL, hD'U⟩, isDiag_diagonal _, fun σ g => ?_⟩
  rw [uni_conj_inl_inr_left, uni_conj_inl_inr_left, uniBlk_fieldU, map_mul, map_mul, map_inv]
  set Y := uniBlk h I (primeFormFieldU h uni_isPrimeFormGram_one σ g) with hY
  set B' := uniBlk h I ⟨D'GL, hD'U⟩ with hB'
  have hDR : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((B' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        diagonal (fun j => if j ∈ I then 1 else d j) := by
    rw [hDd, hB', coe_uniBlk]
    exact (uni_blockOn_diagonal_mul I d).symm
  have hR : (((B'⁻¹ * D : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = diagonal (fun j => if j ∈ I then 1 else d j) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hDR, Units.inv_mul_cancel_left]
  have hcomm : (B'⁻¹ * D) * Y = Y * (B'⁻¹ * D) := by
    apply Subtype.ext
    apply Units.ext
    have e1 : ((((B'⁻¹ * D) * Y : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = (((B'⁻¹ * D : primeFormUnitary h (oneGram F n)) :
          GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((Y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl
    have e2 : (((Y * (B'⁻¹ * D) : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = ((Y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (((B'⁻¹ * D : primeFormUnitary h (oneGram F n)) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) := rfl
    rw [e1, e2, hR, hY, coe_uniBlk]
    refine uni_diagonal_commute_blockOn I (fun j hj k hk => ?_) _
    rw [if_pos hj, if_pos hk]
  calc D * Y * D⁻¹ = B' * ((B'⁻¹ * D) * Y * (B'⁻¹ * D)⁻¹) * B'⁻¹ := by group
    _ = B' * (Y * (B'⁻¹ * D) * (B'⁻¹ * D)⁻¹) * B'⁻¹ := by rw [hcomm]
    _ = B' * Y * B'⁻¹ := by group

end Block

section Frame

variable {f n : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem uni_block_frame {X : Type} [Group X] {K B : Subgroup X}
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hf : f = 1 ∨ f = 3) (hn : 3 ≤ n) (h3 : ¬ 3 ∣ n)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* primeFormP h (oneGram F n)) {σ : F ≃+* F}
    (hσ : σ ^ 3 = 1)
    (hframe : ∀ (b : X) (hb : b ∈ B), ∃ D : primeFormUnitary h (oneGram F n),
      ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag ∧ D ^ 3 = 1 ∧ ∃ k : ℕ,
        uniAut e ⟨b, hBK hb⟩ = primeFormPsi h uni_isPrimeFormGram_one
          (SemidirectProduct.inl D * SemidirectProduct.inr (σ ^ k)))
    (I : Finset (Fin n)) :
    ∃ x : ↥B → blockGamma h I.card,
      (∀ (b : ↥B) (g : primeFormUnitary h (oneGram F I.card)),
        uniAut e ⟨b, hBK b.2⟩ (((uniTheta h hf hn h3).comp (uniBlk h I)) g) =
          ((uniTheta h hf hn h3).comp (uniBlk h I))
            ((x b * SemidirectProduct.inl g * (x b)⁻¹).left)) ∧
      ∀ b : ↥B, ∃ D : primeFormUnitary h (oneGram F I.card),
        ((D : GL (Fin I.card) F) : Matrix (Fin I.card) (Fin I.card) F).IsDiag ∧ ∃ φ : F ≃+* F,
          (∀ c : F, c ^ 3 = 1 → φ c = c) ∧
            (SemidirectProduct.inl 1)⁻¹ * x b * SemidirectProduct.inl 1 =
              SemidirectProduct.inl D * SemidirectProduct.inr φ := by
  choose D hD _ k hk using hframe
  choose D' hD' hconj using fun (b : X) (hb : b ∈ B) => uni_exists_restr h I (D b hb) (hD b hb)
  refine ⟨fun b => SemidirectProduct.inl (D' b b.2) * SemidirectProduct.inr (σ ^ k b b.2),
    fun b g => ?_, fun b => ⟨D' b b.2, hD' b b.2, σ ^ k b b.2, fun c hc => ?_, ?_⟩⟩
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hk b b.2, uniTheta_psi, hconj]
  · have hσk : (σ ^ k b b.2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hσ, one_pow]
    exact uni_fix_cube_root hσk hc
  · rw [map_one, inv_one, one_mul, mul_one]

end Frame

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end

module

public import CFSG.LieType.SeitzGeneration.OrthCubeSplit

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

section Matrix

variable {K : Type} [Field K]

theorem scalar_of_commute_fin_two {M : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ Y : Matrix (Fin 2) (Fin 2) K, M * Y = Y * M) : M = M 0 0 • 1 := by
  have h1 := h !![0, 1; 0, 0]
  have h2 := h !![0, 0; 1, 0]
  rw [Matrix.eta_fin_two M] at h1 h2 ⊢
  simp only [Matrix.mul_fin_two] at h1 h2
  have e10 : M 1 0 = 0 := by
    have := congrFun (congrFun h1 0) 0
    simpa using this.symm
  have e11 : M 1 1 = M 0 0 := by
    have := congrFun (congrFun h1 0) 1
    simp at this
    exact this.symm
  have e01 : M 0 1 = 0 := by
    have := congrFun (congrFun h2 0) 0
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e10, e11, e01]

@[expose] def colZero : Submodule K (Matrix (Fin 2) (Fin 2) K) where
  carrier := {X | X 0 0 = 0 ∧ X 1 0 = 0}
  add_mem' := fun ha hb => ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := fun c X hX => ⟨by simp [hX.1], by simp [hX.2]⟩

theorem mul_mem_colZero (x : Matrix (Fin 2) (Fin 2) K) {X : Matrix (Fin 2) (Fin 2) K}
    (hX : X ∈ colZero) : x * X ∈ colZero := by
  refine ⟨?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hX.1, hX.2]

theorem det_eq_zero_of_mem_colZero {X : Matrix (Fin 2) (Fin 2) K} (hX : X ∈ colZero) :
    X.det = 0 := by
  rw [Matrix.det_fin_two, hX.1, hX.2]
  ring

end Matrix

section M2

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_stable_cube_m2 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : orthDerived Q = elementaryGroup Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P₀ P₁ P₂ P₃ : HypPair Q} (h01 : P₀.Orth P₁) (h23 : P₂.Orth P₃) (h02 : P₀.Orth P₂)
    (h03 : P₀.Orth P₃) (h12 : P₁.Orth P₂) (h13 : P₁.Orth P₃) {x : Matrix (Fin 2) (Fin 2) K}
    (hdet : x.det = 1) (hxp : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ E : Subgroup (elementaryGroup Q), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ v ∈ W, Q v = 0) ∧
        ∀ g ∈ E, ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set B₁ := m2Block h01 with hB₁
  set B₂ := m2Block h23 with hB₂
  have h12m : ∀ y, B₁.m (B₂.ι y) = 0 := fun y =>
    m2Proj_m2Emb_of_orth (hypPair_orth_symm h02) (hypPair_orth_symm h12)
      (hypPair_orth_symm h03) (hypPair_orth_symm h13) y
  have h21m : ∀ X, B₂.m (B₁.ι X) = 0 := fun X => m2Proj_m2Emb_of_orth h02 h03 h12 h13 X
  have hunit : IsUnit x.det := by rw [hdet]; exact isUnit_one
  have hxx : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x hunit
  have hxx' : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul x hunit
  have hL1 : LinearMap.mulLeft K x ∘ₗ LinearMap.mulLeft K x⁻¹ = LinearMap.id := by
    rw [← LinearMap.mulLeft_mul, hxx, LinearMap.mulLeft_one]
  have hL2 : LinearMap.mulLeft K x⁻¹ ∘ₗ LinearMap.mulLeft K x = LinearMap.id := by
    rw [← LinearMap.mulLeft_mul, hxx', LinearMap.mulLeft_one]
  have hR1 : LinearMap.mulRight K x ∘ₗ LinearMap.mulRight K x⁻¹ = LinearMap.id := by
    rw [← LinearMap.mulRight_mul, hxx', LinearMap.mulRight_one]
  have hR2 : LinearMap.mulRight K x⁻¹ ∘ₗ LinearMap.mulRight K x = LinearMap.id := by
    rw [← LinearMap.mulRight_mul, hxx, LinearMap.mulRight_one]
  have hLq : ∀ X : Matrix (Fin 2) (Fin 2) K, (LinearMap.mulLeft K x X).det = X.det := fun X => by
    change (x * X).det = X.det
    rw [Matrix.det_mul, hdet, one_mul]
  have hRq : ∀ X : Matrix (Fin 2) (Fin 2) K, (LinearMap.mulRight K x X).det = X.det := fun X => by
    change (X * x).det = X.det
    rw [Matrix.det_mul, hdet, mul_one]
  have hLp : LinearMap.mulLeft K x ^ p = 1 := by
    rw [LinearMap.pow_mulLeft, hxp, LinearMap.mulLeft_one]
    rfl
  have hRp : LinearMap.mulRight K x ^ p = 1 := by
    rw [LinearMap.pow_mulRight, hxp, LinearMap.mulRight_one]
    rfl
  let g₁ : V ≃ₗ[K] V := B₂.blkEquivOf _ _ hL1 hL2
  let g₂ : V ≃ₗ[K] V := B₁.blkEquivOf _ _ hL1 hL2
  let g₃ : V ≃ₗ[K] V := B₁.blkEquivOf _ _ hR1 hR2
  have hg₁ : g₁ ∈ elementaryGroup Q := mem_elementaryGroup_of_odd_pow hQ hT hE hp hp2
    (B₂.blkEquivOf_mem_orthogonalGroup _ _ hL1 hL2 hLq) (B₂.blkEquivOf_pow_eq_one _ _ hL1 hL2 hLp)
  have hg₂ : g₂ ∈ elementaryGroup Q := mem_elementaryGroup_of_odd_pow hQ hT hE hp hp2
    (B₁.blkEquivOf_mem_orthogonalGroup _ _ hL1 hL2 hLq) (B₁.blkEquivOf_pow_eq_one _ _ hL1 hL2 hLp)
  have hg₃ : g₃ ∈ elementaryGroup Q := mem_elementaryGroup_of_odd_pow hQ hT hE hp hp2
    (B₁.blkEquivOf_mem_orthogonalGroup _ _ hR1 hR2 hRq) (B₁.blkEquivOf_pow_eq_one _ _ hR1 hR2 hRp)
  let G₁ : elementaryGroup Q := ⟨g₁, hg₁⟩
  let G₂ : elementaryGroup Q := ⟨g₂, hg₂⟩
  let G₃ : elementaryGroup Q := ⟨g₃, hg₃⟩
  have hG₁p : G₁ ^ p = 1 := Subtype.ext (B₂.blkEquivOf_pow_eq_one _ _ hL1 hL2 hLp)
  have hG₂p : G₂ ^ p = 1 := Subtype.ext (B₁.blkEquivOf_pow_eq_one _ _ hL1 hL2 hLp)
  have hG₃p : G₃ ^ p = 1 := Subtype.ext (B₁.blkEquivOf_pow_eq_one _ _ hR1 hR2 hRp)
  have a1 : ∀ (a : ℕ) (X : Matrix (Fin 2) (Fin 2) K), (g₁ ^ a) (B₂.ι X) = B₂.ι (x ^ a * X) :=
    fun a X => by
      rw [QBlock.blkEquivOf_pow_apply, QBlock.blk_ι, LinearMap.pow_mulLeft]
      rfl
  have a1' : ∀ (a : ℕ) (X : Matrix (Fin 2) (Fin 2) K), (g₁ ^ a) (B₁.ι X) = B₁.ι X := fun a X => by
    rw [QBlock.blkEquivOf_pow_apply]
    exact QBlock.blk_of_m_eq_zero _ _ (h21m X)
  have a2 : ∀ (b : ℕ) (X : Matrix (Fin 2) (Fin 2) K), (g₂ ^ b) (B₁.ι X) = B₁.ι (x ^ b * X) :=
    fun b X => by
      rw [QBlock.blkEquivOf_pow_apply, QBlock.blk_ι, LinearMap.pow_mulLeft]
      rfl
  have a2' : ∀ (b : ℕ) (X : Matrix (Fin 2) (Fin 2) K), (g₂ ^ b) (B₂.ι X) = B₂.ι X := fun b X => by
    rw [QBlock.blkEquivOf_pow_apply]
    exact QBlock.blk_of_m_eq_zero _ _ (h12m X)
  have a3 : ∀ (c : ℕ) (X : Matrix (Fin 2) (Fin 2) K), (g₃ ^ c) (B₁.ι X) = B₁.ι (X * x ^ c) :=
    fun c X => by
      rw [QBlock.blkEquivOf_pow_apply, QBlock.blk_ι, LinearMap.pow_mulRight]
      rfl
  have a3' : ∀ (c : ℕ) (X : Matrix (Fin 2) (Fin 2) K), (g₃ ^ c) (B₂.ι X) = B₂.ι X := fun c X => by
    rw [QBlock.blkEquivOf_pow_apply]
    exact QBlock.blk_of_m_eq_zero _ _ (h12m X)
  have hι₁ : Function.Injective B₁.ι := fun X Y h => by
    rw [← B₁.m_ι X, ← B₁.m_ι Y, h]
  have hι₂ : Function.Injective B₂.ι := fun X Y h => by
    rw [← B₂.m_ι X, ← B₂.m_ι Y, h]
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hdvd : ∀ a : ℕ, a < p → x ^ a = 1 → a = 0 := fun a ha h =>
    Nat.eq_zero_of_dvd_of_lt (hord ▸ orderOf_dvd_of_pow_eq_one h) ha
  have c12 : Commute G₁ G₂ := Subtype.ext (LinearEquiv.ext fun v => by
    change B₂.blk _ (B₁.blk _ v) = B₁.blk _ (B₂.blk _ v)
    exact B₂.blk_comm B₁ h21m h12m _ _ v)
  have c13 : Commute G₁ G₃ := Subtype.ext (LinearEquiv.ext fun v => by
    change B₂.blk _ (B₁.blk _ v) = B₁.blk _ (B₂.blk _ v)
    exact B₂.blk_comm B₁ h21m h12m _ _ v)
  have c23 : Commute G₂ G₃ := Subtype.ext (LinearEquiv.ext fun v => by
    change B₁.blk _ (B₁.blk _ v) = B₁.blk _ (B₁.blk _ v)
    have hLR : LinearMap.mulLeft K x ∘ₗ LinearMap.mulRight K x =
        LinearMap.mulRight K x ∘ₗ LinearMap.mulLeft K x :=
      LinearMap.ext fun X => (Matrix.mul_assoc x X x).symm
    rw [← QBlock.blk_comp, ← QBlock.blk_comp, hLR])
  have hind := indep_of_nat hp.pos hG₁p hG₂p hG₃p fun a b c ha hb hc h => by
    have hv : ∀ v : V, (((G₁ ^ a * G₂ ^ b * G₃ ^ c : elementaryGroup Q)) : V ≃ₗ[K] V) v = v :=
      fun v => by rw [h]; rfl
    have hv' : ∀ v : V, (g₁ ^ a) ((g₂ ^ b) ((g₃ ^ c) v)) = v := fun v => by
      have := hv v
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, LinearEquiv.mul_apply] at this
      exact this
    have e2 := hv' (B₂.ι 1)
    rw [a3', a2', a1, mul_one] at e2
    have ha0 : a = 0 := hdvd a ha (by simpa using hι₂ e2)
    subst ha0
    have e1 : ∀ X, x ^ b * (X * x ^ c) = X := fun X => by
      have := hv' (B₁.ι X)
      rw [a3, a2, pow_zero] at this
      exact hι₁ this
    have hMN : x ^ b * x ^ c = 1 := by simpa using e1 1
    have hNM : x ^ c * x ^ b = 1 := by
      rw [← pow_add, add_comm, pow_add]
      exact hMN
    have hcomm' : ∀ Y, x ^ b * Y = Y * x ^ b := fun Y => by
      calc x ^ b * Y = x ^ b * Y * (x ^ c * x ^ b) := by rw [hNM, Matrix.mul_one]
        _ = (x ^ b * (Y * x ^ c)) * x ^ b := by simp only [Matrix.mul_assoc]
        _ = Y * x ^ b := by rw [e1]
    have hsc := scalar_of_commute_fin_two hcomm'
    set t := (x ^ b) 0 0 with ht
    have hdet2 : t * t = 1 := by
      have := congrArg Matrix.det hsc
      rw [Matrix.det_pow, hdet, one_pow, Matrix.det_smul, Matrix.det_one, Fintype.card_fin,
        mul_one, _root_.sq] at this
      exact this.symm
    have htp : t ^ p = 1 := by
      have h1 : (x ^ b) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxp, one_pow]
      rw [hsc, smul_pow, one_pow] at h1
      have := congrFun (congrFun h1 0) 0
      simpa using this
    have ht1 : t = 1 := by
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      rw [hk, pow_succ, pow_mul, _root_.sq, hdet2, one_pow, one_mul] at htp
      exact htp
    have hxb : x ^ b = 1 := by rw [hsc, ht1, one_smul]
    have hxc : x ^ c = 1 := by rwa [hxb, Matrix.one_mul] at hMN
    exact ⟨rfl, hdvd b hb hxb, hdvd c hc hxc⟩
  obtain ⟨E, hEab, hEcard, hEform, -⟩ := exists_cube_of_three hp c12 c13 c23 hG₁p hG₂p hG₃p hind
  refine ⟨E, hEab, hEcard, colZero.map B₂.ι, ?_, ?_, ?_⟩
  · intro h0
    have hmem : B₂.ι !![0, 1; 0, 0] ∈ colZero.map B₂.ι :=
      Submodule.mem_map_of_mem (p := colZero) (show !![0, 1; 0, 0] ∈ colZero from ⟨rfl, rfl⟩)
    rw [h0, Submodule.mem_bot] at hmem
    have := hι₂ (hmem.trans (map_zero B₂.ι).symm)
    have h01' := congrFun (congrFun this 0) 1
    simp at h01'
  · rintro _ ⟨X, hX, rfl⟩
    rw [show Q (B₂.ι X) = X.det from Q_m2Emb h23 X]
    exact det_eq_zero_of_mem_colZero hX
  · intro y hy w hw
    obtain ⟨i, j, k, rfl⟩ := hEform y hy
    obtain ⟨X, hX, rfl⟩ := hw
    obtain ⟨a, -, hia, -⟩ := exists_nat_pow_of_pow_eq_one hp.pos hG₁p i
    obtain ⟨b, -, hjb, -⟩ := exists_nat_pow_of_pow_eq_one hp.pos hG₂p j
    obtain ⟨d, -, hkd, -⟩ := exists_nat_pow_of_pow_eq_one hp.pos hG₃p k
    rw [hia, hjb, hkd]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, LinearEquiv.mul_apply]
    change (g₁ ^ a) ((g₂ ^ b) ((g₃ ^ d) (B₂.ι X))) ∈ colZero.map B₂.ι
    rw [a3', a2', a1]
    exact Submodule.mem_map_of_mem (mul_mem_colZero _ hX)

end M2

end CFSG.LieType.SeitzGeneration

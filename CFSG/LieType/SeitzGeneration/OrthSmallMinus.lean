module

public import CFSG.LieType.SeitzGeneration.OrthAnisoTorus
public import CFSG.LieType.SeitzGeneration.OrthHyperExSplit
public import CFSG.LieType.SeitzGeneration.OrthEx

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank TauCeti
open CFSG.RankThree.Classical2 (orthDerived)

section Tail

variable {n : ℕ} {K : Type} [Field K]

@[expose] def tailEmb : (Fin 2 → K) →ₗ[K] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) where
  toFun y := y 0 • Pi.single (Sum.inr (Sum.inr 0)) 1 + y 1 • Pi.single (Sum.inr (Sum.inr 1)) 1
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

@[expose] def tailProj : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun v := ![v (Sum.inr (Sum.inr 0)), v (Sum.inr (Sum.inr 1))]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

theorem tailProj_emb (y : Fin 2 → K) : tailProj (n := n) (tailEmb y) = y := by
  ext i; fin_cases i <;> simp [tailProj, tailEmb]

theorem Q_tail_add (b c : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) (y : Fin 2 → K)
    (hv : tailProj v = 0) :
    quadMinus n K b c (v + tailEmb y) =
      quadMinus n K b c v + (y 0 ^ 2 + b * y 0 * y 1 + c * y 1 ^ 2) := by
  have e0 := congrFun hv 0
  have e1 := congrFun hv 1
  simp [tailProj] at e0 e1
  rw [quadMinus_apply, quadMinus_apply]
  simp [tailEmb, e0, e1]
  ring

@[expose] def tailBlock (b c : K) : QBlock (quadMinus n K b c) (Fin 2 → K) where
  ι := tailEmb
  m := tailProj
  qM y := y 0 ^ 2 + b * y 0 * y 1 + c * y 1 ^ 2
  m_ι := tailProj_emb
  Q_add v y hv := Q_tail_add b c v y hv

theorem tailBlock_m (b c : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    (tailBlock (n := n) b c).m v = ![v (Sum.inr (Sum.inr 0)), v (Sum.inr (Sum.inr 1))] := rfl

theorem tailBlock_ι (b c : K) (y : Fin 2 → K) :
    (tailBlock (n := n) b c).ι y =
      y 0 • Pi.single (Sum.inr (Sum.inr 0)) 1 + y 1 • Pi.single (Sum.inr (Sum.inr 1)) 1 := rfl

theorem tailProj_m2Emb {b c : K} (i j : Fin (n - 1)) (X : Matrix (Fin 2) (Fin 2) K) :
    (tailBlock (n := n) b c).m (m2Emb (minusPair K b c i) (minusPair K b c j) X) = 0 := by
  ext k; fin_cases k <;> simp [tailBlock_m, m2Emb, minusPair_e, minusPair_f]

theorem m2Proj_tailEmb {b c : K} (i j : Fin (n - 1)) (y : Fin 2 → K) :
    m2Proj (minusPair K b c i) (minusPair K b c j) ((tailBlock (n := n) b c).ι y) = 0 := by
  have h : ∀ (k : Fin (n - 1)) (z : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      z = (tailBlock (n := n) b c).ι y →
        polar (quadMinus n K b c) z (Pi.single (Sum.inl k) 1) = 0 ∧
          polar (quadMinus n K b c) z (Pi.single (Sum.inr (Sum.inl k)) 1) = 0 := by
    rintro k z rfl
    rw [polar_comm, polar_single_inl_quadMinus, polar_comm, polar_single_inr_quadMinus]
    simp [tailBlock_ι]
  ext r s; fin_cases r <;> fin_cases s <;>
    simp [m2Proj, minusPair_e, minusPair_f, (h i _ rfl).1, (h i _ rfl).2, (h j _ rfl).1,
      (h j _ rfl).2]

end Tail

section Cube

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_stable_cube_m2_rot (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : orthDerived Q = elementaryGroup Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P₀ P₁ : HypPair Q} (h01 : P₀.Orth P₁) {M' : Type} [AddCommGroup M'] [Module K M']
    (C : QBlock Q M') (hBC : ∀ y, (m2Block h01).m (C.ι y) = 0)
    (hCB : ∀ X, C.m ((m2Block h01).ι X) = 0) {w₀ : V} (hw₀ : w₀ ≠ 0) (hw₀Q : Q w₀ = 0)
    (hBw : (m2Block h01).m w₀ = 0) (hCw : C.m w₀ = 0) {T T' : M' →ₗ[K] M'}
    (h1 : T ∘ₗ T' = LinearMap.id) (h2 : T' ∘ₗ T = LinearMap.id) (hTq : ∀ y, C.qM (T y) = C.qM y)
    (hTp : T ^ p = 1) {y₀ : M'} (hTfix : ∀ a : ℕ, a < p → (T ^ a) y₀ = y₀ → a = 0)
    {x : Matrix (Fin 2) (Fin 2) K} (hdet : x.det = 1) (hxp : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ E : Subgroup (elementaryGroup Q), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ v ∈ W, Q v = 0) ∧
        ∀ g ∈ E, ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set B := m2Block h01 with hB
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
  let g₁ : V ≃ₗ[K] V := C.blkEquivOf T T' h1 h2
  let g₂ : V ≃ₗ[K] V := B.blkEquivOf _ _ hL1 hL2
  let g₃ : V ≃ₗ[K] V := B.blkEquivOf _ _ hR1 hR2
  have hg₁ : g₁ ∈ elementaryGroup Q := mem_elementaryGroup_of_odd_pow hQ hT hE hp hp2
    (C.blkEquivOf_mem_orthogonalGroup _ _ h1 h2 hTq) (C.blkEquivOf_pow_eq_one _ _ h1 h2 hTp)
  have hg₂ : g₂ ∈ elementaryGroup Q := mem_elementaryGroup_of_odd_pow hQ hT hE hp hp2
    (B.blkEquivOf_mem_orthogonalGroup _ _ hL1 hL2 hLq) (B.blkEquivOf_pow_eq_one _ _ hL1 hL2 hLp)
  have hg₃ : g₃ ∈ elementaryGroup Q := mem_elementaryGroup_of_odd_pow hQ hT hE hp hp2
    (B.blkEquivOf_mem_orthogonalGroup _ _ hR1 hR2 hRq) (B.blkEquivOf_pow_eq_one _ _ hR1 hR2 hRp)
  let G₁ : elementaryGroup Q := ⟨g₁, hg₁⟩
  let G₂ : elementaryGroup Q := ⟨g₂, hg₂⟩
  let G₃ : elementaryGroup Q := ⟨g₃, hg₃⟩
  have hG₁p : G₁ ^ p = 1 := Subtype.ext (C.blkEquivOf_pow_eq_one _ _ h1 h2 hTp)
  have hG₂p : G₂ ^ p = 1 := Subtype.ext (B.blkEquivOf_pow_eq_one _ _ hL1 hL2 hLp)
  have hG₃p : G₃ ^ p = 1 := Subtype.ext (B.blkEquivOf_pow_eq_one _ _ hR1 hR2 hRp)
  have a1 : ∀ (a : ℕ) (y : M'), (g₁ ^ a) (C.ι y) = C.ι ((T ^ a) y) := fun a y => by
    rw [QBlock.blkEquivOf_pow_apply, QBlock.blk_ι]
  have a1' : ∀ (a : ℕ) (X : Matrix (Fin 2) (Fin 2) K), (g₁ ^ a) (B.ι X) = B.ι X := fun a X => by
    rw [QBlock.blkEquivOf_pow_apply]
    exact QBlock.blk_of_m_eq_zero _ _ (hCB X)
  have a2 : ∀ (b : ℕ) (X : Matrix (Fin 2) (Fin 2) K), (g₂ ^ b) (B.ι X) = B.ι (x ^ b * X) :=
    fun b X => by
      rw [QBlock.blkEquivOf_pow_apply, QBlock.blk_ι, LinearMap.pow_mulLeft]
      rfl
  have a2' : ∀ (b : ℕ) (y : M'), (g₂ ^ b) (C.ι y) = C.ι y := fun b y => by
    rw [QBlock.blkEquivOf_pow_apply]
    exact QBlock.blk_of_m_eq_zero _ _ (hBC y)
  have a3 : ∀ (c : ℕ) (X : Matrix (Fin 2) (Fin 2) K), (g₃ ^ c) (B.ι X) = B.ι (X * x ^ c) :=
    fun c X => by
      rw [QBlock.blkEquivOf_pow_apply, QBlock.blk_ι, LinearMap.pow_mulRight]
      rfl
  have a3' : ∀ (c : ℕ) (y : M'), (g₃ ^ c) (C.ι y) = C.ι y := fun c y => by
    rw [QBlock.blkEquivOf_pow_apply]
    exact QBlock.blk_of_m_eq_zero _ _ (hBC y)
  have hιB : Function.Injective B.ι := fun X Y h => by rw [← B.m_ι X, ← B.m_ι Y, h]
  have hιC : Function.Injective C.ι := fun X Y h => by rw [← C.m_ι X, ← C.m_ι Y, h]
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hdvd : ∀ a : ℕ, a < p → x ^ a = 1 → a = 0 := fun a ha h =>
    Nat.eq_zero_of_dvd_of_lt (hord ▸ orderOf_dvd_of_pow_eq_one h) ha
  have c12 : Commute G₁ G₂ := Subtype.ext (LinearEquiv.ext fun v => by
    change C.blk _ (B.blk _ v) = B.blk _ (C.blk _ v)
    exact C.blk_comm B hCB hBC _ _ v)
  have c13 : Commute G₁ G₃ := Subtype.ext (LinearEquiv.ext fun v => by
    change C.blk _ (B.blk _ v) = B.blk _ (C.blk _ v)
    exact C.blk_comm B hCB hBC _ _ v)
  have c23 : Commute G₂ G₃ := Subtype.ext (LinearEquiv.ext fun v => by
    change B.blk _ (B.blk _ v) = B.blk _ (B.blk _ v)
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
    have e2 := hv' (C.ι y₀)
    rw [a3', a2', a1] at e2
    have ha0 : a = 0 := hTfix a ha (hιC e2)
    subst ha0
    have e1 : ∀ X, x ^ b * (X * x ^ c) = X := fun X => by
      have := hv' (B.ι X)
      rw [a3, a2, pow_zero] at this
      exact hιB this
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
  have hf₁ : g₁ w₀ = w₀ := QBlock.blk_of_m_eq_zero _ _ hCw
  have hf₂ : g₂ w₀ = w₀ := QBlock.blk_of_m_eq_zero _ _ hBw
  have hf₃ : g₃ w₀ = w₀ := QBlock.blk_of_m_eq_zero _ _ hBw
  refine ⟨E, hEab, hEcard, K ∙ w₀, fun h0 => hw₀ (Submodule.span_singleton_eq_bot.mp h0), ?_, ?_⟩
  · intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [QuadraticMap.map_smul, hw₀Q, smul_zero]
  · intro y hy w hw
    obtain ⟨i, j, k, rfl⟩ := hEform y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hfix : ((G₁ ^ i * G₂ ^ j * G₃ ^ k : elementaryGroup Q) : V ≃ₗ[K] V) w₀ = w₀ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow, LinearEquiv.mul_apply]
      rw [OrthBlk.zpow_apply_of_fixed hf₃ k, OrthBlk.zpow_apply_of_fixed hf₂ j,
        OrthBlk.zpow_apply_of_fixed hf₁ i]
    rw [map_smul, hfix]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w₀)

end Cube

section Model

variable {K : Type} [Field K]

theorem rotMat_pow_exists (b c α β : K) (n : ℕ) :
    ∃ α' β' : K, rotMat b c α β ^ n = rotMat b c α' β' := by
  induction n with
  | zero => exact ⟨1, 0, by rw [pow_zero, rotMat_one]⟩
  | succ n ih =>
    obtain ⟨α', β', h⟩ := ih
    exact ⟨_, _, by rw [pow_succ, h, rotMat_mul]⟩

theorem m2Proj_eq_zero_of_orth {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    {P P' R : HypPair Q} (h : R.Orth P) (h' : R.Orth P') : m2Proj P P' R.e = 0 := by
  have a1 : polar Q R.e P.f = 0 := h.ef
  have a2 : polar Q R.e P'.f = 0 := h'.ef
  have a3 : polar Q R.e P'.e = 0 := h'.ee
  have a4 : polar Q R.e P.e = 0 := h.ee
  ext i j; fin_cases i <;> fin_cases j <;> simp [m2Proj, a1, a2, a3, a4]

variable [Finite K]

theorem exists_hyperGen_minus_four {d : ValidLieTypeIndex} {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {π : elementaryGroup (quadMinus 4 K b c) →* Cat d}
    (hc : IsOrthogonalCover (quadMinus 4 K b c) π)
    (hT : ∃ T : Submodule K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K), finrank K T = 3 ∧
      ∀ x ∈ T, quadMinus 4 K b c x = 0)
    (hE : orthDerived (quadMinus 4 K b c) = elementaryGroup (quadMinus 4 K b c)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hpq : p ∣ Nat.card K + 1) :
    ∃ E' : Subgroup (Cat d), IsElemAbelian p E' ∧ Nat.card E' = p ^ 3 ∧
      HyperGen p (⊤ : Subgroup (Cat d)) E' := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hdet, hxp, hx1⟩ := exists_sl2_order hp (dvd_sq_sub_one_of_dvd_add_one hpq)
  obtain ⟨α, β, hN, hMp, hM1⟩ := exists_rotMat_order hirr hp hp2 hpq
  set M := rotMat b c α β with hM
  have hMunit : IsUnit M.det := by rw [hM, det_rotMat, hN]; exact isUnit_one
  let T : Module.End K (Fin 2 → K) := Matrix.toLinAlgEquiv' M
  let T' : Module.End K (Fin 2 → K) := Matrix.toLinAlgEquiv' M⁻¹
  have h1 : T ∘ₗ T' = LinearMap.id := by
    change T * T' = 1
    rw [← map_mul, Matrix.mul_nonsing_inv M hMunit, map_one]
  have h2 : T' ∘ₗ T = LinearMap.id := by
    change T' * T = 1
    rw [← map_mul, Matrix.nonsing_inv_mul M hMunit, map_one]
  have hTapp : ∀ (a : ℕ) (y : Fin 2 → K), (T ^ a) y = (M ^ a).mulVec y := fun a y => by
    rw [← map_pow, Matrix.toLinAlgEquiv'_apply]
  have hTq : ∀ y, (tailBlock (n := 4) b c).qM (T y) = (tailBlock (n := 4) b c).qM y := fun y => by
    have := hTapp 1 y
    rw [pow_one, pow_one] at this
    change (T y) 0 ^ 2 + b * (T y) 0 * (T y) 1 + c * (T y) 1 ^ 2 =
      y 0 ^ 2 + b * y 0 * y 1 + c * y 1 ^ 2
    rw [this]
    exact rotMat_isom b c α β hN y
  have hTp : T ^ p = 1 := by
    change Matrix.toLinAlgEquiv' M ^ p = 1
    rw [← map_pow, hMp, map_one]
  have hordM : orderOf M = p := orderOf_eq_prime hMp hM1
  have hTfix : ∀ a : ℕ, a < p → (T ^ a) ![1, 0] = ![1, 0] → a = 0 := by
    intro a ha h
    obtain ⟨α', β', hab⟩ := rotMat_pow_exists b c α β a
    rw [hTapp, hab] at h
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    simp [rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
    have hMa : M ^ a = 1 := by rw [hab, e0, e1, rotMat_one]
    exact Nat.eq_zero_of_dvd_of_lt (hordM ▸ orderOf_dvd_of_pow_eq_one hMa) ha
  let i₀ : Fin (4 - 1) := ⟨0, by norm_num⟩
  let i₁ : Fin (4 - 1) := ⟨1, by norm_num⟩
  let i₂ : Fin (4 - 1) := ⟨2, by norm_num⟩
  have h01 : (minusPair K b c i₀).Orth (minusPair K b c i₁) :=
    minusPair_orth (by simp [i₀, i₁])
  obtain ⟨E, hEab, hEcard, W, hW0, hWQ, hWE⟩ := exists_stable_cube_m2_rot hc.nondegenerate hT hE
    hp hp2 h01 (tailBlock (n := 4) b c) (m2Proj_tailEmb i₀ i₁) (tailProj_m2Emb i₀ i₁)
    (minusPair K b c i₂).e_ne_zero (minusPair K b c i₂).Q_e
    (m2Proj_eq_zero_of_orth (minusPair_orth (by simp [i₀, i₂]))
      (minusPair_orth (by simp [i₁, i₂])))
    (by rw [tailBlock_m]; ext k; fin_cases k <;> simp [minusPair_e, i₂]) h1 h2 hTq hTp hTfix
    hdet hxp hx1
  exact exists_hyperGen_of_stable_cube hc hp hp2 hpK hEab hEcard hW0 hWQ hWE

end Model

section Residual

@[expose] def OSmallPrimeB3 (d : ValidLieTypeIndex) (p : ℕ) : Prop :=
  IsOrthogonalIndex d.1 ∧ ∃ q : PrimePower, d.1 = .B 3 q ∧ p ∣ q.card + 1

@[expose] def OrthHyperExSmallB3 : Prop := SeitzHyperLieEx fun d p _ => OSmallPrimeB3 d p

theorem orthHyperExSmall_of_B3 (h : OrthHyperExSmallB3) : OrthHyperExSmall := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, hO, q, hd, hq⟩
  rcases hd with hd | hd
  · exact h ⟨d, hv⟩ p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, hO, q, hd, hq⟩
  · subst hd
    have hfp : Fact p.Prime := ⟨hp⟩
    have hq' : p ≠ q.p := by simpa using hpd
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        4 q hv
    have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD 4 q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard := card_fixedField_eq_card ⟨.twistedD 4 q, hv⟩ (q := q) (by simp)
    have hpK : (p : ↥(ValidLieTypeIndex.fixedField ⟨.twistedD 4 q, hv⟩)) ≠ 0 :=
      CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp
        (by rw [hcard, PrimePower.card_def]; exact not_dvd_pow_of_ne hp q.prime_p hq')
    have hreg := regular_quadMinus (n := 4) le_rfl hirr
    have hEq := commutator_orthogonalGroup_quadMinus (n := 4) le_rfl hirr
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadMinus 4 _ b c) hEq hreg.1 e
    exact exists_hyperGen_minus_four hirr hπ hreg.2 hEq hp hp2 hpK (by rw [hcard]; exact hq)

end Residual

end CFSG.LieType.SeitzGeneration

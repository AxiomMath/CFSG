module

public import CFSG.LieType.SeitzGeneration.OrthB3Model
public import CFSG.LieType.SeitzGeneration.OrthRelRoot
public import CFSG.LieType.SeitzGeneration.OrthNonsplitCore
public import CFSG.LieType.SeitzGeneration.OrthHyperExSplit

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin OrthBlk
  CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

section Algebra

variable {K : Type} [Field K]

theorem sl2_mem_of_moves (h2 : (2 : K) ≠ 0) {x₀ : Matrix (Fin 2) (Fin 2) K}
    (hx₀ : x₀ 1 1 = -x₀ 0 0) (hc : x₀ 1 0 ≠ 0) (S : AddSubgroup (Matrix (Fin 2) (Fin 2) K))
    (h0 : ∀ c : K, c • x₀ ∈ S)
    (hup : ∀ Z ∈ S, ∀ μ : K, !![1, μ; 0, 1] * Z * !![1, -μ; 0, 1] - Z ∈ S)
    (hlo : ∀ Z ∈ S, ∀ μ : K, !![1, 0; μ, 1] * Z * !![1, 0; -μ, 1] - Z ∈ S)
    {Z : Matrix (Fin 2) (Fin 2) K} (hZ : Z 1 1 = -Z 0 0) : Z ∈ S := by
  have hE01 : ∀ ν : K, !![0, ν; 0, 0] ∈ S := fun ν => by
    have h := S.add_mem (hup _ (h0 (-ν / (2 * x₀ 1 0))) 1) (hup _ (h0 (-ν / (2 * x₀ 1 0))) (-1))
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.sub_apply,
        Matrix.add_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, hx₀] <;>
      field_simp <;> ring
  have hD : ∀ ν : K, !![ν, 0; 0, -ν] ∈ S := fun ν => by
    have h := S.add_mem (hup _ (h0 (ν / x₀ 1 0)) 1)
      (hE01 (ν / x₀ 1 0 * (2 * x₀ 0 0 + x₀ 1 0)))
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.sub_apply,
        Matrix.add_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, hx₀] <;>
      field_simp <;> ring
  have hE10 : ∀ ν : K, !![0, 0; ν, 0] ∈ S := fun ν => by
    have h := S.add_mem (hlo _ (hE01 (-ν)) 1) (hD (-ν))
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.add_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      ring
  have h := S.add_mem (S.add_mem (hD (Z 0 0)) (hE01 (Z 0 1))) (hE10 (Z 1 0))
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one,
      Fin.isValue, hZ] <;>
    ring

end Algebra

structure B3Reg (K : Type) [Field K] : Prop where
  nondeg : (polarBilin (quadOdd 3 K)).Nondegenerate
  ts : ∃ T : Submodule K (Fin 3 ⊕ Fin 3 ⊕ Unit → K), finrank K T = 3 ∧
    ∀ v ∈ T, quadOdd 3 K v = 0
  derived : orthDerived (quadOdd 3 K) = elementaryGroup (quadOdd 3 K)

namespace B3Data

variable {K : Type} [Field K] (X : B3Data K)

@[expose] def u (ε : K) : Fin 3 ⊕ Fin 3 ⊕ Unit → K := X.bv + (mB K).ι (ε • X.x₀)

theorem mB_m_u (ε : K) : (mB K).m (X.u ε) = ε • X.x₀ := by
  rw [u, map_add, X.mB_m_bv, (mB K).m_ι, zero_add]

theorem polar_u_ι (ε : K) (M : Matrix (Fin 2) (Fin 2) K) :
    polar (quadOdd 3 K) (X.u ε) ((mB K).ι M) = ε * polDet X.x₀ M := by
  rw [polar_mB, mB_m_u, polDet_smul_left]

theorem polDet_x₀_mul (Z : Matrix (Fin 2) (Fin 2) K) : polDet X.x₀ (Z * X.x₀) = X.c₂ * Z.trace := by
  rw [polDet_eq, X.trace_x₀, zero_mul, zero_sub, Matrix.trace_mul_comm X.x₀, Matrix.mul_assoc,
    X.x₀_mul_x₀, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  ring

theorem polar_u_ι_mul (ε : K) {Z : Matrix (Fin 2) (Fin 2) K} (hZ : Z.trace = 0) :
    polar (quadOdd 3 K) (X.u ε) ((mB K).ι (Z * X.x₀)) = 0 := by
  rw [polar_u_ι, polDet_x₀_mul, hZ, mul_zero, mul_zero]

theorem Q_u {ε : K} (hε : ε ^ 2 = 1) : quadOdd 3 K (X.u ε) = 0 := by
  rw [u, (mB K).Q_add _ _ X.mB_m_bv, X.Q_bv, mB_qM, Matrix.det_smul, Fintype.card_fin, X.det_x₀,
    hε, one_mul, neg_add_cancel]

theorem polar_u_u (ε ε' : K) :
    polar (quadOdd 3 K) (X.u ε) (X.u ε') = 2 * (ε * ε' - 1) * X.c₂ := by
  have h1 : polar (quadOdd 3 K) X.bv X.bv = -2 * X.c₂ := by rw [polar_self, X.Q_bv]; ring
  have h2 : polar (quadOdd 3 K) ((mB K).ι (ε • X.x₀)) ((mB K).ι (ε' • X.x₀)) =
      2 * (ε * ε') * X.c₂ := by
    rw [polar_mB, (mB K).m_ι, polDet_smul_left, polDet_comm, polDet_smul_left, polDet_self,
      X.det_x₀]
    ring
  rw [u, u, polar_add_left, polar_add_right, polar_add_right, h1, h2,
    polar_mB_of_m_eq_zero X.mB_m_bv, polar_mB_of_m_eq_zero' X.mB_m_bv]
  ring

theorem u_mem_U₂ (ε : K) : X.u ε ∈ perp (quadOdd 3 K) (Submodule.span K {zv K, X.v₂}) := by
  rw [mem_perp_span_pair, u, polar_add_right, polar_add_right, X.polar_zv_bv, X.polar_v₂_bv,
    polar_mB_of_m_eq_zero mB_m_zv, polar_mB_of_m_eq_zero X.mB_m_v₂]
  simp

theorem eq_of_mem_U₂ {w : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hw : w ∈ perp (quadOdd 3 K) (Submodule.span K {zv K, X.v₂})) :
    w = (mB K).ι ((mB K).m w) + w (Sum.inl 2) • X.bv := by
  obtain ⟨h1, h2⟩ := mem_perp_span_pair.mp hw
  rw [polar_q3] at h1 h2
  simp [zv, v₂, e₂, f₂] at h1 h2
  have hz : w (Sum.inr (Sum.inr ())) = 0 := h1.resolve_left X.two
  have hf : w (Sum.inr (Sum.inl 2)) = -X.c₂ * w (Sum.inl 2) := by
    rw [hz] at h2
    linear_combination h2
  funext k
  rcases k with i | i | ⟨⟩
  · fin_cases i <;> simp [mB_ι, m2Emb, oddPair_e, oddPair_f, mB_m, bv, e₂, f₂]
  · fin_cases i <;> simp [mB_ι, m2Emb, oddPair_e, oddPair_f, mB_m, bv, e₂, f₂, hf, mul_comm]
  · simp [mB_ι, m2Emb, oddPair_e, oddPair_f, bv, e₂, f₂, hz]

@[expose] def conjx₀ (t : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨(-X.c₂⁻¹) • (X.x₀ * (t : Matrix (Fin 2) (Fin 2) K) * X.x₀), by
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul, X.det_x₀,
      Matrix.SpecialLinearGroup.det_coe, mul_one]
    have hc := X.c₂_ne_zero
    field_simp⟩

theorem coe_conjx₀ (t : Matrix.SpecialLinearGroup (Fin 2) K) :
    (X.conjx₀ t : Matrix (Fin 2) (Fin 2) K) =
      (-X.c₂⁻¹) • (X.x₀ * (t : Matrix (Fin 2) (Fin 2) K) * X.x₀) := rfl

theorem x₀_mul_conjx₀ (t : Matrix.SpecialLinearGroup (Fin 2) K) :
    X.x₀ * (X.conjx₀ t : Matrix (Fin 2) (Fin 2) K) = (t : Matrix (Fin 2) (Fin 2) K) * X.x₀ := by
  rw [coe_conjx₀, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, X.x₀_mul_x₀,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul, neg_mul_neg,
    inv_mul_cancel₀ X.c₂_ne_zero, one_smul]

theorem x₀_mul_conjx₀_pow (t : Matrix.SpecialLinearGroup (Fin 2) K) (n : ℕ) :
    X.x₀ * (↑(X.conjx₀ t ^ n) : Matrix (Fin 2) (Fin 2) K) =
      (↑(t ^ n) : Matrix (Fin 2) (Fin 2) K) * X.x₀ := by
  induction n with
  | zero => simp only [pow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, Matrix.one_mul]
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
      x₀_mul_conjx₀, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, ← pow_succ]

theorem inv_x₀_mul_x₀ : ((-X.c₂⁻¹) • X.x₀) * X.x₀ = 1 := by
  rw [Matrix.smul_mul, X.x₀_mul_x₀, smul_smul, neg_mul_neg, inv_mul_cancel₀ X.c₂_ne_zero, one_smul]

theorem conjx₀_pow_eq_one {t : Matrix.SpecialLinearGroup (Fin 2) K} {n : ℕ} (ht : t ^ n = 1) :
    X.conjx₀ t ^ n = 1 := by
  have h2 := X.x₀_mul_conjx₀_pow t n
  rw [ht, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] at h2
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_one]
  calc (↑(X.conjx₀ t ^ n) : Matrix (Fin 2) (Fin 2) K) =
        ((-X.c₂⁻¹) • X.x₀) * X.x₀ * ↑(X.conjx₀ t ^ n) := by rw [X.inv_x₀_mul_x₀, Matrix.one_mul]
    _ = 1 := by rw [Matrix.mul_assoc, h2, X.inv_x₀_mul_x₀]

theorem x₀_mul_conjx₀_inv (t : Matrix.SpecialLinearGroup (Fin 2) K) :
    X.x₀ * (↑(X.conjx₀ t)⁻¹ : Matrix (Fin 2) (Fin 2) K) =
      (↑t⁻¹ : Matrix (Fin 2) (Fin 2) K) * X.x₀ := by
  calc X.x₀ * (↑(X.conjx₀ t)⁻¹ : Matrix (Fin 2) (Fin 2) K) =
        (↑t⁻¹ : Matrix (Fin 2) (Fin 2) K) * ↑t * X.x₀ * ↑(X.conjx₀ t)⁻¹ := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
          Matrix.one_mul]
    _ = (↑t⁻¹ : Matrix (Fin 2) (Fin 2) K) * (X.x₀ * ↑(X.conjx₀ t)) * ↑(X.conjx₀ t)⁻¹ := by
        rw [X.x₀_mul_conjx₀, Matrix.mul_assoc (↑t⁻¹ : Matrix (Fin 2) (Fin 2) K)]
    _ = (↑t⁻¹ : Matrix (Fin 2) (Fin 2) K) * X.x₀ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

omit X in
theorem trace_conj_sub (t : Matrix.SpecialLinearGroup (Fin 2) K) (Z : Matrix (Fin 2) (Fin 2) K) :
    ((t : Matrix (Fin 2) (Fin 2) K) * Z * (↑t⁻¹ : Matrix (Fin 2) (Fin 2) K) - Z).trace = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, sub_self]

@[expose] def conjσ : elementaryGroup (quadOdd 3 K) ≃* elementaryGroup (quadOdd 3 K) where
  toFun g := ⟨X.σ * g * X.σ⁻¹, conj_mem_elementaryGroup X.σ_mem g.2⟩
  invFun g := ⟨X.σ⁻¹ * g * X.σ, by
    simpa using conj_mem_elementaryGroup (inv_mem X.σ_mem) g.2⟩
  left_inv g := Subtype.ext (by
    change X.σ⁻¹ * (X.σ * g.1 * X.σ⁻¹) * X.σ = g.1
    group)
  right_inv g := Subtype.ext (by
    change X.σ * (X.σ⁻¹ * g.1 * X.σ) * X.σ⁻¹ = g.1
    group)
  map_mul' g h := Subtype.ext (by
    change X.σ * (g.1 * h.1) * X.σ⁻¹ = X.σ * g.1 * X.σ⁻¹ * (X.σ * h.1 * X.σ⁻¹)
    group)

theorem coe_conjσ (g : elementaryGroup (quadOdd 3 K)) :
    (X.conjσ g : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) =
      X.σ * g * X.σ⁻¹ := rfl

theorem conjσ_conjσ (g : elementaryGroup (quadOdd 3 K)) : X.conjσ (X.conjσ g) = g := by
  refine Subtype.ext ?_
  rw [coe_conjσ, coe_conjσ, X.σ_inv]
  calc X.σ * (X.σ * g.1 * X.σ) * X.σ = (X.σ * X.σ) * g.1 * (X.σ * X.σ) := by group
    _ = g := by rw [X.σ_mul_σ, one_mul, mul_one]

theorem σ_σ (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) : X.σ (X.σ v) = v := by
  rw [← LinearEquiv.mul_apply, X.σ_mul_σ]
  rfl

theorem σ_g₀_σ : X.σ * X.g₀ * X.σ⁻¹ = X.g₂ := by rw [X.sigma_mul_g₀, mul_inv_cancel_right]

theorem σ_g₁_σ : X.σ * X.g₁ * X.σ⁻¹ = X.g₁ := by rw [X.sigma_mul_g₁, mul_inv_cancel_right]

theorem σ_g₂_σ : X.σ * X.g₂ * X.σ⁻¹ = X.g₀ := by
  rw [← X.σ_g₀_σ, X.σ_inv]
  calc X.σ * (X.σ * X.g₀ * X.σ) * X.σ = (X.σ * X.σ) * X.g₀ * (X.σ * X.σ) := by group
    _ = X.g₀ := by rw [X.σ_mul_σ, one_mul, mul_one]

theorem σ_mem_U₂ {e : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (he : e ∈ perp (quadOdd 3 K) (Submodule.span K {(mB K).ι 1, (mB K).ι X.x})) :
    X.σ e ∈ perp (quadOdd 3 K) (Submodule.span K {zv K, X.v₂}) := by
  obtain ⟨h1, h2⟩ := mem_perp_span_pair.mp he
  refine mem_perp_span_pair.mpr ⟨?_, ?_⟩
  · rw [← X.σ_ι_one, polar_map_of_mem X.σ_mem, h1]
  · rw [← X.σ_ι_x, polar_map_of_mem X.σ_mem, h2]

end B3Data

structure B3Cube {K : Type} [Field K] (X : B3Data K) where
  E : Subgroup (elementaryGroup (quadOdd 3 K))
  elem : IsElemAbelian X.p E
  card : Nat.card E = X.p ^ 3
  L : elementaryGroup (quadOdd 3 K)
  R : elementaryGroup (quadOdd 3 K)
  G : elementaryGroup (quadOdd 3 K)
  coe_L : (L : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) =
    (B3Data.mB K).sand (X.x, 1)
  coe_R : (R : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) =
    (B3Data.mB K).sand (1, X.x)
  coe_G : (G : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) = X.g₂
  mem_L : L ∈ E
  mem_R : R ∈ E
  mem_G : G ∈ E
  form : ∀ g ∈ E, ∃ i j k : ℤ, g = L ^ i * R ^ j * G ^ k

theorem ringChar_prime {K : Type} [Field K] [Finite K] : (ringChar K).Prime :=
  CharP.prime_ringChar K

theorem ringChar_ne_two {K : Type} [Field K] (h2 : (2 : K) ≠ 0) : ringChar K ≠ 2 := by
  intro h
  apply h2
  have := ringChar.Nat.cast_ringChar (R := K)
  rw [h] at this
  exact_mod_cast this

namespace B3Data

variable {K : Type} [Field K]

theorem sand_pow_p_eq_one {a b : Matrix.SpecialLinearGroup (Fin 2) K} {n : ℕ} (ha : a ^ n = 1)
    (hb : b ^ n = 1) : (mB K).sand (a, b) ^ n = 1 := by
  rw [← map_pow]
  change (mB K).sand (a ^ n, b ^ n) = 1
  rw [ha, hb]
  exact map_one _

variable [Finite K] (X : B3Data K)

omit X in
theorem sand_mem_elementaryGroup (hR : B3Reg K) {n : ℕ} (hn : n.Prime) (hn2 : n ≠ 2)
    {a b : Matrix.SpecialLinearGroup (Fin 2) K} (ha : a ^ n = 1) (hb : b ^ n = 1) :
    (mB K).sand (a, b) ∈ elementaryGroup (quadOdd 3 K) :=
  mem_elementaryGroup_of_odd_pow hR.nondeg hR.ts hR.derived hn hn2 (sand_mem _)
    (sand_pow_p_eq_one ha hb)

theorem nonempty_cube (hR : B3Reg K) : Nonempty (B3Cube X) := by
  have hL := sand_mem_elementaryGroup hR X.hp X.hp2 (b := 1) X.hxp (one_pow _)
  have hR' := sand_mem_elementaryGroup hR X.hp X.hp2 (a := 1) (one_pow _) X.hxp
  have hG : X.g₂ ∈ elementaryGroup (quadOdd 3 K) :=
    mem_elementaryGroup_of_odd_pow hR.nondeg hR.ts hR.derived X.hp X.hp2 X.g₂_mem X.g₂_pow
  let L : elementaryGroup (quadOdd 3 K) := ⟨_, hL⟩
  let R : elementaryGroup (quadOdd 3 K) := ⟨_, hR'⟩
  let G : elementaryGroup (quadOdd 3 K) := ⟨_, hG⟩
  have cLR : Commute L R := Subtype.ext (by
    change (mB K).sand (X.x, 1) * (mB K).sand (1, X.x) = (mB K).sand (1, X.x) * (mB K).sand (X.x, 1)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simp) (by simp))
  have cLG : Commute L G := Subtype.ext (X.sand_commute_g₂ _).eq
  have cRG : Commute R G := Subtype.ext (X.sand_commute_g₂ _).eq
  have hLp : L ^ X.p = 1 := Subtype.ext (sand_pow_p_eq_one X.hxp (one_pow _))
  have hRp : R ^ X.p = 1 := Subtype.ext (sand_pow_p_eq_one (one_pow _) X.hxp)
  have hGp : G ^ X.p = 1 := Subtype.ext X.g₂_pow
  obtain ⟨E, hEab, hEc, hform, hLE, hRE, hGE⟩ := exists_cube_of_three X.hp cLR cLG cRG hLp hRp hGp
    fun i j k h => X.indep_L_R_g₂ (by
      have := congrArg Subtype.val h
      simpa only [Subgroup.coe_mul, Subgroup.coe_zpow, OneMemClass.coe_one] using this)
  exact ⟨⟨E, hEab, hEc, L, R, G, rfl, rfl, rfl, hLE, hRE, hGE, hform⟩⟩

end B3Data

namespace B3Cube

open B3Data

variable {K : Type} [Field K] {X : B3Data K} (C : B3Cube X)

@[expose] def hcl : Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) :=
  (hyperClosure X.p ⊤ C.E).map (elementaryGroup (quadOdd 3 K)).subtype

theorem hcl_le : C.hcl ≤ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) := by
  rintro _ ⟨x, -, rfl⟩
  exact elementaryGroup_le_orthogonalGroup _ x.2

theorem mem_hcl {a b : elementaryGroup (quadOdd 3 K)} (ha : a ∈ C.E) (hb : b ∈ C.E)
    (hind : ∀ i j : ℤ,
      (a : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) ^ i *
        (b : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) ^ j = 1 →
      (X.p : ℤ) ∣ i ∧ (X.p : ℤ) ∣ j)
    {k : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hk : k ∈ elementaryGroup (quadOdd 3 K)) (hka : Commute k a) (hkb : Commute k b) :
    k ∈ C.hcl := by
  have hab : Commute a b := congrArg Subtype.val (C.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hk' : (⟨k, hk⟩ : elementaryGroup (quadOdd 3 K)) ∈ hyperClosure X.p ⊤ C.E :=
    mem_hyperClosure_of_commute X.hp C.card ha hb hab (C.elem.2 a ha) (C.elem.2 b hb)
      (fun i j h => hind i j (by
        have := congrArg Subtype.val h
        simpa only [Subgroup.coe_mul, Subgroup.coe_zpow, OneMemClass.coe_one] using this))
      (Subtype.ext hka.eq) (Subtype.ext hkb.eq)
  exact ⟨⟨k, hk⟩, hk', rfl⟩

@[expose] def G₁ : elementaryGroup (quadOdd 3 K) := C.L ^ X.m * C.R ^ X.m

theorem coe_G₁ : (C.G₁ : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) = X.g₁ := by
  rw [G₁, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, C.coe_L, C.coe_R, ← map_pow,
    ← map_pow, ← map_mul, B3Data.g₁]
  congr 1
  exact Prod.ext (by simp [B3Data.y]) (by simp [B3Data.y])

theorem mem_G₁ : C.G₁ ∈ C.E := C.E.mul_mem (C.E.pow_mem C.mem_L _) (C.E.pow_mem C.mem_R _)

theorem eichler_u_one_mem (ε c : K) :
    eichler (quadOdd 3 K) (X.u ε) (c • (mB K).ι 1) ∈ C.hcl := by
  have hu1 : X.g₁ (X.u ε) = X.u ε := by
    rw [B3Data.u, map_add, X.g₁_fix X.mB_m_bv, X.g₁_ι_x₀]
  have hu2 : X.g₂ (X.u ε) = X.u ε := by
    rw [B3Data.u, map_add, X.g₂_fix X.C₂_m_bv, X.g₂_fix (X.C₂_m_mB_ι _)]
  have hw1 : X.g₁ (c • (mB K).ι 1) = c • (mB K).ι 1 := by rw [map_smul, X.g₁_ι_one]
  have hw2 : X.g₂ (c • (mB K).ι 1) = c • (mB K).ι 1 := by
    rw [map_smul, X.g₂_fix (X.C₂_m_mB_ι _)]
  refine C.mem_hcl C.mem_G₁ C.mem_G (fun i j h => X.indep_g₁_g₂ (by rwa [C.coe_G₁, C.coe_G] at h))
    (eichler_mem_elementaryGroup _ _ _) ?_ ?_
  · rw [C.coe_G₁]
    exact (commute_eichler_of_fix X.g₁_mem hu1 hw1).symm
  · rw [C.coe_G]
    exact (commute_eichler_of_fix X.g₂_mem hu2 hw2).symm

variable [Finite K]

theorem sand_left_mem (hR : B3Reg K) {t : Matrix.SpecialLinearGroup (Fin 2) K}
    (ht : t ^ ringChar K = 1) : (mB K).sand (t, 1) ∈ C.hcl := by
  refine C.mem_hcl C.mem_R C.mem_G (fun i j h => X.indep_R_g₂ (by rwa [C.coe_R, C.coe_G] at h))
    (sand_mem_elementaryGroup hR ringChar_prime (ringChar_ne_two X.two) ht (one_pow _)) ?_ ?_
  · rw [C.coe_R]
    change (mB K).sand (t, 1) * (mB K).sand (1, X.x) = (mB K).sand (1, X.x) * (mB K).sand (t, 1)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simp) (by simp)
  · rw [C.coe_G]
    exact X.sand_commute_g₂ _

theorem sand_right_mem (hR : B3Reg K) {t : Matrix.SpecialLinearGroup (Fin 2) K}
    (ht : t ^ ringChar K = 1) : (mB K).sand (1, t) ∈ C.hcl := by
  refine C.mem_hcl C.mem_L C.mem_G (fun i j h => X.indep_L_g₂ (by rwa [C.coe_L, C.coe_G] at h))
    (sand_mem_elementaryGroup hR ringChar_prime (ringChar_ne_two X.two) (one_pow _) ht) ?_ ?_
  · rw [C.coe_L]
    change (mB K).sand (1, t) * (mB K).sand (X.x, 1) = (mB K).sand (X.x, 1) * (mB K).sand (1, t)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (by simp) (by simp)
  · rw [C.coe_G]
    exact X.sand_commute_g₂ _

theorem move_mem (hR : B3Reg K) {ε : K} {t : Matrix.SpecialLinearGroup (Fin 2) K}
    (ht : t ^ ringChar K = 1)
    {Z : Matrix (Fin 2) (Fin 2) K} (hZ : Z.trace = 0)
    (hmem : eichler (quadOdd 3 K) (X.u ε) ((mB K).ι (Z * X.x₀)) ∈ C.hcl) :
    eichler (quadOdd 3 K) (X.u ε) ((mB K).ι (((t : Matrix (Fin 2) (Fin 2) K) * Z *
      (↑t⁻¹ : Matrix (Fin 2) (Fin 2) K) - Z) * X.x₀)) ∈ C.hcl := by
  have hs : X.conjx₀ t ^ ringChar K = 1 := X.conjx₀_pow_eq_one ht
  have hH : (mB K).sand (t, X.conjx₀ t) ∈ C.hcl := by
    have h : (mB K).sand (t, X.conjx₀ t) = (mB K).sand (t, 1) * (mB K).sand (1, X.conjx₀ t) := by
      rw [← map_mul]
      congr 1
      exact Prod.ext (mul_one t).symm (one_mul _).symm
    rw [h]
    exact C.hcl.mul_mem (C.sand_left_mem hR ht) (C.sand_right_mem hR hs)
  have hu : (mB K).sand (t, X.conjx₀ t) (X.u ε) = X.u ε := by
    rw [B3Data.u, map_add, (mB K).sand_of_m_eq_zero _ X.mB_m_bv, (mB K).sand_ι]
    congr 2
    dsimp only
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, X.x₀_mul_conjx₀_inv, ← Matrix.mul_assoc,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mul]
  have hcomm := commutatorElement_eichler (sand_mem (t, X.conjx₀ t)) hu (X.polar_u_ι_mul ε hZ)
  have hv : (mB K).sand (t, X.conjx₀ t) ((mB K).ι (Z * X.x₀)) - (mB K).ι (Z * X.x₀) =
      (mB K).ι (((t : Matrix (Fin 2) (Fin 2) K) * Z * (↑t⁻¹ : Matrix (Fin 2) (Fin 2) K) - Z) *
        X.x₀) := by
    rw [(mB K).sand_ι, ← map_sub]
    congr 1
    dsimp only
    rw [Matrix.sub_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [X.x₀_mul_conjx₀_inv]
  rw [← hv, ← hcomm, commutatorElement_def]
  exact C.hcl.mul_mem (C.hcl.mul_mem (C.hcl.mul_mem hH hmem) (C.hcl.inv_mem hH))
    (C.hcl.inv_mem hmem)

theorem eichler_u_mem (hR : B3Reg K) (ε : K) {Z : Matrix (Fin 2) (Fin 2) K}
    (hZ : Z.trace = 0) : eichler (quadOdd 3 K) (X.u ε) ((mB K).ι (Z * X.x₀)) ∈ C.hcl := by
  let S : AddSubgroup (Matrix (Fin 2) (Fin 2) K) :=
    { carrier := {Z | Z.trace = 0 ∧ eichler (quadOdd 3 K) (X.u ε) ((mB K).ι (Z * X.x₀)) ∈ C.hcl}
      add_mem' := fun {a b} ha hb => ⟨by rw [Matrix.trace_add, ha.1, hb.1, add_zero], by
        rw [Matrix.add_mul, map_add,
          ← eichler_mul (X.polar_u_ι_mul ε ha.1) (X.polar_u_ι_mul ε hb.1)]
        exact C.hcl.mul_mem ha.2 hb.2⟩
      zero_mem' := ⟨Matrix.trace_zero _ _, by
        rw [Matrix.zero_mul, map_zero, eichler_zero_right]
        exact C.hcl.one_mem⟩
      neg_mem' := fun {a} ha => ⟨by rw [Matrix.trace_neg, ha.1, neg_zero], by
        rw [Matrix.neg_mul, map_neg, ← eichler_inv (X.polar_u_ι_mul ε ha.1)]
        exact C.hcl.inv_mem ha.2⟩ }
  have h0 : ∀ c : K, c • X.x₀ ∈ S := fun c => ⟨by rw [Matrix.trace_smul, X.trace_x₀, smul_zero], by
    rw [Matrix.smul_mul, X.x₀_mul_x₀, smul_smul, map_smul]
    exact C.eichler_u_one_mem ε _⟩
  have hup : ∀ Z ∈ S, ∀ μ : K, !![1, μ; 0, 1] * Z * !![1, -μ; 0, 1] - Z ∈ S := fun Z hZ μ => by
    have h1 := C.move_mem hR (upT_pow_ringChar μ) hZ.1 hZ.2
    have h2 := trace_conj_sub (upT μ) Z
    rw [coe_upT, coe_upT_inv] at h1 h2
    exact ⟨h2, h1⟩
  have hlo : ∀ Z ∈ S, ∀ μ : K, !![1, 0; μ, 1] * Z * !![1, 0; -μ, 1] - Z ∈ S := fun Z hZ μ => by
    have h1 := C.move_mem hR (loT_pow_ringChar μ) hZ.1 hZ.2
    have h2 := trace_conj_sub (loT μ) Z
    rw [coe_loT, coe_loT_inv] at h1 h2
    exact ⟨h2, h1⟩
  have hZ' : Z 1 1 = -Z 0 0 := by
    rw [Matrix.trace_fin_two] at hZ
    linear_combination hZ
  exact (sl2_mem_of_moves X.two X.x₀_11 (by rw [X.x₀_10]; exact X.x10_ne_zero) S h0 hup hlo
    hZ').2

theorem eichler_u_mem_of_perp (hR : B3Reg K) {ε : K} (hε : ε ^ 2 = 1)
    {w : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hw : w ∈ perp (quadOdd 3 K) (Submodule.span K {zv K, X.v₂}))
    (hpw : polar (quadOdd 3 K) (X.u ε) w = 0) : eichler (quadOdd 3 K) (X.u ε) w ∈ C.hcl := by
  have hε0 : ε ≠ 0 := by
    rintro rfl
    norm_num at hε
  have hdec := X.eq_of_mem_U₂ hw
  set M' := (mB K).m w - w (Sum.inl 2) • (ε • X.x₀) with hM'
  have hw' : w = (mB K).ι M' + w (Sum.inl 2) • X.u ε := by
    conv_lhs => rw [hdec]
    rw [hM', B3Data.u, map_sub, map_smul, smul_add]
    abel
  have hQu := X.Q_u hε
  have hpol : polar (quadOdd 3 K) (X.u ε) ((mB K).ι M') = 0 := by
    rw [hw', polar_add_right, polar_smul_right, polar_self, hQu] at hpw
    simpa using hpw
  have htr : (X.x₀ * M').trace = 0 := by
    rw [X.polar_u_ι, polDet_eq, X.trace_x₀, zero_mul, zero_sub] at hpol
    have := (mul_eq_zero.mp hpol).resolve_left hε0
    exact neg_eq_zero.mp this
  set Z := (-X.c₂⁻¹) • (M' * X.x₀) with hZdef
  have hZx : Z * X.x₀ = M' := by
    rw [hZdef, Matrix.smul_mul, Matrix.mul_assoc, X.x₀_mul_x₀, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, neg_mul_neg, inv_mul_cancel₀ X.c₂_ne_zero, one_smul]
  have hZtr : Z.trace = 0 := by
    rw [hZdef, Matrix.trace_smul, Matrix.trace_mul_comm, htr, smul_zero]
  rw [hw', eichler_add_smul_self hQu, ← hZx]
  exact C.eichler_u_mem hR ε hZtr

omit [Finite K] in
theorem polarNondegOn_U₂ (hR : B3Reg K) :
    PolarNondegOn (quadOdd 3 K) (perp (quadOdd 3 K) (Submodule.span K {zv K, X.v₂})) :=
  polarNondegOn_perp hR.nondeg (polarNondegOn_span_pair Q_zv X.Q_v₂ X.polar_zv_v₂
    X.four_sub_ne_zero)

theorem eichler_mem_U₂ (hR : B3Reg K) :
    ∀ e ∈ perp (quadOdd 3 K) (Submodule.span K {zv K, X.v₂}),
      ∀ w ∈ perp (quadOdd 3 K) (Submodule.span K {zv K, X.v₂}),
        eichler (quadOdd 3 K) e w ∈ C.hcl := by
  have hpol : polar (quadOdd 3 K) (X.u 1) (X.u (-1)) ≠ 0 := by
    rw [X.polar_u_u, show (1 : K) * -1 - 1 = -2 by ring]
    exact mul_ne_zero (mul_ne_zero X.two (neg_ne_zero.mpr X.two)) X.c₂_ne_zero
  exact eichler_mem_of_relRoot C.hcl_le (polarNondegOn_U₂ (X := X) hR) (X.u_mem_U₂ 1)
    (X.u_mem_U₂ (-1))
    (X.Q_u (by norm_num)) (X.Q_u (by norm_num)) hpol
    (fun w hw hpw => C.eichler_u_mem_of_perp hR (by norm_num) hw hpw)
    (fun w hw hpw => C.eichler_u_mem_of_perp hR (by norm_num) hw hpw)

omit [Finite K] in
theorem conjσ_L : X.conjσ C.L = C.G * C.G₁ := by
  refine Subtype.ext ?_
  rw [coe_conjσ, Subgroup.coe_mul, C.coe_L, C.coe_G, C.coe_G₁, ← X.g₀_mul_g₁]
  calc X.σ * (X.g₀ * X.g₁) * X.σ⁻¹ = (X.σ * X.g₀ * X.σ⁻¹) * (X.σ * X.g₁ * X.σ⁻¹) := by group
    _ = X.g₂ * X.g₁ := by rw [X.σ_g₀_σ, X.σ_g₁_σ]

omit [Finite K] in
theorem conjσ_R : X.conjσ C.R = C.G⁻¹ * C.G₁ := by
  refine Subtype.ext ?_
  rw [coe_conjσ, Subgroup.coe_mul, Subgroup.coe_inv, C.coe_R, C.coe_G, C.coe_G₁,
    ← X.g₀_inv_mul_g₁]
  calc X.σ * (X.g₀⁻¹ * X.g₁) * X.σ⁻¹ = (X.σ * X.g₀ * X.σ⁻¹)⁻¹ * (X.σ * X.g₁ * X.σ⁻¹) := by
        group
    _ = X.g₂⁻¹ * X.g₁ := by rw [X.σ_g₀_σ, X.σ_g₁_σ]

omit [Finite K] in
theorem conjσ_G : X.conjσ C.G = C.G₁ * C.R⁻¹ := by
  refine Subtype.ext ?_
  rw [coe_conjσ, Subgroup.coe_mul, Subgroup.coe_inv, C.coe_G, C.coe_G₁, C.coe_R, X.σ_g₂_σ,
    ← X.g₀_inv_mul_g₁]
  group

omit [Finite K] in
theorem conjσ_mem {g : elementaryGroup (quadOdd 3 K)} (hg : g ∈ C.E) : X.conjσ g ∈ C.E := by
  obtain ⟨i, j, k, rfl⟩ := C.form g hg
  rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow, C.conjσ_L, C.conjσ_R, C.conjσ_G]
  exact C.E.mul_mem (C.E.mul_mem (C.E.zpow_mem (C.E.mul_mem C.mem_G C.mem_G₁) i)
    (C.E.zpow_mem (C.E.mul_mem (C.E.inv_mem C.mem_G) C.mem_G₁) j))
    (C.E.zpow_mem (C.E.mul_mem C.mem_G₁ (C.E.inv_mem C.mem_R)) k)

omit [Finite K] in
theorem map_conjσ : C.E.map X.conjσ.toMonoidHom = C.E := by
  refine le_antisymm ?_ fun g hg => ⟨X.conjσ g, C.conjσ_mem hg, X.conjσ_conjσ g⟩
  rintro _ ⟨g, hg, rfl⟩
  exact C.conjσ_mem hg

omit [Finite K] in
theorem conj_mem_hcl {k : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hk : k ∈ C.hcl) : X.σ * k * X.σ⁻¹ ∈ C.hcl := by
  obtain ⟨k', hk', rfl⟩ := hk
  exact ⟨X.conjσ k', map_hyperClosure_le_of_normalizes X.conjσ C.map_conjσ ⟨k', hk', rfl⟩, rfl⟩

theorem eichler_mem_U₀ (hR : B3Reg K) :
    ∀ e ∈ perp (quadOdd 3 K) (Submodule.span K {(mB K).ι 1, (mB K).ι X.x}),
      ∀ w ∈ perp (quadOdd 3 K) (Submodule.span K {(mB K).ι 1, (mB K).ι X.x}),
        eichler (quadOdd 3 K) e w ∈ C.hcl := by
  intro e he w hw
  have h := C.conj_mem_hcl (C.eichler_mem_U₂ hR _ (X.σ_mem_U₂ he) _ (X.σ_mem_U₂ hw))
  rwa [eichler_conj X.σ_mem, X.σ_σ, X.σ_σ] at h

omit [Finite K] in
theorem finrank_span_pair_le {V : Type} [AddCommGroup V] [Module K V] (a b : V) :
    finrank K (Submodule.span K {a, b}) ≤ 2 := by
  classical
  have h := finrank_span_finset_le_card (R := K) ({a, b} : Finset V)
  rw [Set.finrank, Finset.coe_insert, Finset.coe_singleton] at h
  exact h.trans Finset.card_le_two

theorem elementaryGroup_le_hcl (hR : B3Reg K) : elementaryGroup (quadOdd 3 K) ≤ C.hcl := by
  have hreg₀ : PolarNondegOn (quadOdd 3 K) (Submodule.span K {(mB K).ι 1, (mB K).ι X.x}) :=
    polarNondegOn_span_pair Q_ι_one X.Q_ι_x X.polar_ι_one_x X.four_sub_ne_zero
  have hreg₂ : PolarNondegOn (quadOdd 3 K) (Submodule.span K {zv K, X.v₂}) :=
    polarNondegOn_span_pair Q_zv X.Q_v₂ X.polar_zv_v₂ X.four_sub_ne_zero
  have hN₀U₂ : Submodule.span K {(mB K).ι 1, (mB K).ι X.x} ≤
      perp (quadOdd 3 K) (Submodule.span K {zv K, X.v₂}) := by
    rw [Submodule.span_le]
    rintro v (rfl | rfl)
    · exact mem_perp_span_pair.mpr
        ⟨polar_mB_of_m_eq_zero mB_m_zv _, polar_mB_of_m_eq_zero X.mB_m_v₂ _⟩
    · exact mem_perp_span_pair.mpr
        ⟨polar_mB_of_m_eq_zero mB_m_zv _, polar_mB_of_m_eq_zero X.mB_m_v₂ _⟩
  have hsep : OrthSep (quadOdd 3 K) (Submodule.span K {(mB K).ι 1, (mB K).ι X.x})
      (Submodule.span K {zv K, X.v₂}) := fun s hs t ht => by
    rw [polar_comm]
    exact mem_perp.mp (hN₀U₂ hs) t ht
  have hsup := polarNondegOn_sup hreg₀ hreg₂ hsep
  have hdim : 3 ≤ finrank K (perp (quadOdd 3 K) (Submodule.span K {(mB K).ι 1, (mB K).ι X.x} ⊔
      Submodule.span K {zv K, X.v₂})) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp hsup)
    have h2 := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span K {(mB K).ι 1, (mB K).ι X.x}) (Submodule.span K {zv K, X.v₂})
    have h3 := finrank_span_pair_le (K := K) ((mB K).ι 1) ((mB K).ι X.x)
    have h4 := finrank_span_pair_le (K := K) (zv K) X.v₂
    have h7 : finrank K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 7 := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
    omega
  obtain ⟨P, hPe, hPf⟩ := exists_hypPair_in (polarNondegOn_perp hR.nondeg hsup) hdim
  have hW₂ := LinearMap.BilinForm.orthogonal_le (B := polarBilin (quadOdd 3 K))
    (le_sup_right : Submodule.span K {zv K, X.v₂} ≤
      Submodule.span K {(mB K).ι 1, (mB K).ι X.x} ⊔ Submodule.span K {zv K, X.v₂})
  have hW₀ := LinearMap.BilinForm.orthogonal_le (B := polarBilin (quadOdd 3 K))
    (le_sup_left : Submodule.span K {(mB K).ι 1, (mB K).ι X.x} ≤
      Submodule.span K {(mB K).ι 1, (mB K).ι X.x} ⊔ Submodule.span K {zv K, X.v₂})
  refine elementaryGroup_le_of_two C.hcl_le hR.nondeg (polarNondegOn_U₂ (X := X) hR) ?_
    (C.eichler_mem_U₂ hR) (C.eichler_mem_U₀ hR) P ⟨hW₂ hPe, hW₀ hPe⟩ ⟨hW₂ hPf, hW₀ hPf⟩
  intro v hv
  rw [mem_perp] at hv ⊢
  exact fun s hs => hv s (hN₀U₂ hs)

theorem hyperClosure_eq_top (hR : B3Reg K) : hyperClosure X.p ⊤ C.E = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨y, hy, hyg⟩ := C.elementaryGroup_le_hcl hR g.2
  rwa [show g = y from Subtype.ext hyg.symm]

end B3Cube

theorem exists_hyperGen_B3 {d : TauCeti.ValidLieTypeIndex} {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) {π : elementaryGroup (quadOdd 3 K) →* Cat d}
    (hc : IsOrthogonalCover (quadOdd 3 K) π) (hR : B3Reg K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) (hpq : p ∣ Nat.card K + 1) :
    ∃ E' : Subgroup (Cat d), IsElemAbelian p E' ∧ Nat.card E' = p ^ 3 ∧
      HyperGen p (⊤ : Subgroup (Cat d)) E' := by
  obtain ⟨x, hdet, hxp, hx1⟩ := exists_sl2_order hp (dvd_sq_sub_one_of_dvd_add_one hpq)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro h1
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq h1
    have hq : 1 ≤ Nat.card K := Finite.card_pos
    have h4 : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [h4] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  let x' : Matrix.SpecialLinearGroup (Fin 2) K := ⟨x, hdet⟩
  let X : B3Data K :=
    { x := x'
      p := p
      hp := hp
      hp2 := hp2
      hxp := Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
        exact hxp)
      hx1 := fun h => hx1 (by
        have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
          (g : Matrix (Fin 2) (Fin 2) K)) h
        simpa using this)
      two := h2
      ell := trace_sq_ne_zero hp hpK hpq1 hdet hxp hx1 }
  obtain ⟨C⟩ := X.nonempty_cube hR
  exact exists_hyperGen_of_hyperClosure_eq_top hc.surjective hp
    (not_dvd_card_ker_of_scalar hc hp hp2)
    C.elem C.card (C.hyperClosure_eq_top hR)

end CFSG.LieType.SeitzGeneration

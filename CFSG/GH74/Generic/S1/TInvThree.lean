module

public import CFSG.GH74.Generic.S1.RA4Facts
public import CFSG.GH74.L5U5.ModelsPairsUnitary

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.Assembly.LowTwoRank Module Matrix
open scoped MatrixGroups

section Lin3

variable {F : Type*} [Field F]

theorem rinv3_dim_two (h2 : (2 : F) ≠ 0) (t : Matrix (Fin 3) (Fin 3) F) (ht : t * t = 1)
    (hdet : t.det = 1) (h1 : t ≠ 1) :
    finrank F (LinearMap.ker (Matrix.toLin' t + LinearMap.id)) = 2 := by
  classical
  let f := Matrix.toLin' t
  have hf : ∀ v, f (f v) = v := rinv_toLin_involutive t ht
  have hsum := involution_finrank_add h2 f hf
  have h3 : finrank F (Fin 3 → F) = 3 := by simp
  have hdet' := involution_det h2 t ht
  rw [hdet] at hdet'
  have hneg : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    have : (2 : F) = 1 - -1 := by norm_num
    rw [this, h]; simp
  have hev : Even (finrank F (LinearMap.ker (f + LinearMap.id))) := by
    rw [← neg_one_pow_eq_one_iff_even hneg]
    exact hdet'.symm
  set a := finrank F (LinearMap.ker (f + LinearMap.id)) with ha
  set b := finrank F (LinearMap.ker (f - LinearMap.id)) with hb
  have hab : a + b = 3 := by rw [hsum, h3]
  obtain ⟨m, hm⟩ := hev
  have hcases : a = 0 ∨ a = 2 := by omega
  rcases hcases with h0 | h2'
  · exfalso
    have hb3 : b = 3 := by omega
    have htop : LinearMap.ker (f - LinearMap.id) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [← hb, hb3, h3])
    apply h1
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker (f - LinearMap.id) := by rw [htop]; trivial
    have : f v - v = 0 := by simpa using hv
    show f v = (Matrix.toLin' (1 : Matrix (Fin 3) (Fin 3) F)) v
    rw [Matrix.toLin'_apply (1 : Matrix (Fin 3) (Fin 3) F), Matrix.one_mulVec]
    exact sub_eq_zero.1 this
  · exact h2'

theorem rinvSign_three_two : rinvSign F 3 2 = ![-1, -1, 1] := by
  funext j
  fin_cases j <;> simp [rinvSign]

theorem rinv_det_diagonal_sign3 : (Matrix.diagonal (rinvSign F 3 2)).det = 1 := by
  rw [rinvSign_three_two]
  simp [Matrix.det_diagonal, Fin.prod_univ_three]

@[expose] def rinvFirst3 (d : F) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.diagonal fun i => if i = 0 then d else 1

theorem rinv3_det_first (d : F) : (rinvFirst3 d).det = d := by
  simp [rinvFirst3, Matrix.det_diagonal]

theorem rinvFirst3_mul_diagonal_comm (d : F) (ε : Fin 3 → F) :
    rinvFirst3 d * Matrix.diagonal ε = Matrix.diagonal ε * rinvFirst3 d := by
  simp only [rinvFirst3, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem rinv3_exists_det_one (h2 : (2 : F) ≠ 0) (T : Matrix (Fin 3) (Fin 3) F) (hT : T * T = 1)
    (hdet : T.det = 1) (h1 : T ≠ 1) :
    ∃ P : Matrix (Fin 3) (Fin 3) F, P.det = 1 ∧ T * P = P * Matrix.diagonal (rinvSign F 3 2) := by
  classical
  have hf : ∀ v, Matrix.toLin' T (Matrix.toLin' T v) = v := rinv_toLin_involutive T hT
  have hsum := involution_finrank_add h2 (Matrix.toLin' T) hf
  have h3 : finrank F (Fin 3 → F) = 3 := by simp
  obtain ⟨b, hb⟩ : ∃ b, finrank F (LinearMap.ker (Matrix.toLin' T - LinearMap.id)) = b := ⟨_, rfl⟩
  have ha : finrank F (LinearMap.ker (Matrix.toLin' T + LinearMap.id)) = 2 :=
    rinv3_dim_two h2 T hT hdet h1
  have hab : 2 + b = 3 := by rw [← ha, ← hb, hsum, h3]
  obtain ⟨B, hB1, hB2⟩ := exists_basis_involution' h2 (Matrix.toLin' T) hf 2 b ha hb
  have hB1' : ∀ i, T *ᵥ B (Sum.inl i) = -B (Sum.inl i) := fun i => by
    simpa [Matrix.toLin'_apply] using hB1 i
  have hB2' : ∀ j, T *ᵥ B (Sum.inr j) = B (Sum.inr j) := fun j => by
    simpa [Matrix.toLin'_apply] using hB2 j
  have hTP := rinvMat_mul_eq hab B T hB1' hB2'
  have hu := rinvMat_isUnit hab B
  have hd0 : (rinvMat hab B).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  refine ⟨rinvMat hab B * rinvFirst3 (rinvMat hab B).det⁻¹, ?_, ?_⟩
  · rw [Matrix.det_mul, rinv3_det_first, mul_inv_cancel₀ hd0]
  · rw [← Matrix.mul_assoc, hTP, Matrix.mul_assoc, Matrix.mul_assoc, rinvFirst3_mul_diagonal_comm]

theorem invClass3_lin (h2 : (2 : F) ≠ 0) (s t : SL(3, F)) (hs : s * s = 1) (ht : t * t = 1)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) : ∃ g : SL(3, F), g * s * g⁻¹ = t := by
  obtain ⟨D, hD⟩ : ∃ D : SL(3, F), (D : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (rinvSign F 3 2) := ⟨⟨_, rinv_det_diagonal_sign3⟩, rfl⟩
  have key : ∀ u : SL(3, F), u * u = 1 → u ≠ 1 → ∃ g : SL(3, F), g * u * g⁻¹ = D := by
    intro u huu hu1
    have hT : (u : Matrix (Fin 3) (Fin 3) F) * (u : Matrix (Fin 3) (Fin 3) F) = 1 := by
      have := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) huu
      simpa using this
    have hT1 : (u : Matrix (Fin 3) (Fin 3) F) ≠ 1 := fun h => hu1 (Subtype.ext (by simpa using h))
    obtain ⟨P, hPdet, hTP⟩ := rinv3_exists_det_one h2 (u : Matrix (Fin 3) (Fin 3) F) hT u.2 hT1
    obtain ⟨Pm, hPm⟩ : ∃ Pm : SL(3, F), (Pm : Matrix (Fin 3) (Fin 3) F) = P := ⟨⟨P, hPdet⟩, rfl⟩
    refine rinv_group_conj (P := Pm) ?_
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hD, hPm]
    exact congrFun (congrFun hTP i) j
  obtain ⟨g₁, h₁⟩ := key s hs hs1
  obtain ⟨g₂, h₂⟩ := key t ht ht1
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  calc g₂⁻¹ * g₁ * s * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * s * g₁⁻¹) * g₂ := by group
    _ = g₂⁻¹ * D * g₂ := by rw [h₁]
    _ = t := by rw [← h₂]; group

end Lin3

section Uni3

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {F : Type} [Field F] {p f : ℕ}

theorem rinvFirst3_mul (d e : F) : rinvFirst3 d * rinvFirst3 e = rinvFirst3 (d * e) := by
  simp only [rinvFirst3, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  by_cases hi : i = 0 <;> simp [hi]

theorem rinvFirst3_one : rinvFirst3 (1 : F) = 1 := by
  simp [rinvFirst3]

theorem rinvFirst3_map (σ : F →+* F) (d : F) : (rinvFirst3 d).map σ = rinvFirst3 (σ d) := by
  rw [rinvFirst3, Matrix.diagonal_map (map_zero σ), rinvFirst3]
  congr 1
  ext i
  by_cases hi : i = 0 <;> simp [hi]

theorem rinv3_exists_unitary_det_one (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0)
    (T : Matrix (Fin 3) (Fin 3) F) (hT : T * T = 1) (hU : (T.map h.bar)ᵀ * T = 1)
    (hdet : T.det = 1) (h1 : T ≠ 1) :
    ∃ P : Matrix (Fin 3) (Fin 3) F, P.det = 1 ∧ (P.map h.bar)ᵀ * P = 1 ∧
      T * P = P * Matrix.diagonal (rinvSign F 3 2) := by
  classical
  have hf : ∀ v, Matrix.toLin' T (Matrix.toLin' T v) = v := rinv_toLin_involutive T hT
  have hsum := involution_finrank_add h2 (Matrix.toLin' T) hf
  have h3 : finrank F (Fin 3 → F) = 3 := by simp
  obtain ⟨b, hb⟩ : ∃ b, finrank F (LinearMap.ker (Matrix.toLin' T - LinearMap.id)) = b := ⟨_, rfl⟩
  have ha : finrank F (LinearMap.ker (Matrix.toLin' T + LinearMap.id)) = 2 :=
    rinv3_dim_two h2 T hT hdet h1
  have hab : 2 + b = 3 := by rw [← ha, ← hb, hsum, h3]
  obtain ⟨B, hB1, hB2, hon⟩ := rinv_orthonormal_basis h h2 T hT hU 2 b ha hb
  have hTP := rinvMat_mul_eq hab B T hB1 hB2
  have hPU := rinvMat_unitary h hab B hon
  have hd : h.bar (rinvMat hab B).det * (rinvMat hab B).det = 1 := by
    have := congrArg Matrix.det hPU
    rwa [Matrix.det_mul, rinv_det_map_bar, Matrix.det_one] at this
  have hd0 : (rinvMat hab B).det ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hd
    exact zero_ne_one hd
  refine ⟨rinvMat hab B * rinvFirst3 (rinvMat hab B).det⁻¹, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, rinv3_det_first, mul_inv_cancel₀ hd0]
  · calc ((rinvMat hab B * rinvFirst3 (rinvMat hab B).det⁻¹).map h.bar)ᵀ *
          (rinvMat hab B * rinvFirst3 (rinvMat hab B).det⁻¹)
        = ((rinvFirst3 (rinvMat hab B).det⁻¹).map h.bar)ᵀ *
            (((rinvMat hab B).map h.bar)ᵀ * rinvMat hab B) * rinvFirst3 (rinvMat hab B).det⁻¹ := by
          rw [Matrix.map_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hPU, Matrix.mul_one, rinvFirst3_map, rinvFirst3, Matrix.diagonal_transpose,
            ← rinvFirst3, rinvFirst3_mul, map_inv₀, ← mul_inv, hd, inv_one, rinvFirst3_one]
  · rw [← Matrix.mul_assoc, hTP, Matrix.mul_assoc, Matrix.mul_assoc, rinvFirst3_mul_diagonal_comm]

end Uni3

theorem invClass3_uni {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : Odd q) (s t : ↥(StatedSU 3 q F)) (hs : s * s = 1) (ht : t * t = 1) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) : ∃ g : ↥(StatedSU 3 q F), g * s * g⁻¹ = t := by
  obtain ⟨p, f, h, rfl⟩ := rinv_exists_unitaryFieldData hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact hq.pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  have key : ∀ P : Matrix (Fin 3) (Fin 3) F, P.det = 1 → (P.map h.bar)ᵀ * P = 1 →
      ∃ Pm : ↥(StatedSU 3 (p ^ f) F), (((Pm : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) = P :=
    fun P hdet hP => ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P (by rw [hdet]; exact one_ne_zero),
      (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).2 ⟨hdet, hP⟩⟩, rfl⟩
  have hD : (Matrix.diagonal (rinvSign F 3 2)).det = 1 ∧
      ((Matrix.diagonal (rinvSign F 3 2)).map h.bar)ᵀ * Matrix.diagonal (rinvSign F 3 2) = 1 := by
    refine ⟨rinv_det_diagonal_sign3, ?_⟩
    rw [rinvSign_three_two, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  obtain ⟨D, hDm⟩ := key _ hD.1 hD.2
  have conj1 : ∀ u : ↥(StatedSU 3 (p ^ f) F), u * u = 1 → u ≠ 1 →
      ∃ g : ↥(StatedSU 3 (p ^ f) F), g * u * g⁻¹ = D := by
    intro u huu hu1
    have hT : ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      have := congrArg (fun x : ↥(StatedSU 3 (p ^ f) F) =>
        ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) huu
      simpa using this
    have hT1 : ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 := fun h' =>
      hu1 (Subtype.ext (Units.ext (by simpa using h')))
    obtain ⟨hdet, hU⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 u.2
    obtain ⟨P, hPdet, hPU, hTP⟩ := rinv3_exists_unitary_det_one h h2 _ hT hU hdet hT1
    obtain ⟨Pm, hPm⟩ := key P hPdet hPU
    refine rinv_group_conj (P := Pm) ?_
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hPm, hDm]
    exact hTP
  obtain ⟨g₁, h₁⟩ := conj1 s hs hs1
  obtain ⟨g₂, h₂⟩ := conj1 t ht ht1
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  calc g₂⁻¹ * g₁ * s * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * s * g₁⁻¹) * g₂ := by group
    _ = g₂⁻¹ * D * g₂ := by rw [h₁]
    _ = t := by rw [← h₂]; group


theorem fusion_of_hom {A X : Type} [Group A] [Finite A] [Group X] (θ : A →* X)
    (hker : θ.ker ≤ Subgroup.center A) (hodd : Odd (Nat.card (Subgroup.center A)))
    (hA : ∀ s t : A, s * s = 1 → t * t = 1 → s ≠ 1 → t ≠ 1 → ∃ g : A, g * s * g⁻¹ = t) :
    ∀ s t : X, s ∈ θ.range → t ∈ θ.range → s * s = 1 → t * t = 1 → s ≠ 1 → t ≠ 1 →
      ∃ g ∈ θ.range, g * s * g⁻¹ = t := by
  intro s t hs ht hs2 ht2 hs1 ht1
  obtain ⟨s', hs'2, hs'⟩ := exists_involution_preimage θ hker hodd hs hs2
  obtain ⟨t', ht'2, ht'⟩ := exists_involution_preimage θ hker hodd ht ht2
  have hs'1 : s' ≠ 1 := fun h => hs1 (by rw [← hs', h, map_one])
  have ht'1 : t' ≠ 1 := fun h => ht1 (by rw [← ht', h, map_one])
  obtain ⟨g, hg⟩ := hA s' t' hs'2 ht'2 hs'1 ht'1
  refine ⟨θ g, ⟨g, rfl⟩, ?_⟩
  rw [← hs', ← ht', ← hg, map_mul, map_mul, map_inv]

theorem sup_eq_range_of_blocks {A X : Type} [Group A] [Group X] (θ : A →* X) (c : A)
    {B₁ B₂ : Subgroup A} (htop : B₁ ⊔ B₂ = ⊤) {U V : Subgroup X}
    (h1 : (B₁.map (MulAut.conj c⁻¹).toMonoidHom).map θ = U)
    (h2 : (B₂.map (MulAut.conj c⁻¹).toMonoidHom).map θ = V) : U ⊔ V = θ.range := by
  rw [← h1, ← h2, ← Subgroup.map_sup, ← Subgroup.map_sup, htop,
    Subgroup.map_top_of_surjective _ (MulAut.conj c⁻¹).surjective, MonoidHom.range_eq_map]

theorem odd_card_center_lin3 {F : Type} [Field F] [Finite F] :
    Odd (Nat.card (Subgroup.center SL(3, F))) := by
  rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 3 (by norm_num)]
  exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)

theorem odd_card_center_uni3 {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : Odd q) : Odd (Nat.card (Subgroup.center ↥(StatedSU 3 q F))) := by
  obtain ⟨p, f, h, rfl⟩ := rcard_exists_unitaryFieldData hF
  have : Fact p.Prime := ⟨h.prime⟩
  have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := by
    intro h'
    have : p ^ f = 2 := (Prod.mk.inj h').2
    rw [this] at hq
    exact absurd hq (by decide)
  have hc := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := p)
    (f := f) (n := 3) hF (by norm_num) hnq).2
  rw [hc, (CFSG.LinearGroups.unitary_scalar_kernel h.prime hF (n := 3) (by norm_num)).2.2]
  exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)

theorem lin_pair_fusion {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) {X : Type} [Group X]
    {W U V : Subgroup X} (hP : CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair F W U V) :
    W = U ⊔ V ∧ ∀ s t : X, s ∈ W → t ∈ W → orderOf s = 2 → orderOf t = 2 →
      ∃ g ∈ W, g * s * g⁻¹ = t := by
  obtain ⟨θ, c, hrange, hker, hcases⟩ := hP
  have hsup : W = U ⊔ V := by
    rw [← hrange]
    rcases hcases with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · exact (sup_eq_range_of_blocks θ c CFSG.ClassicalInvolution.WeakCT.B12_sup_B23 h1 h2').symm
    · rw [sup_comm]
      exact (sup_eq_range_of_blocks θ c CFSG.ClassicalInvolution.WeakCT.B12_sup_B23 h1 h2').symm
  refine ⟨hsup, ?_⟩
  intro s t hs ht hs2 ht2
  have hs2' : s * s = 1 := by rw [← sq, ← hs2]; exact pow_orderOf_eq_one s
  have ht2' : t * t = 1 := by rw [← sq, ← ht2]; exact pow_orderOf_eq_one t
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  rw [← hrange] at hs ht ⊢
  exact fusion_of_hom θ hker odd_card_center_lin3 (invClass3_lin h2) s t hs ht hs2' ht2' hs1 ht1

theorem uni_pair_fusion {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hq : Odd (p ^ f)) {X : Type} [Group X] {W U V : Subgroup X}
    (hP : CFSG.ClassicalInvolution.Phan.UnitaryBlockStandardPair F p f W U V) :
    W = U ⊔ V ∧ ∀ s t : X, s ∈ W → t ∈ W → orderOf s = 2 → orderOf t = 2 →
      ∃ g ∈ W, g * s * g⁻¹ = t := by
  have hq2 : p ^ f ≠ 2 := by
    intro h
    rw [h] at hq
    exact absurd hq (by decide)
  obtain ⟨θ, c, hrange, hker, hcases⟩ := hP
  have hsup : W = U ⊔ V := by
    rw [← hrange]
    rcases hcases with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · exact (sup_eq_range_of_blocks θ c (CFSG.ClassicalInvolution.Phan.B12_sup_B23 hF hq2) h1 h2').symm
    · rw [sup_comm]
      exact (sup_eq_range_of_blocks θ c (CFSG.ClassicalInvolution.Phan.B12_sup_B23 hF hq2) h1 h2').symm
  refine ⟨hsup, ?_⟩
  intro s t hs ht hs2 ht2
  have hs2' : s * s = 1 := by rw [← sq, ← hs2]; exact pow_orderOf_eq_one s
  have ht2' : t * t = 1 := by rw [← sq, ← ht2]; exact pow_orderOf_eq_one t
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hodd : Odd (Nat.card (Subgroup.center (CFSG.ClassicalInvolution.Phan.Su F p f 3))) := by
    rw [Nat.card_congr (Subgroup.centerCongr (CFSG.GH74.L5U5.suEquiv hF 3)).toEquiv]
    exact odd_card_center_uni3 hF hq
  have hA : ∀ s t : CFSG.ClassicalInvolution.Phan.Su F p f 3, s * s = 1 → t * t = 1 → s ≠ 1 →
      t ≠ 1 → ∃ g : CFSG.ClassicalInvolution.Phan.Su F p f 3, g * s * g⁻¹ = t := by
    intro s t hs hs2 hs1 ht1
    obtain ⟨g, hg⟩ := invClass3_uni hF hq (CFSG.GH74.L5U5.suEquiv hF 3 s)
      (CFSG.GH74.L5U5.suEquiv hF 3 t) (by rw [← map_mul, hs, map_one])
      (by rw [← map_mul, hs2, map_one])
      (fun h => hs1 ((CFSG.GH74.L5U5.suEquiv hF 3).injective (by rw [h, map_one])))
      (fun h => ht1 ((CFSG.GH74.L5U5.suEquiv hF 3).injective (by rw [h, map_one])))
    refine ⟨(CFSG.GH74.L5U5.suEquiv hF 3).symm g, (CFSG.GH74.L5U5.suEquiv hF 3).injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hg
  rw [← hrange] at hs ht ⊢
  exact fusion_of_hom θ hker hodd hA s t hs ht hs2' ht2' hs1 ht1

end CFSG.GH74.Generic.S1

module

public import CFSG.CGT.Stroth77.Extension28Basic

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {m : ℕ} {hm : 2 ≤ m}

theorem t310_k_pos (hm : 2 ≤ m) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t310 m hm).k i := by
  fin_cases i <;> (change 1 ≤ m; omega)

theorem parityTorus_rho310 (hk : ∀ i, 1 ≤ Type310.k m i) (y : Torus (Type310.k m)) :
    parityTorus _ hk ((Type310.action m hm).φρ y) = rhoBar300 (parityTorus _ hk y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type310.k m) y
  rw [type310_rho_apply_gens, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h4 : (4 : ZMod 2) = 0 := by decide
  funext t
  fin_cases t
  · simp [rhoBar300, h4]
  · simp [rhoBar300, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar300, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

section Square

variable (D : StrothTypeData B (StrothTypeIndex.t310 m hm))
  (hsq : ∀ x : C, (x : S) * x ∈ B)

@[expose] noncomputable def sqParity310 (x : C) : Fin 3 → ZMod 2 :=
  parityTorus _ (t310_k_pos hm) (D.ec ⟨(x : S) * x, hsq x⟩)

variable {D hsq}

theorem sqParity310_mul (hcomm : ∀ x y : C, x * y = y * x) (x y : C) :
    sqParity310 D hsq (x * y) = sqParity310 D hsq x + sqParity310 D hsq y := by
  have hxy : (⟨((x * y : C) : S) * ((x * y : C) : S), hsq (x * y)⟩ : B) =
      ⟨(x : S) * x, hsq x⟩ * ⟨(y : S) * y, hsq y⟩ := by
    apply Subtype.ext
    have h := congrArg Subtype.val (hcomm x y)
    simp only [Subgroup.coe_mul] at h ⊢
    calc (x : S) * y * ((x : S) * y) = x * ((y : S) * x) * y := by group
      _ = x * ((x : S) * y) * y := by rw [← h]
      _ = (x : S) * x * ((y : S) * y) := by group
  simp only [sqParity310]
  rw [hxy, D.ec_mul, map_add]

theorem sqParity310_of_mem (x : C) (hx : (x : S) ∈ B) : sqParity310 D hsq x = 0 := by
  simp only [sqParity310]
  rw [parityTorus_eq_zero_iff]
  refine ⟨D.ec ⟨x, hx⟩, ?_⟩
  have h : (⟨(x : S) * x, hsq x⟩ : B) = ⟨x, hx⟩ * ⟨x, hx⟩ := rfl
  rw [h, D.ec_mul, two_nsmul]

theorem mem_of_sqParity310_eq_zero (hcomm : ∀ x y : C, x * y = y * x)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hH : NoInvolutionsCentralizing S' B)
    (hcS : C ≤ S') (hBC : B ≤ C) (x : C) (h : sqParity310 D hsq x = 0) :
    (x : S) ∈ B := by
  simp only [sqParity310] at h
  rw [parityTorus_eq_zero_iff] at h
  obtain ⟨z, hz⟩ := h
  let σ : B := Additive.toMul (D.e.symm z)
  have hσz : D.ec σ = z := D.e.apply_symm_apply z
  have hσ : σ * σ = ⟨(x : S) * x, hsq x⟩ := by
    apply D.ec_injective
    rw [D.ec_mul, ← two_nsmul, hσz, hz]
  have hσS : (σ : S) * σ = (x : S) * x := by
    simpa using congrArg Subtype.val hσ
  let σC : C := ⟨σ, hBC σ.2⟩
  let w : C := x * σC⁻¹
  have hww : (w : S) * w = 1 := by
    have hwC : w * w = 1 := by
      calc w * w = x * (σC⁻¹ * x) * σC⁻¹ := by simp only [w]; group
        _ = x * (x * σC⁻¹) * σC⁻¹ := by rw [hcomm σC⁻¹ x]
        _ = (x * x) * (σC * σC)⁻¹ := by group
        _ = 1 := by
          rw [mul_inv_eq_one]
          apply Subtype.ext
          simpa [σC] using hσS.symm
    simpa using congrArg Subtype.val hwC
  have hwB : (w : S) ∈ B := hH w (hcS w.2) hww (hC w.2)
  have hx : (x : S) = w * σ := by simp [w, σC]
  rw [hx]
  exact B.mul_mem hwB σ.2

theorem sqParity310_conj_ρ (hL : D.L ≤ Subgroup.normalizer C) (x : C) :
    sqParity310 D hsq (conjBy (hL D.ρ_mem_L) x) = rhoBar300 (sqParity310 D hsq x) := by
  have h : (⟨((conjBy (hL D.ρ_mem_L) x : C) : S) * (conjBy (hL D.ρ_mem_L) x : C),
      hsq _⟩ : B) = conjBy D.ρ_mem ⟨(x : S) * x, hsq x⟩ := by
    apply Subtype.ext
    simp only [conjBy_val]
    group
  simp only [sqParity310]
  rw [h]
  have hconj : D.ec (conjBy D.ρ_mem ⟨(x : S) * x, hsq x⟩) =
      (Type310.action m hm).φρ (D.ec ⟨(x : S) * x, hsq x⟩) := D.ρ_conj _
  rw [hconj]
  exact parityTorus_rho310 (t310_k_pos hm) _

theorem sqParity310_of_sq_eq_a (hBC : B ≤ C) {x : C} (hx : x * x = ⟨D.a, hBC D.a.2⟩) :
    sqParity310 D hsq x = Pi.single 1 1 := by
  have h : (⟨(x : S) * x, hsq x⟩ : B) = D.a := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hx
  simp only [sqParity310]
  rw [h, D.ec_a]
  exact parityTorus_gen _ _ 1

theorem sqParity310_of_sq_eq_b (hBC : B ≤ C) {x : C} (hx : x * x = ⟨D.b, hBC D.b.2⟩) :
    sqParity310 D hsq x = Pi.single 2 1 := by
  have h : (⟨(x : S) * x, hsq x⟩ : B) = D.b := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hx
  simp only [sqParity310]
  rw [h, D.ec_b]
  exact parityTorus_gen _ _ 2

end Square

section Main

variable [hN : (B.subgroupOf C).Normal]

theorem exists_sq_eq_a310_of_data (D : StrothTypeData B (StrothTypeIndex.t310 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    ∃ e : C, e * e = ⟨D.a, hBC D.a.2⟩ := by
  classical
  have hcommC : IsMulCommutative C := isMulCommutative_of_relIndex_four_t310_of_data D hBC hC hrel hL hncyc
  have hcomm : ∀ x y : C, x * y = y * x := fun x y => hcommC.is_comm.comm x y
  have hsq : ∀ x : C, (x : S) * x ∈ B := sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc
  have hcardQ : Nat.card (C ⧸ B.subgroupOf C) = 4 := card_quotient_four hBC hC hrel
  have hexp : ∀ q : C ⧸ B.subgroupOf C, q * q = 1 := by
    rcases cyclic_or_sq_eq_one hcardQ with hcyc | h
    · exact absurd hcyc hncyc
    · exact h
  let P : C → Fin 3 → ZMod 2 := sqParity310 D hsq
  have hPmul : ∀ x y, P (x * y) = P x + P y := sqParity310_mul hcomm
  have hPB : ∀ x : C, x ∈ B.subgroupOf C → P x = 0 := fun x hx =>
    sqParity310_of_mem x (Subgroup.mem_subgroupOf.mp hx)
  have hP0 : ∀ x : C, P x = 0 → x ∈ B.subgroupOf C := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (mem_of_sqParity310_eq_zero hcomm hC hH hcS hBC x hx)
  have hPinv : ∀ x, P x⁻¹ = -P x := by
    intro x
    have h := hPmul x⁻¹ x
    rw [inv_mul_cancel, hPB 1 (Subgroup.one_mem _)] at h
    exact (neg_eq_of_add_eq_zero_left h.symm).symm
  obtain ⟨x₁, x₂, h1, h2, h12⟩ := exists_gens_Idx4 hcardQ hncyc
  have hrange : ∀ y : C, P y = 0 ∨ P y = P x₁ ∨ P y = P x₂ ∨ P y = P x₁ + P x₂ := by
    intro y
    have hcoset := mem_cosets_Idx4 hcardQ hexp h1 h2 h12 y
    have key : ∀ x : C, y * x⁻¹ ∈ B.subgroupOf C → P y = P x := by
      intro x hx
      have h := hPmul (y * x⁻¹) x
      rw [inv_mul_cancel_right, hPB _ hx, zero_add] at h
      exact h
    rcases hcoset with h | h | h | h
    · exact Or.inl (hPB y h)
    · exact Or.inr (Or.inl (key x₁ h))
    · exact Or.inr (Or.inr (Or.inl (key x₂ h)))
    · exact Or.inr (Or.inr (Or.inr ((key _ h).trans (hPmul x₁ x₂))))
  have hv1 : P x₁ ≠ 0 := fun h => h1 (hP0 x₁ h)
  have hv2 : P x₂ ≠ 0 := fun h => h2 (hP0 x₂ h)
  have hv12 : P x₁ ≠ P x₂ := by
    intro h
    apply h12
    apply hP0
    rw [hPmul, hPinv, h]
    exact add_neg_cancel _
  have hρ1 := hrange (conjBy (hL D.ρ_mem_L) x₁)
  have hρ2 := hrange (conjBy (hL D.ρ_mem_L) x₂)
  rw [show P (conjBy (hL D.ρ_mem_L) x₁) = rhoBar300 (P x₁) from sqParity310_conj_ρ hL x₁]
    at hρ1
  rw [show P (conjBy (hL D.ρ_mem_L) x₂) = rhoBar300 (P x₂) from sqParity310_conj_ρ hL x₂]
    at hρ2
  obtain ⟨y, hy⟩ : ∃ y : C, P y = Pi.single 1 1 := by
    rcases rhoBar300_check (P x₁) (P x₂) ⟨hv1, hv2, hv12, hρ1, hρ2⟩ with h | h | h
    · exact ⟨x₁, h⟩
    · exact ⟨x₂, h⟩
    · exact ⟨x₁ * x₂, (hPmul x₁ x₂).trans h⟩
  have hpar : parityTorus _ (t310_k_pos hm) (D.ec (⟨(y : S) * y, hsq y⟩ * D.a⁻¹)) = 0 := by
    have hy' : parityTorus _ (t310_k_pos hm) (D.ec ⟨(y : S) * y, hsq y⟩) = Pi.single 1 1 := hy
    rw [D.ec_mul, D.ec_inv, map_add, map_neg, D.ec_a, parityTorus_gen, hy']
    exact add_neg_cancel _
  rw [parityTorus_eq_zero_iff] at hpar
  obtain ⟨z, hz⟩ := hpar
  let σ : B := Additive.toMul (D.e.symm z)
  have hσz : D.ec σ = z := D.e.apply_symm_apply z
  have hσ : σ * σ = ⟨(y : S) * y, hsq y⟩ * D.a⁻¹ := by
    apply D.ec_injective
    rw [D.ec_mul, ← two_nsmul, hσz, hz]
  let aC : C := ⟨D.a, hBC D.a.2⟩
  let σC : C := ⟨σ, hBC σ.2⟩
  have hσC2 : σC * σC = y * y * aC⁻¹ := by
    apply Subtype.ext
    simpa [σC, aC] using congrArg Subtype.val hσ
  refine ⟨y * σC⁻¹, ?_⟩
  change y * σC⁻¹ * (y * σC⁻¹) = aC
  calc y * σC⁻¹ * (y * σC⁻¹) = y * (σC⁻¹ * y) * σC⁻¹ := by group
    _ = y * (y * σC⁻¹) * σC⁻¹ := by rw [hcomm σC⁻¹ y]
    _ = (y * y) * (σC * σC)⁻¹ := by group
    _ = (y * y) * (y * y * aC⁻¹)⁻¹ := by rw [hσC2]
    _ = aC := by
      rw [mul_inv_rev, inv_inv, ← mul_assoc, hcomm (y * y) aC, mul_assoc, mul_inv_cancel,
        mul_one]

theorem exists_sq_eq_a310 (hB : HasStrothType B (StrothTypeIndex.t310 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    ∃ e : C, e * e = ⟨hB.data.a, hBC hB.data.a.2⟩ :=
  exists_sq_eq_a310_of_data hB.data hBC hC hrel hL hH hcS hncyc

end Main

end CFSG.CGT.Stroth77

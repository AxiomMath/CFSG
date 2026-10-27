module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryEmbed

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld Matrix
open scoped MatrixGroups

section SL3Tau

@[expose] noncomputable def sl3Tau (F : Type) [Field F] : SL(3, F) →* SL(3, F) where
  toFun y := ⟨(((y⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ, by
    rw [Matrix.det_transpose]; exact (y⁻¹).2⟩
  map_one' := by
    apply Subtype.ext
    simp only [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  map_mul' x y := by
    apply Subtype.ext
    simp only [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
    rfl

variable {F : Type} [Field F]

theorem sl3Tau_apply (y : SL(3, F)) :
    ((sl3Tau F y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (((y⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ := rfl

theorem tv_inv_eq_tv_neg {n : ℕ} {i j : Fin n} (h : i ≠ j) (c : F) :
    (tv i j c)⁻¹ = tv i j (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [tv_of_ne h, tv_of_ne h]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  have := Matrix.transvection_mul_transvection_same i j h c (-c)
  simp only [Matrix.transvection, add_neg_cancel, Matrix.single_zero, add_zero] at this
  simpa using this

theorem sl3Tau_tv (i j : Fin 3) (h : i ≠ j) (c : F) : sl3Tau F (tv i j c) = tv j i (-c) := by
  apply Subtype.ext
  rw [sl3Tau_apply, tv_inv_eq_tv_neg h, tv_of_ne h, tv_of_ne h.symm,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  simp [Matrix.transpose_add, Matrix.transpose_single]

end SL3Tau

section Scalar

variable {τ : Tag} {k : Type} [Field k]

theorem conj_scalar_inv {g : ModGL τ k} {γ γ' : Fin τ.rank → ℤ} {A : k} (hA : A ≠ 0)
    (h : ∀ x : k, g * pinnedX τ k γ x * g⁻¹ = pinnedX τ k γ' (A * x)) :
    ∀ x : k, g⁻¹ * pinnedX τ k γ' x * g = pinnedX τ k γ (A⁻¹ * x) := by
  intro x
  have h1 := h (A⁻¹ * x)
  rw [← mul_assoc, mul_inv_cancel₀ hA, one_mul] at h1
  calc g⁻¹ * pinnedX τ k γ' x * g = g⁻¹ * (g * pinnedX τ k γ (A⁻¹ * x) * g⁻¹) * g := by rw [h1]
    _ = _ := by group

theorem conj_scalar_comp {g h : ModGL τ k} {γ γ' γ'' : Fin τ.rank → ℤ} {A B : k}
    (hg : ∀ x : k, g * pinnedX τ k γ x * g⁻¹ = pinnedX τ k γ' (A * x))
    (hh : ∀ x : k, h * pinnedX τ k γ' x * h⁻¹ = pinnedX τ k γ'' (B * x)) :
    ∀ x : k, (h * g) * pinnedX τ k γ x * (h * g)⁻¹ = pinnedX τ k γ'' ((B * A) * x) := by
  intro x
  calc h * g * pinnedX τ k γ x * (h * g)⁻¹ = h * (g * pinnedX τ k γ x * g⁻¹) * h⁻¹ := by group
    _ = _ := by rw [hg x, hh (A * x), mul_assoc]

theorem frobenius_conj_scalar (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k] (e : ℕ)
    {t : ModGL τ k} {γ : Fin τ.rank → ℤ} {c : k}
    (h : ∀ x : k, t * pinnedX τ k γ x * t⁻¹ = pinnedX τ k γ (c * x)) (x : k) :
    entrywiseFrobGL τ k p e t * pinnedX τ k γ x * (entrywiseFrobGL τ k p e t)⁻¹ =
      pinnedX τ k γ (c ^ p ^ e * x) := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq x (pow_pos (Fact.out : p.Prime).pos e)
  have := congrArg (entrywiseFrobGL τ k p e) (h y)
  rw [map_mul, map_mul, map_inv, entrywiseFrobGL_pinnedX, entrywiseFrobGL_pinnedX,
    iterateFrobenius_def, iterateFrobenius_def, mul_pow, hy] at this
  exact this

omit [Field k] in
theorem scalar_core {k : Type} [Field k] {X Λ₀ Λ₁ κ : k} {q : ℕ}
    (hn : X ^ (q + 1) = Λ₀ * κ) (h01 : Λ₀ * Λ₁ = 1) (hκ : κ * κ = 1) :
    X⁻¹ ^ q * (Λ₀ * X⁻¹) = κ ∧ X ^ q * (Λ₁ * X) = κ := by
  have hΛ : Λ₀ ≠ 0 := fun h => by simp [h] at h01
  have hκ0 : κ ≠ 0 := fun h => by simp [h] at hκ
  constructor
  · have h1 : X⁻¹ ^ q * (Λ₀ * X⁻¹) = Λ₀ * (X ^ (q + 1))⁻¹ := by
      rw [pow_succ, mul_inv, inv_pow]
      ring
    rw [h1, hn, mul_inv, ← mul_assoc, mul_inv_cancel₀ hΛ, one_mul]
    exact inv_eq_of_mul_eq_one_right hκ
  · calc X ^ q * (Λ₁ * X) = X ^ (q + 1) * Λ₁ := by ring
      _ = κ := by rw [hn]; linear_combination κ * h01

end Scalar

section TorusPair

variable {τ : Tag} {k : Type} [Field k]

theorem torusMod_pair (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k] (e : ℕ)
    {γ : Fin τ.rank → ℤ} {t u u' : ModGL τ k} {χ : kˣ} {Λ Λ' κ : k}
    (hu' : u' = entrywiseFrobGL τ k p e t * u * t⁻¹)
    (ht₁ : ∀ x : k, t * pinnedX τ k γ x * t⁻¹ = pinnedX τ k γ ((χ : k) * x))
    (ht₂ : ∀ x : k, t * pinnedX τ k (-γ) x * t⁻¹ =
      pinnedX τ k (-γ) (((χ⁻¹ : kˣ) : k) * x))
    (hu₁ : ∀ x : k, u * pinnedX τ k γ x * u⁻¹ = pinnedX τ k (-γ) (Λ * x))
    (hu₂ : ∀ x : k, u * pinnedX τ k (-γ) x * u⁻¹ = pinnedX τ k γ (Λ' * x))
    (hχ : (χ : k) ^ (p ^ e + 1) = Λ * κ) (hΛ : Λ * Λ' = 1) (hκ : κ * κ = 1) :
    (∀ x : k, u' * pinnedX τ k γ x * u'⁻¹ = pinnedX τ k (-γ) (κ * x)) ∧
      ∀ x : k, u' * pinnedX τ k (-γ) x * u'⁻¹ = pinnedX τ k γ (κ * x) := by
  have hχ0 : (χ : k) ≠ 0 := χ.ne_zero
  have hχ' : ((χ⁻¹ : kˣ) : k) = (χ : k)⁻¹ := Units.val_inv_eq_inv_val χ
  have i₁ : ∀ x : k, t⁻¹ * pinnedX τ k γ x * (t⁻¹)⁻¹ =
      pinnedX τ k γ (((χ : k))⁻¹ * x) := fun x => by
    rw [inv_inv]
    exact conj_scalar_inv hχ0 ht₁ x
  have i₂ : ∀ x : k, t⁻¹ * pinnedX τ k (-γ) x * (t⁻¹)⁻¹ =
      pinnedX τ k (-γ) ((((χ⁻¹ : kˣ) : k))⁻¹ * x) := fun x => by
    rw [inv_inv]
    exact conj_scalar_inv (by rw [hχ']; exact inv_ne_zero hχ0) ht₂ x
  have f₁ := frobenius_conj_scalar (τ := τ) p e ht₁
  have f₂ := frobenius_conj_scalar (τ := τ) p e ht₂
  obtain ⟨c₁, c₂⟩ := scalar_core (X := (χ : k)) hχ hΛ hκ
  subst hu'
  constructor
  · intro x
    have := conj_scalar_comp i₁ (conj_scalar_comp hu₁ f₂) x
    rw [this]
    congr 1
    rw [hχ']
    linear_combination x * c₁
  · intro x
    have := conj_scalar_comp i₂ (conj_scalar_comp hu₂ f₁) x
    rw [this]
    congr 1
    rw [hχ', inv_inv]
    linear_combination x * c₂

end TorusPair

section TorusElement

variable {τ : Tag} {k : Type} [Field k] {θ δ : Fin τ.rank → ℤ}

variable (k) in
@[expose] noncomputable def torusPair (θ δ : Fin τ.rank → ℤ) (a b : kˣ) : ModGL τ k :=
  rootTorusSL2 τ k θ a * rootTorusSL2 τ k δ b

theorem torusPair_mem_torusGroup (hθ : IsRoot τ θ) (hδ : IsRoot τ δ) (a b : kˣ) :
    torusPair k θ δ a b ∈ torusGroup τ k :=
  mul_mem ((exceptional_Lang_root_rank_one_torus_transport τ k hθ).2.1 a)
    ((exceptional_Lang_root_rank_one_torus_transport τ k hδ).2.1 b)

theorem torusPair_conj {α : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (hδ : IsRoot τ δ)
    (hα : IsRoot τ α) {n m : ℤ} (hn : 2 * iform θ α / iform θ θ = n)
    (hm : 2 * iform δ α / iform δ δ = m) (a b : kˣ) (x : k) :
    torusPair k θ δ a b * pinnedX τ k α x * (torusPair k θ δ a b)⁻¹ =
      pinnedX τ k α (((a ^ n * b ^ m : kˣ) : k) * x) := by
  unfold torusPair
  calc rootTorusSL2 τ k θ a * rootTorusSL2 τ k δ b * pinnedX τ k α x *
        (rootTorusSL2 τ k θ a * rootTorusSL2 τ k δ b)⁻¹ =
      rootTorusSL2 τ k θ a * (rootTorusSL2 τ k δ b * pinnedX τ k α x *
        (rootTorusSL2 τ k δ b)⁻¹) * (rootTorusSL2 τ k θ a)⁻¹ := by group
    _ = _ := by
      rw [← hm, ← hn, rootTorusSL2_conj_pinnedX_of_isRoot hδ hα,
        rootTorusSL2_conj_pinnedX_of_isRoot hθ hα, Units.val_mul]
      congr 1
      ring

structure A2Pairing (θ δ : Fin τ.rank → ℤ) : Prop where
  norm : iform θ θ = iform δ δ
  pos : 0 < iform θ θ
  cross : 2 * iform θ δ = -iform θ θ

theorem A2Pairing.exponents (h : A2Pairing θ δ) :
    2 * iform θ θ / iform θ θ = 2 ∧ 2 * iform δ θ / iform δ δ = -1 ∧
      2 * iform θ δ / iform θ θ = -1 ∧ 2 * iform δ δ / iform δ δ = 2 := by
  have h1 : iform θ θ ≠ 0 := h.pos.ne'
  have h2 : iform δ δ ≠ 0 := h.norm ▸ h1
  have h3 : 2 * iform δ θ = -iform δ δ := by rw [iform_comm, h.cross, h.norm]
  refine ⟨Int.ediv_eq_of_eq_mul_left h1 (by ring), Int.ediv_eq_of_eq_mul_left h2 (by rw [h3]; ring),
    Int.ediv_eq_of_eq_mul_left h1 (by rw [h.cross]; ring),
    Int.ediv_eq_of_eq_mul_left h2 (by ring)⟩

theorem torusPair_conj_theta (hθ : IsRoot τ θ) (hδ : IsRoot τ δ) (h : A2Pairing θ δ)
    (a b : kˣ) (x : k) :
    torusPair k θ δ a b * pinnedX τ k θ x * (torusPair k θ δ a b)⁻¹ =
      pinnedX τ k θ (((a ^ 2 * b⁻¹ : kˣ) : k) * x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.exponents
  rw [torusPair_conj hθ hδ hθ (n := 2) (m := -1) h1 h2]
  simp

theorem torusPair_conj_neg_theta (hθ : IsRoot τ θ) (hδ : IsRoot τ δ) (h : A2Pairing θ δ)
    (a b : kˣ) (x : k) :
    torusPair k θ δ a b * pinnedX τ k (-θ) x * (torusPair k θ δ a b)⁻¹ =
      pinnedX τ k (-θ) ((((a ^ 2 * b⁻¹)⁻¹ : kˣ) : k) * x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.exponents
  have h1' : iform θ θ ≠ 0 := h.pos.ne'
  have h2' : iform δ δ ≠ 0 := h.norm ▸ h1'
  rw [torusPair_conj hθ hδ (IsRoot.neg hθ) (n := -2) (m := 1)
    (Int.ediv_eq_of_eq_mul_left h1' (by rw [iform_neg_right]; ring))
    (Int.ediv_eq_of_eq_mul_left h2' (by
      rw [iform_neg_right, iform_comm δ θ]; linarith [h.cross, h.norm]))]
  simp [mul_comm]

theorem torusPair_conj_delta (hθ : IsRoot τ θ) (hδ : IsRoot τ δ) (h : A2Pairing θ δ)
    (a b : kˣ) (x : k) :
    torusPair k θ δ a b * pinnedX τ k δ x * (torusPair k θ δ a b)⁻¹ =
      pinnedX τ k δ (((a⁻¹ * b ^ 2 : kˣ) : k) * x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.exponents
  rw [torusPair_conj hθ hδ hδ (n := -1) (m := 2) h3 h4]
  simp

theorem torusPair_conj_neg_delta (hθ : IsRoot τ θ) (hδ : IsRoot τ δ) (h : A2Pairing θ δ)
    (a b : kˣ) (x : k) :
    torusPair k θ δ a b * pinnedX τ k (-δ) x * (torusPair k θ δ a b)⁻¹ =
      pinnedX τ k (-δ) ((((a⁻¹ * b ^ 2)⁻¹ : kˣ) : k) * x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.exponents
  have h1' : iform θ θ ≠ 0 := h.pos.ne'
  have h2' : iform δ δ ≠ 0 := h.norm ▸ h1'
  rw [torusPair_conj hθ hδ (IsRoot.neg hδ) (n := 1) (m := -2)
    (Int.ediv_eq_of_eq_mul_left h1' (by rw [iform_neg_right]; linarith [h.cross]))
    (Int.ediv_eq_of_eq_mul_left h2' (by rw [iform_neg_right]; ring))]
  simp [mul_comm]

end TorusElement

section Modification

variable {τ : Tag} {k : Type} [Field k] {θ δ : Fin τ.rank → ℤ}

theorem exists_torusMod (hθ : IsRoot τ θ) (hδ : IsRoot τ δ) (hpair : A2Pairing θ δ) (p : ℕ)
    [Fact p.Prime] [CharP k p] [IsAlgClosed k] (e : ℕ)
    {Λ₀ Λ₁ Λ₂ Λ₃ κ₀ κ₂ : k} (h01 : Λ₀ * Λ₁ = 1) (h23 : Λ₂ * Λ₃ = 1) (hκ₀ : κ₀ * κ₀ = 1)
    (hκ₂ : κ₂ * κ₂ = 1) :
    ∃ t : ModGL τ k, t ∈ torusGroup τ k ∧ ∀ u u' : ModGL τ k,
      u' = entrywiseFrobGL τ k p e t * u * t⁻¹ →
      (∀ x : k, u * pinnedX τ k θ x * u⁻¹ = pinnedX τ k (-θ) (Λ₀ * x)) →
      (∀ x : k, u * pinnedX τ k (-θ) x * u⁻¹ = pinnedX τ k θ (Λ₁ * x)) →
      (∀ x : k, u * pinnedX τ k δ x * u⁻¹ = pinnedX τ k (-δ) (Λ₂ * x)) →
      (∀ x : k, u * pinnedX τ k (-δ) x * u⁻¹ = pinnedX τ k δ (Λ₃ * x)) →
      (∀ x : k, u' * pinnedX τ k θ x * u'⁻¹ = pinnedX τ k (-θ) (κ₀ * x)) ∧
      (∀ x : k, u' * pinnedX τ k (-θ) x * u'⁻¹ = pinnedX τ k θ (κ₀ * x)) ∧
      (∀ x : k, u' * pinnedX τ k δ x * u'⁻¹ = pinnedX τ k (-δ) (κ₂ * x)) ∧
      (∀ x : k, u' * pinnedX τ k (-δ) x * u'⁻¹ = pinnedX τ k δ (κ₂ * x)) := by
  have hΛ₀ : Λ₀ ≠ 0 := fun h => by simp [h] at h01
  have hΛ₂ : Λ₂ ≠ 0 := fun h => by simp [h] at h23
  have hκ₀0 : κ₀ ≠ 0 := fun h => by simp [h] at hκ₀
  have hκ₂0 : κ₂ ≠ 0 := fun h => by simp [h] at hκ₂
  obtain ⟨a, b, ha, hb⟩ := exists_torus_pow (Units.mk0 (Λ₀ * κ₀) (mul_ne_zero hΛ₀ hκ₀0))
    (Units.mk0 (Λ₂ * κ₂) (mul_ne_zero hΛ₂ hκ₂0)) (n := p ^ e + 1) (Nat.succ_pos _)
  refine ⟨torusPair k θ δ a b, torusPair_mem_torusGroup hθ hδ a b,
    fun u u' hu' h₀ h₁ h₂ h₃ => ?_⟩
  have hχ₁ : (((a ^ 2 * b⁻¹ : kˣ) : k)) ^ (p ^ e + 1) = Λ₀ * κ₀ := by
    have := congrArg Units.val ha
    simpa using this
  have hχ₂ : (((a⁻¹ * b ^ 2 : kˣ) : k)) ^ (p ^ e + 1) = Λ₂ * κ₂ := by
    have := congrArg Units.val hb
    simpa using this
  obtain ⟨u₁, u₂⟩ := torusMod_pair p e (t := torusPair k θ δ a b) hu'
    (torusPair_conj_theta hθ hδ hpair a b) (torusPair_conj_neg_theta hθ hδ hpair a b) h₀ h₁ hχ₁
    h01 hκ₀
  obtain ⟨u₃, u₄⟩ := torusMod_pair p e (t := torusPair k θ δ a b) hu'
    (torusPair_conj_delta hθ hδ hpair a b) (torusPair_conj_neg_delta hθ hδ hpair a b) h₂ h₃ hχ₂
    h23 hκ₂
  exact ⟨u₁, u₂, u₃, u₄⟩

end Modification

section Compat

variable {τ : Tag} {θ δ : Fin τ.rank → ℤ} {k : Type} [Field k] {K₂ : Type} [Field K₂]

theorem conj_iota_eq_tau (E : A2Embedding τ θ δ K₂) (j : K₂ →+* k)
    {u' : ModGL τ k} {κ₀ κ₂ : k}
    (h₀ : ∀ x : k, u' * pinnedX τ k θ x * u'⁻¹ = pinnedX τ k (-θ) (κ₀ * x))
    (h₁ : ∀ x : k, u' * pinnedX τ k (-θ) x * u'⁻¹ = pinnedX τ k θ (κ₀ * x))
    (h₂ : ∀ x : k, u' * pinnedX τ k δ x * u'⁻¹ = pinnedX τ k (-δ) (κ₂ * x))
    (h₃ : ∀ x : k, u' * pinnedX τ k (-δ) x * u'⁻¹ = pinnedX τ k δ (κ₂ * x))
    (hκ₀ : κ₀ = -(j E.m₁ * j E.m₀)) (hκ₂ : κ₂ = -(j E.m₃ * j E.m₂)) (y : SL(3, K₂)) :
    u' * baseChangeGL j (E.ι y) * u'⁻¹ = baseChangeGL j (E.ι (sl3Tau K₂ y)) := by
  have sq : ∀ {m : K₂}, m * m = 1 → j m * j m = 1 := fun {m} h => by
    rw [← map_mul, h, map_one]
  have s₀ := sq E.sq₀
  have s₁ := sq E.sq₁
  have s₂ := sq E.sq₂
  have s₃ := sq E.sq₃
  have key := hom_ext_sl3_tv (H := ModGL τ k)
    (f := (MulAut.conj u').toMonoidHom.comp ((baseChangeGL j).comp E.ι))
    (g := ((baseChangeGL j).comp E.ι).comp (sl3Tau K₂)) (fun c => ?_) (fun c => ?_)
    (fun c => ?_) (fun c => ?_)
  · exact DFunLike.congr_fun key y
  · change u' * baseChangeGL j (E.ι (tv 0 1 c)) * u'⁻¹ =
      baseChangeGL j (E.ι (sl3Tau K₂ (tv 0 1 c)))
    rw [sl3Tau_tv 0 1 (by decide), E.h01, E.h10, baseChangeGL_pinnedX, baseChangeGL_pinnedX, h₀]
    congr 1
    simp only [map_mul, map_neg]
    rw [hκ₀]
    linear_combination (-(j E.m₁ * j c)) * s₀
  · change u' * baseChangeGL j (E.ι (tv 1 0 c)) * u'⁻¹ =
      baseChangeGL j (E.ι (sl3Tau K₂ (tv 1 0 c)))
    rw [sl3Tau_tv 1 0 (by decide), E.h10, E.h01, baseChangeGL_pinnedX, baseChangeGL_pinnedX, h₁]
    congr 1
    simp only [map_mul, map_neg]
    rw [hκ₀]
    linear_combination (-(j E.m₀ * j c)) * s₁
  · change u' * baseChangeGL j (E.ι (tv 1 2 c)) * u'⁻¹ =
      baseChangeGL j (E.ι (sl3Tau K₂ (tv 1 2 c)))
    rw [sl3Tau_tv 1 2 (by decide), E.h12, E.h21, baseChangeGL_pinnedX, baseChangeGL_pinnedX, h₂]
    congr 1
    simp only [map_mul, map_neg]
    rw [hκ₂]
    linear_combination (-(j E.m₃ * j c)) * s₂
  · change u' * baseChangeGL j (E.ι (tv 2 1 c)) * u'⁻¹ =
      baseChangeGL j (E.ι (sl3Tau K₂ (tv 2 1 c)))
    rw [sl3Tau_tv 2 1 (by decide), E.h21, E.h12, baseChangeGL_pinnedX, baseChangeGL_pinnedX, h₃]
    congr 1
    simp only [map_mul, map_neg]
    rw [hκ₂]
    linear_combination (-(j E.m₂ * j c)) * s₃

end Compat

end CFSG.ClassicalInvolution.ModelFacts.Levi

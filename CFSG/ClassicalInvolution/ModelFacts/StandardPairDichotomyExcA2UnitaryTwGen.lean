module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryHom

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg Matrix
open scoped MatrixGroups

section Cocycle

variable {τ : Tag} {θ δ : Fin τ.rank → ℤ} {J : Set (Fin τ.rank)} {k : Type} [Field k]

theorem cocycle_conj_pinnedX_of_comm (hk : ringChar k ≠ 2)
    (hθ : IsRoot τ θ) (hδ : IsRoot τ δ) {u m d n : ModGL τ k}
    (hud : d * u = u * d) (hm : m ∈ parabolicLevi τ k J) (hn : n ∈ parabolicLevi τ k J)
    (hcoc : u = m * rootSL2 τ k θ WSL)
    (hνd : d * (n * rootSL2 τ k θ WSL) = (n * rootSL2 τ k θ WSL) * d)
    (hμ₀ : ∃ μ : kˣ, ∀ c : k, (n * rootSL2 τ k θ WSL) * pinnedX τ k θ c *
      (n * rootSL2 τ k θ WSL)⁻¹ = pinnedX τ k (-θ) (μ * c))
    (hμ₁ : ∃ μ : kˣ, ∀ c : k, (n * rootSL2 τ k θ WSL) * pinnedX τ k (-θ) c *
      (n * rootSL2 τ k θ WSL)⁻¹ = pinnedX τ k θ (μ * c))
    (hμ₂ : ∃ μ : kˣ, ∀ c : k, (n * rootSL2 τ k θ WSL) * pinnedX τ k δ c *
      (n * rootSL2 τ k θ WSL)⁻¹ = pinnedX τ k (-δ) (μ * c))
    (hμ₃ : ∃ μ : kˣ, ∀ c : k, (n * rootSL2 τ k θ WSL) * pinnedX τ k (-δ) c *
      (n * rootSL2 τ k θ WSL)⁻¹ = pinnedX τ k δ (μ * c))
    (hdiag : ∀ s ∈ parabolicLevi τ k J, d * s = s * d →
      s ∈ diagActSubgroup τ k {θ, -θ, δ, -δ}) :
    ∃ Λ₀ Λ₁ Λ₂ Λ₃ : k, Λ₀ * Λ₁ = 1 ∧ Λ₂ * Λ₃ = 1 ∧
      (∀ x : k, u * pinnedX τ k θ x * u⁻¹ = pinnedX τ k (-θ) (Λ₀ * x)) ∧
      (∀ x : k, u * pinnedX τ k (-θ) x * u⁻¹ = pinnedX τ k θ (Λ₁ * x)) ∧
      (∀ x : k, u * pinnedX τ k δ x * u⁻¹ = pinnedX τ k (-δ) (Λ₂ * x)) ∧
      (∀ x : k, u * pinnedX τ k (-δ) x * u⁻¹ = pinnedX τ k δ (Λ₃ * x)) := by
  set ν := n * rootSL2 τ k θ WSL with hν
  have hdν : d * ν⁻¹ = ν⁻¹ * d :=
    calc d * ν⁻¹ = ν⁻¹ * (ν * d) * ν⁻¹ := by group
      _ = ν⁻¹ * (d * ν) * ν⁻¹ := by rw [hνd]
      _ = ν⁻¹ * d := by group
  set s₀ := u * ν⁻¹ with hs₀
  have hs₀m : s₀ = m * n⁻¹ := by
    rw [hs₀, hcoc, hν]
    group
  have hs₀J : s₀ ∈ parabolicLevi τ k J := by
    rw [hs₀m]
    exact mul_mem hm (inv_mem hn)
  have hs₀d : d * s₀ = s₀ * d :=
    calc d * (u * ν⁻¹) = (d * u) * ν⁻¹ := by group
      _ = (u * d) * ν⁻¹ := by rw [hud]
      _ = u * (d * ν⁻¹) := by group
      _ = u * (ν⁻¹ * d) := by rw [hdν]
      _ = (u * ν⁻¹) * d := by group
  obtain ⟨a₀, ha₀⟩ := hdiag s₀ hs₀J hs₀d
  have hsν : u = s₀ * ν := by rw [hs₀]; group
  have hθ' := IsRoot.neg hθ
  have hδ' := IsRoot.neg hδ
  obtain ⟨μ₀, hμ₀⟩ := hμ₀
  obtain ⟨μ₁, hμ₁⟩ := hμ₁
  obtain ⟨μ₂, hμ₂⟩ := hμ₂
  obtain ⟨μ₃, hμ₃⟩ := hμ₃
  have e1 : (μ₀ : k) * (μ₁ : k) = 1 :=
    scalar_inv_of_conj_swap hk hθ μ₁.ne_zero hμ₀ hμ₁
  have e2 : (μ₂ : k) * (μ₃ : k) = 1 :=
    scalar_inv_of_conj_swap hk hδ μ₃.ne_zero hμ₂ hμ₃
  have act : ∀ {γ γ' : Fin τ.rank → ℤ} {μ : kˣ}, IsRoot τ γ →
      γ' ∈ ({θ, -θ, δ, -δ} : Set (Fin τ.rank → ℤ)) → IsRoot τ γ' →
      (∀ x : k, ν * pinnedX τ k γ x * ν⁻¹ = pinnedX τ k γ' (μ * x)) →
        ∀ x : k, u * pinnedX τ k γ x * u⁻¹ =
          pinnedX τ k γ' ((rootChar a₀ γ' : k) * (μ * x)) := by
    intro γ γ' μ _ hγ' hr' h x
    calc u * pinnedX τ k γ x * u⁻¹ =
        s₀ * (ν * pinnedX τ k γ x * ν⁻¹) * s₀⁻¹ := by rw [hsν]; group
      _ = _ := by rw [h x, ha₀ γ' hγ' hr']
  refine ⟨(rootChar a₀ (-θ) : k) * μ₀, (rootChar a₀ θ : k) * μ₁,
    (rootChar a₀ (-δ) : k) * μ₂, (rootChar a₀ δ : k) * μ₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := rootChar_neg' a₀ θ
    calc (rootChar a₀ (-θ) : k) * μ₀ * ((rootChar a₀ θ : k) * μ₁) =
        ((rootChar a₀ (-θ) * rootChar a₀ θ : kˣ) : k) * (μ₀ * μ₁) := by
          push_cast; ring
      _ = 1 := by rw [this, inv_mul_cancel, Units.val_one, e1, one_mul]
  · have := rootChar_neg' a₀ δ
    calc (rootChar a₀ (-δ) : k) * μ₂ * ((rootChar a₀ δ : k) * μ₃) =
        ((rootChar a₀ (-δ) * rootChar a₀ δ : kˣ) : k) * (μ₂ * μ₃) := by
          push_cast; ring
      _ = 1 := by rw [this, inv_mul_cancel, Units.val_one, e2, one_mul]
  · intro x
    rw [act hθ (Or.inr (Or.inl rfl)) hθ' hμ₀ x, mul_assoc]
  · intro x
    rw [act hθ' (Or.inl rfl) hθ hμ₁ x, mul_assoc]
  · intro x
    rw [act hδ (Or.inr (Or.inr (Or.inr rfl))) hδ' hμ₂ x, mul_assoc]
  · intro x
    rw [act hδ' (Or.inr (Or.inr (Or.inl rfl))) hδ hμ₃ x, mul_assoc]

end Cocycle

section FrobAct

variable {τ : Tag} {k : Type} [Field k]

structure A2FrobAct (F : ModGL τ k →* ModGL τ k) (q : ℕ) (θ δ : Fin τ.rank → ℤ) : Prop where
  θ_pos : ∀ x : k, F (pinnedX τ k θ x) = pinnedX τ k θ (x ^ q)
  θ_neg : ∀ x : k, F (pinnedX τ k (-θ) x) = pinnedX τ k (-θ) (x ^ q)
  δ_pos : ∀ x : k, F (pinnedX τ k δ x) = pinnedX τ k δ (x ^ q)
  δ_neg : ∀ x : k, F (pinnedX τ k (-δ) x) = pinnedX τ k (-δ) (x ^ q)

theorem frobenius_conj_scalar_F [IsAlgClosed k] (F : ModGL τ k →* ModGL τ k) {q : ℕ} (hq : 0 < q)
    {γ : Fin τ.rank → ℤ} (hF : ∀ x : k, F (pinnedX τ k γ x) = pinnedX τ k γ (x ^ q))
    {t : ModGL τ k} {c : k}
    (h : ∀ x : k, t * pinnedX τ k γ x * t⁻¹ = pinnedX τ k γ (c * x)) (x : k) :
    F t * pinnedX τ k γ x * (F t)⁻¹ = pinnedX τ k γ (c ^ q * x) := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq x hq
  have := congrArg F (h y)
  rw [map_mul, map_mul, map_inv, hF, hF, mul_pow, hy] at this
  exact this

theorem torusMod_pair_F [IsAlgClosed k] (F : ModGL τ k →* ModGL τ k) {q : ℕ} (hq : 0 < q)
    {γ : Fin τ.rank → ℤ} {t u u' : ModGL τ k} {χ : kˣ} {Λ Λ' κ : k}
    (hF₁ : ∀ x : k, F (pinnedX τ k γ x) = pinnedX τ k γ (x ^ q))
    (hF₂ : ∀ x : k, F (pinnedX τ k (-γ) x) = pinnedX τ k (-γ) (x ^ q))
    (hu' : u' = F t * u * t⁻¹)
    (ht₁ : ∀ x : k, t * pinnedX τ k γ x * t⁻¹ = pinnedX τ k γ ((χ : k) * x))
    (ht₂ : ∀ x : k, t * pinnedX τ k (-γ) x * t⁻¹ =
      pinnedX τ k (-γ) (((χ⁻¹ : kˣ) : k) * x))
    (hu₁ : ∀ x : k, u * pinnedX τ k γ x * u⁻¹ = pinnedX τ k (-γ) (Λ * x))
    (hu₂ : ∀ x : k, u * pinnedX τ k (-γ) x * u⁻¹ = pinnedX τ k γ (Λ' * x))
    (hχ : (χ : k) ^ (q + 1) = Λ * κ) (hΛ : Λ * Λ' = 1) (hκ : κ * κ = 1) :
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
  have f₁ := frobenius_conj_scalar_F F hq hF₁ ht₁
  have f₂ := frobenius_conj_scalar_F F hq hF₂ ht₂
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

theorem exists_torusMod_F [IsAlgClosed k] {θ δ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hδ : IsRoot τ δ) (hpair : A2Pairing θ δ) (F : ModGL τ k →* ModGL τ k) {q : ℕ} (hq : 0 < q)
    (hF : A2FrobAct F q θ δ) {Λ₀ Λ₁ Λ₂ Λ₃ κ₀ κ₂ : k} (h01 : Λ₀ * Λ₁ = 1) (h23 : Λ₂ * Λ₃ = 1)
    (hκ₀ : κ₀ * κ₀ = 1) (hκ₂ : κ₂ * κ₂ = 1) :
    ∃ t : ModGL τ k, t ∈ torusGroup τ k ∧ ∀ u u' : ModGL τ k,
      u' = F t * u * t⁻¹ →
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
    (Units.mk0 (Λ₂ * κ₂) (mul_ne_zero hΛ₂ hκ₂0)) (n := q + 1) (Nat.succ_pos _)
  refine ⟨torusPair k θ δ a b, torusPair_mem_torusGroup hθ hδ a b,
    fun u u' hu' h₀ h₁ h₂ h₃ => ?_⟩
  have hχ₁ : (((a ^ 2 * b⁻¹ : kˣ) : k)) ^ (q + 1) = Λ₀ * κ₀ := by
    have := congrArg Units.val ha
    simpa using this
  have hχ₂ : (((a⁻¹ * b ^ 2 : kˣ) : k)) ^ (q + 1) = Λ₂ * κ₂ := by
    have := congrArg Units.val hb
    simpa using this
  obtain ⟨u₁, u₂⟩ := torusMod_pair_F F hq (t := torusPair k θ δ a b) hF.θ_pos hF.θ_neg hu'
    (torusPair_conj_theta hθ hδ hpair a b) (torusPair_conj_neg_theta hθ hδ hpair a b) h₀ h₁ hχ₁
    h01 hκ₀
  obtain ⟨u₃, u₄⟩ := torusMod_pair_F F hq (t := torusPair k θ δ a b) hF.δ_pos hF.δ_neg hu'
    (torusPair_conj_delta hθ hδ hpair a b) (torusPair_conj_neg_delta hθ hδ hpair a b) h₂ h₃ hχ₂
    h23 hκ₂
  exact ⟨u₁, u₂, u₃, u₄⟩

end FrobAct

section FrobIota

variable {τ : Tag} {θ δ : Fin τ.rank → ℤ} {k : Type} [Field k] {K₂ : Type} [Field K₂]

theorem frob_baseChange_iota_F (F : ModGL τ k →* ModGL τ k) {q : ℕ} (hq : Odd q)
    (hF : A2FrobAct F q θ δ) (E : A2Embedding τ θ δ K₂) (j : K₂ →+* k) (σ : K₂ →+* K₂)
    (hσ : ∀ x, j (σ x) = j x ^ q) (z : SL(3, K₂)) :
    F (baseChangeGL j (E.ι z)) = baseChangeGL j (E.ι (Matrix.SpecialLinearGroup.map σ z)) := by
  have hm : ∀ {m : K₂}, m * m = 1 → j m ^ q = j m := fun {m} h => by
    rcases mul_self_eq_one_iff.1 h with rfl | rfl
    · simp
    · simp [hq.neg_pow]
  have key := hom_ext_sl3_tv (H := ModGL τ k)
    (f := F.comp ((baseChangeGL j).comp E.ι))
    (g := ((baseChangeGL j).comp E.ι).comp (Matrix.SpecialLinearGroup.map σ))
    (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun c => ?_)
  · exact DFunLike.congr_fun key z
  · change F (baseChangeGL j (E.ι (tv 0 1 c))) =
      baseChangeGL j (E.ι (Matrix.SpecialLinearGroup.map σ (tv 0 1 c)))
    rw [specialLinear_map_tv, E.h01, E.h01, baseChangeGL_pinnedX, baseChangeGL_pinnedX,
      hF.θ_pos, map_mul, map_mul, hσ, mul_pow, hm E.sq₀]
  · change F (baseChangeGL j (E.ι (tv 1 0 c))) =
      baseChangeGL j (E.ι (Matrix.SpecialLinearGroup.map σ (tv 1 0 c)))
    rw [specialLinear_map_tv, E.h10, E.h10, baseChangeGL_pinnedX, baseChangeGL_pinnedX,
      hF.θ_neg, map_mul, map_mul, hσ, mul_pow, hm E.sq₁]
  · change F (baseChangeGL j (E.ι (tv 1 2 c))) =
      baseChangeGL j (E.ι (Matrix.SpecialLinearGroup.map σ (tv 1 2 c)))
    rw [specialLinear_map_tv, E.h12, E.h12, baseChangeGL_pinnedX, baseChangeGL_pinnedX,
      hF.δ_pos, map_mul, map_mul, hσ, mul_pow, hm E.sq₂]
  · change F (baseChangeGL j (E.ι (tv 2 1 c))) =
      baseChangeGL j (E.ι (Matrix.SpecialLinearGroup.map σ (tv 2 1 c)))
    rw [specialLinear_map_tv, E.h21, E.h21, baseChangeGL_pinnedX, baseChangeGL_pinnedX,
      hF.δ_neg, map_mul, map_mul, hσ, mul_pow, hm E.sq₃]

theorem frob_alpha_F (F : ModGL τ k →* ModGL τ k) {q : ℕ} (hq : Odd q) (hF : A2FrobAct F q θ δ)
    (E : A2Embedding τ θ δ K₂) (j : K₂ →+* k) (σ : K₂ →+* K₂) (hσ : ∀ x, j (σ x) = j x ^ q)
    {v' u' : ModGL τ k} (hu' : F v' = u' * v')
    (hτ : ∀ y : SL(3, K₂), u' * baseChangeGL j (E.ι y) * u'⁻¹ =
      baseChangeGL j (E.ι (sl3Tau K₂ y)))
    {y : SL(3, K₂)} (hy : Matrix.SpecialLinearGroup.map σ y = sl3Tau K₂ y) :
    F (v'⁻¹ * baseChangeGL j (E.ι y) * v') = v'⁻¹ * baseChangeGL j (E.ι y) * v' := by
  rw [map_mul, map_mul, map_inv, hu', frob_baseChange_iota_F F hq hF E j σ hσ, hy]
  have h := hτ y
  calc (u' * v')⁻¹ * baseChangeGL j (E.ι (sl3Tau K₂ y)) * (u' * v') =
      v'⁻¹ * (u'⁻¹ * baseChangeGL j (E.ι (sl3Tau K₂ y)) * u') * v' := by group
    _ = _ := by
      rw [← h]
      group

end FrobIota

section Alpha

variable {p e : ℕ} [Fact p.Prime]

theorem exists_unitary_alpha_F {τ : Tag} {θ δ : Fin τ.rank → ℤ} {L k : Type} [Field L] [Finite L]
    [CharP L p] [Field k] [IsAlgClosed k] (hp2 : p ≠ 2) (hθ : IsRoot τ θ) (hδ : IsRoot τ δ)
    (hpair : A2Pairing θ δ) (Em : A2Embedding τ θ δ L) (j : L →+* k)
    (F : ModGL τ k →* ModGL τ k) (hF : A2FrobAct F (p ^ e) θ δ)
    {c v d : ModGL τ k} (hd : v * c * v⁻¹ = d)
    (hcocycle : ∃ Λ₀ Λ₁ Λ₂ Λ₃ : k, Λ₀ * Λ₁ = 1 ∧ Λ₂ * Λ₃ = 1 ∧
      (∀ x : k, (F v * v⁻¹) * pinnedX τ k θ x * (F v * v⁻¹)⁻¹ = pinnedX τ k (-θ) (Λ₀ * x)) ∧
      (∀ x : k, (F v * v⁻¹) * pinnedX τ k (-θ) x * (F v * v⁻¹)⁻¹ = pinnedX τ k θ (Λ₁ * x)) ∧
      (∀ x : k, (F v * v⁻¹) * pinnedX τ k δ x * (F v * v⁻¹)⁻¹ = pinnedX τ k (-δ) (Λ₂ * x)) ∧
      (∀ x : k, (F v * v⁻¹) * pinnedX τ k (-δ) x * (F v * v⁻¹)⁻¹ = pinnedX τ k δ (Λ₃ * x)))
    (hdt : ∀ t ∈ torusGroup τ k, d * t = t * d)
    (hvadj : ∀ t ∈ torusGroup τ k, t * v ∈ adjointGroup τ k)
    (hvconj : ∀ t ∈ torusGroup τ k, ∀ A : SL2 k, ∃ A' : SL2 k,
      (t * v)⁻¹ * rootSL2 τ k θ A * (t * v) = rootSL2 τ k θ A')
    (hsign : baseChangeGL j (rootSL2 τ L δ (HSL (-1 : Lˣ))) = d) :
    ∃ α : Su L p e 3 →* ModGL τ k, Function.Injective α ∧
      (∀ y, α y ∈ adjointGroup τ k) ∧ (∀ y, F (α y) = α y) ∧
      (∀ A : Su L p e 2, ∃ A' : SL2 k,
        α (embSUid (unitaryInvolution L p e) 2 A) = rootSL2 τ k θ A') ∧
      α (embSUid (unitaryInvolution L p e) 0 (suNegOne L p e)) = c := by
  classical
  have hE2 : ringChar L ≠ 2 := by
    rw [ringChar.eq L p]
    exact hp2
  have hodd : Odd (p ^ e) := (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hpos : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hj : ∀ x : L, j (unitaryInvolution L p e x) = j x ^ p ^ e := fun x => by
    rw [unitaryInvolution_apply, map_pow]
  obtain ⟨Λ₀, Λ₁, Λ₂, Λ₃, e1, e2, a0, a1, a2, a3⟩ := hcocycle
  have sq : ∀ {x : L}, x * x = 1 → j x * j x = 1 := fun {x} h => by
    rw [← map_mul, h, map_one]
  have s₀ := sq Em.sq₀
  have s₁ := sq Em.sq₁
  have s₂ := sq Em.sq₂
  have s₃ := sq Em.sq₃
  have hκ₀ : (-(j Em.m₁ * j Em.m₀)) * (-(j Em.m₁ * j Em.m₀)) = 1 := by
    linear_combination (j Em.m₁ * j Em.m₁) * s₀ + s₁
  have hκ₂ : (-(j Em.m₃ * j Em.m₂)) * (-(j Em.m₃ * j Em.m₂)) = 1 := by
    linear_combination (j Em.m₃ * j Em.m₃) * s₂ + s₃
  obtain ⟨t, ht, hmod⟩ := exists_torusMod_F hθ hδ hpair F hpos hF e1 e2 hκ₀ hκ₂
  set v' := t * v with hv'def
  set u := F v * v⁻¹ with hu
  set u' := F t * u * t⁻¹ with hu'
  obtain ⟨b₀, b₁, b₂, b₃⟩ := hmod u u' rfl a0 a1 a2 a3
  have hτ := conj_iota_eq_tau Em j b₀ b₁ b₂ b₃ rfl rfl
  have hv'adj : v' ∈ adjointGroup τ k := hvadj t ht
  have hd' : v' * c * v'⁻¹ = d := by
    have hcomm : d * t = t * d := hdt t ht
    calc v' * c * v'⁻¹ = t * (v * c * v⁻¹) * t⁻¹ := by rw [hv'def]; group
      _ = t * d * t⁻¹ := by rw [hd]
      _ = d := by rw [← hcomm]; group
  have hFv' : F v' = u' * v' := by
    rw [hv'def, map_mul]
    have : F v = u * v := by rw [hu]; group
    rw [this, hu']
    group
  let α : Su L p e 3 →* ModGL τ k :=
    (MulAut.conj v'⁻¹).toMonoidHom.comp (((baseChangeGL j).comp Em.ι).comp
      (suToSL (unitaryInvolution L p e) 3))
  have hα : ∀ y, α y = v'⁻¹ * baseChangeGL j (Em.ι (suToSL (unitaryInvolution L p e) 3 y)) * v' :=
    fun y => by simp [α]
  have hαF : ∀ y, F (α y) = α y := fun y => by
    rw [hα]
    exact frob_alpha_F F hodd hF Em j
      ((unitaryInvolution L p e : L ≃+* L) : L →+* L) hj hFv' hτ (map_suToSL_eq_tau y)
  refine ⟨α, ?_, ?_, hαF, ?_, ?_⟩
  · intro y₁ y₂ h
    rw [hα, hα] at h
    have h2 := mul_left_cancel (mul_right_cancel h)
    exact suToSL_injective (Em.inj (baseChangeGL_injective j h2))
  · intro y
    rw [hα]
    exact mul_mem (mul_mem (inv_mem hv'adj) (baseChangeGL_mem_adjointGroup j (Em.mem _))) hv'adj
  · intro A
    have h3 : suToSL (unitaryInvolution L p e) 3
        (embSUid (unitaryInvolution L p e) 2 A) =
        blk L 0 (suToSL (unitaryInvolution L p e) 2 A) := by
      rw [embSUid_two_eq_blockEmb, suToSL_blockEmb]
      rfl
    obtain ⟨B₁, hB₁⟩ := Em.blk_zero_mem hθ (suToSL (unitaryInvolution L p e) 2 A)
    obtain ⟨A', hA'⟩ := hvconj t ht (Matrix.SpecialLinearGroup.map j B₁)
    exact ⟨A', by rw [hα, h3, ← hB₁, baseChangeGL_rootSL2', hA']⟩
  · have h3 : suToSL (unitaryInvolution L p e) 3
        (embSUid (unitaryInvolution L p e) 0 (suNegOne L p e)) =
        blk L 1 (HSL (-1 : Lˣ)) := by
      rw [embSUid_zero_eq_blockEmb, suToSL_blockEmb, suToSL_suNegOne]
      rfl
    rw [hα, h3, Em.blk_one_neg_one hE2 hδ, hsign]
    calc v'⁻¹ * d * v' = v'⁻¹ * (v' * c * v'⁻¹) * v' := by rw [hd']
      _ = c := by group

end Alpha

end CFSG.ClassicalInvolution.ModelFacts.Levi

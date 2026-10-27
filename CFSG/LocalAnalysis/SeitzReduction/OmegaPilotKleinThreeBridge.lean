module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeModel

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Matrix QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply quadMinus quadMinus_apply polar_quadMinus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateMinusIsometry minusIndexEquiv reindexVectorEquiv_symm_apply)

section Bridge

variable {F : Type} [Field F]

@[expose] def bridgeC₀ (b : F) (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) : F :=
  v (.inr (.inl 0)) + v (.inl 0) + b * v (.inl 1)

@[expose] def bridgeC₁ (c : F) (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) : F :=
  v (.inr (.inl 1)) + c * v (.inl 1)

@[expose] def bridgeFun (α α' b c β : F) (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) : Fin 3 ⊕ Fin 3 → F :=
  Sum.elim
    ![v (.inl 0) + v (.inl 1) * α + (bridgeC₀ b v * (1 + α' * β) + bridgeC₁ c v * β),
      bridgeC₀ b v * (1 + α' * β) + bridgeC₁ c v * β,
      v (.inr (.inr 0)) + v (.inr (.inr 1)) * α]
    ![v (.inl 0) + v (.inl 1) * α' + (bridgeC₀ b v * (1 + α * β) + bridgeC₁ c v * β),
      bridgeC₀ b v * (1 + α * β) + bridgeC₁ c v * β,
      v (.inr (.inr 0)) + v (.inr (.inr 1)) * α']

@[expose] def bridgeLin (α α' b c β : F) :
    (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 3 ⊕ Fin 3 → F) where
  toFun := bridgeFun α α' b c β
  map_add' v w := by
    funext s
    rcases s with i | i <;> fin_cases i <;>
      simp [bridgeFun, bridgeC₀, bridgeC₁] <;> ring
  map_smul' a v := by
    funext s
    rcases s with i | i <;> fin_cases i <;>
      simp [bridgeFun, bridgeC₀, bridgeC₁] <;> ring

theorem bridgeLin_apply (α α' b c β : F) (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) :
    bridgeLin α α' b c β v = bridgeFun α α' b c β v :=
  rfl

theorem quadMinus_three_apply (b c : F) (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) :
    quadMinus 3 F b c v = v (.inl 0) * v (.inr (.inl 0)) + v (.inl 1) * v (.inr (.inl 1)) +
      v (.inr (.inr 0)) ^ 2 + b * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
        c * v (.inr (.inr 1)) ^ 2 := by
  rw [quadMinus_apply]
  simp [Fin.sum_univ_two]

section Coords

variable (α α' b c β : F) (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F)

theorem bridgeFun_inl_zero : bridgeFun α α' b c β v (.inl 0) =
    v (.inl 0) + v (.inl 1) * α + (bridgeC₀ b v * (1 + α' * β) + bridgeC₁ c v * β) := rfl

theorem bridgeFun_inl_one : bridgeFun α α' b c β v (.inl 1) =
    bridgeC₀ b v * (1 + α' * β) + bridgeC₁ c v * β := rfl

theorem bridgeFun_inl_two : bridgeFun α α' b c β v (.inl 2) =
    v (.inr (.inr 0)) + v (.inr (.inr 1)) * α := rfl

theorem bridgeFun_inr_zero : bridgeFun α α' b c β v (.inr 0) =
    v (.inl 0) + v (.inl 1) * α' + (bridgeC₀ b v * (1 + α * β) + bridgeC₁ c v * β) := rfl

theorem bridgeFun_inr_one : bridgeFun α α' b c β v (.inr 1) =
    bridgeC₀ b v * (1 + α * β) + bridgeC₁ c v * β := rfl

theorem bridgeFun_inr_two : bridgeFun α α' b c β v (.inr 2) =
    v (.inr (.inr 0)) + v (.inr (.inr 1)) * α' := rfl

end Coords

variable [CharP F 2] {α α' b c β : F}

theorem quadPlus_bridgeLin (hs : α + α' = b) (hp : α * α' = c) (hb : b * β = 1)
    (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) :
    quadPlus 3 F (bridgeLin α α' b c β v) = quadMinus 3 F b c v := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [quadPlus_apply, quadMinus_three_apply, bridgeLin_apply, Fin.sum_univ_three,
    bridgeFun_inl_zero, bridgeFun_inl_one, bridgeFun_inl_two, bridgeFun_inr_zero,
    bridgeFun_inr_one, bridgeFun_inr_two, bridgeC₀, bridgeC₁]
  set a₀ := v (.inl 0)
  set a₁ := v (.inl 1)
  set c₀ := v (.inr (.inl 0))
  set c₁ := v (.inr (.inl 1))
  set u := v (.inr (.inr 0))
  set w := v (.inr (.inr 1))
  linear_combination (a₀ * a₁ + a₀ * (c₀ + a₀ + b * a₁) * β +
      a₁ * (c₀ + a₀ + b * a₁) * (1 + (α + α' - b) * β + 2 * b * β) +
      a₁ * (c₁ + c * a₁) * β + u * w) * hs + (a₁ ^ 2 + w ^ 2) * hp +
    (a₀ * (c₀ + a₀ + b * a₁) + a₁ * (c₀ + a₀ + b * a₁) * b + a₁ * (c₁ + c * a₁)) * hb +
    (a₀ ^ 2 + b * a₀ * a₁ + c * a₁ ^ 2 + a₀ * (c₀ + a₀ + b * a₁) + a₀ * (c₁ + c * a₁) * β +
      a₁ * (c₀ + a₀ + b * a₁) * (b - α * α' * β) +
      ((c₀ + a₀ + b * a₁) * (1 + α' * β) + (c₁ + c * a₁) * β) *
        ((c₀ + a₀ + b * a₁) * (1 + α * β) + (c₁ + c * a₁) * β)) * h2

omit [CharP F 2] in
theorem polar_quadMinus_three (h2 : (2 : F) = 0) (v w : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) :
    polar (quadMinus 3 F b c) v w =
      v (.inl 0) * w (.inr (.inl 0)) + w (.inl 0) * v (.inr (.inl 0)) +
        (v (.inl 1) * w (.inr (.inl 1)) + w (.inl 1) * v (.inr (.inl 1))) +
        b * (v (.inr (.inr 0)) * w (.inr (.inr 1)) + w (.inr (.inr 0)) * v (.inr (.inr 1))) := by
  rw [polar_quadMinus]
  simp only [h2, zero_mul, add_zero]
  have e : ∀ f : Fin (3 - 1) → F, ∑ i, f i = f 0 + f 1 := fun f => Fin.sum_univ_two f
  rw [e]

theorem eq_zero_of_forall_polar_quadMinus_three (hb0 : b ≠ 0) {v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F}
    (h : ∀ w, polar (quadMinus 3 F b c) v w = 0) : v = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have key : ∀ s, polar (quadMinus 3 F b c) v (Pi.single s 1) = 0 := fun s => h _
  funext s
  rcases s with i | i | i <;> fin_cases i
  · have := key (.inr (.inl 0))
    rw [polar_quadMinus_three h2] at this
    simpa [Pi.single_apply] using this
  · have := key (.inr (.inl 1))
    rw [polar_quadMinus_three h2] at this
    simpa [Pi.single_apply] using this
  · have := key (.inl 0)
    rw [polar_quadMinus_three h2] at this
    simpa [Pi.single_apply] using this
  · have := key (.inl 1)
    rw [polar_quadMinus_three h2] at this
    simpa [Pi.single_apply] using this
  · have := key (.inr (.inr 1))
    rw [polar_quadMinus_three h2] at this
    simpa [Pi.single_apply, hb0] using this
  · have := key (.inr (.inr 0))
    rw [polar_quadMinus_three h2] at this
    simpa [Pi.single_apply, hb0] using this

theorem bridgeLin_injective (hs : α + α' = b) (hp : α * α' = c) (hb : b * β = 1) :
    Function.Injective (bridgeLin α α' b c β) := by
  have hb0 : b ≠ 0 := left_ne_zero_of_mul_eq_one hb
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  apply eq_zero_of_forall_polar_quadMinus_three hb0
  intro w
  rw [polar, ← quadPlus_bridgeLin hs hp hb, ← quadPlus_bridgeLin hs hp hb,
    ← quadPlus_bridgeLin hs hp hb, map_add, hv, zero_add, QuadraticMap.map_zero]
  ring

@[expose] noncomputable def bridgeIso (hs : α + α' = b) (hp : α * α' = c) (hb : b * β = 1) :
    (quadMinus 3 F b c).IsometryEquiv (quadPlus 3 F) :=
  { LinearEquiv.ofBijective (bridgeLin α α' b c β)
      ⟨bridgeLin_injective hs hp hb,
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1
          (bridgeLin_injective hs hp hb)⟩ with
    map_app' := quadPlus_bridgeLin hs hp hb }

omit [CharP F 2] in
theorem bridgeFun_fieldMap (σ : F ≃+* F) (hσα : σ α = α') (hσα' : σ α' = α) (hσb : σ b = b)
    (hσc : σ c = c) (hσβ : σ β = β) (v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) :
    bridgeFun α α' b c β (fun s => σ (v s)) = fun s => σ (bridgeFun α α' b c β v s.swap) := by
  funext s
  rcases s with i | i <;> fin_cases i <;>
    simp [bridgeFun, bridgeC₀, bridgeC₁, hσα, hσα', hσb, hσc, hσβ]

end Bridge

section MinusKlein

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)

variable {F : Type} [Field F] [CharP F 2] {α α' b c β : F}

@[expose] noncomputable def minusKleinIso (hs : α + α' = b) (hp : α * α' = c) (hb : b * β = 1) :
    (coordinateQuadMinus 3 F (by norm_num) b c).IsometryEquiv (quadPlus 3 F) :=
  (coordinateMinusIsometry 3 F (by norm_num) b c).symm.trans (bridgeIso hs hp hb)

theorem minusKleinIso_apply (hs : α + α' = b) (hp : α * α' = c) (hb : b * β = 1)
    (w : Fin (2 * 3) → F) :
    minusKleinIso hs hp hb w =
      bridgeFun α α' b c β (fun i => w (minusIndexEquiv 3 (by norm_num) i)) :=
  rfl

theorem minusKleinIso_fieldMap (hs : α + α' = b) (hp : α * α' = c) (hb : b * β = 1)
    (σ : F ≃+* F) (hσα : σ α = α') (hσα' : σ α' = α) (hσb : σ b = b) (hσc : σ c = c)
    (hσβ : σ β = β) (w : Fin (2 * 3) → F) :
    minusKleinIso hs hp hb (coordinateFieldMap (2 * 3) σ w) =
      fun s => σ (minusKleinIso hs hp hb w s.swap) := by
  rw [minusKleinIso_apply, minusKleinIso_apply]
  exact bridgeFun_fieldMap σ hσα hσα' hσb hσc hσβ _

variable [Finite F]

@[expose] noncomputable def minusKleinEquiv (hs : α + α' = b) (hp : α * α' = c) (hb : b * β = 1) :
    LinearFlag.projectiveSL 4 F ≃*
      matrixProjectiveDerived (coordinateQuadMinus 3 F (by norm_num) b c) :=
  kleinEquivOf (minusKleinIso hs hp hb)

theorem minusKleinEquiv_graphField (hs : α + α' = b) (hp : α * α' = c) (hb : b * β = 1)
    (σ : F ≃+* F) (hσα : σ α = α') (hσα' : σ α' = α) (hσb : σ b = b) (hσc : σ c = c)
    (hσβ : σ β = β)
    (hQσ : ∀ v, coordinateQuadMinus 3 F (by norm_num) b c (coordinateFieldMap (2 * 3) σ v) =
      σ (coordinateQuadMinus 3 F (by norm_num) b c v))
    (x : LinearFlag.projectiveSL 4 F) :
    minusKleinEquiv hs hp hb ((LinearFlag.fieldAut 4 F σ * LinearFlag.dualAut 4 F) x) =
      fieldAutT (coordinateQuadMinus 3 F (by norm_num) b c) σ hQσ (minusKleinEquiv hs hp hb x) :=
  kleinEquivOf_graphField _ σ (minusKleinIso_fieldMap hs hp hb σ hσα hσα' hσb hσc hσβ) hQσ x

end MinusKlein

end CFSG.SeitzReduction.OmegaPilot

module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.Front.Transport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix

@[expose] def GoodFixedCentral {K : Type} [Group K] (T : Prop) (α : MulAut K) : Prop :=
  ∃ H : Subgroup K, (∀ h ∈ H, α h = h) ∧ (∀ z ∈ Subgroup.center K, z ∈ H) ∧ GoodSub T H

theorem GoodFixedCentral.mono {K : Type} [Group K] {T T' : Prop} (h : T → T') {α : MulAut K}
    (hα : GoodFixedCentral T α) : GoodFixedCentral T' α := by
  obtain ⟨H, h1, h2, h3⟩ := hα
  exact ⟨H, h1, h2, h3.mono h⟩

theorem GoodFixedCentral.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {T : Prop}
    {α : MulAut K} (hα : GoodFixedCentral T α) :
    GoodFixedCentral T (MulAut.congr e α) := by
  obtain ⟨H, h1, h2, h3⟩ := hα
  refine ⟨H.map e.toMonoidHom, ?_, ?_, goodSub_map e.toMonoidHom h3⟩
  · rintro _ ⟨h, hh, rfl⟩
    change e (α (e.symm (e h))) = e h
    rw [MulEquiv.symm_apply_apply, h1 h hh]
  · intro z hz
    refine ⟨e.symm z, h2 _ ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul]
    simpa using hz (e g)

section Native

variable {F : Type} [Field F]

@[expose] def ActsAsConj (S : Subgroup (GL (Fin 4) F)) (β : MulAut ↥S) (ρ : GL (Fin 4) F) : Prop :=
  ∀ k : ↥S, ((β k : ↥S) : GL (Fin 4) F) = ρ * (k : GL (Fin 4) F) * ρ⁻¹

@[expose] def IsReflection (S : Subgroup (GL (Fin 4) F)) (β : MulAut ↥S) : Prop :=
  ∃ ρ : GL (Fin 4) F, ρ * ρ = 1 ∧ (ρ : Matrix (Fin 4) (Fin 4) F).det = -1 ∧ ActsAsConj S β ρ

@[expose] def IsGraphLike (S : Subgroup (GL (Fin 4) F)) (β : MulAut ↥S) : Prop :=
  ∃ g : GL (Fin 4) F,
    ((g : Matrix (Fin 4) (Fin 4) F)ᵀ = (g : Matrix (Fin 4) (Fin 4) F) ∨
      (g : Matrix (Fin 4) (Fin 4) F)ᵀ = -(g : Matrix (Fin 4) (Fin 4) F)) ∧
    ∀ k : ↥S, ((β k : ↥S) : GL (Fin 4) F) =
      g * Matrix.GeneralLinearGroup.inverseTranspose (k : GL (Fin 4) F) * g⁻¹

@[expose] def IsGraphFieldLike (S : Subgroup (GL (Fin 4) F)) (q : ℕ) (β : MulAut ↥S) : Prop :=
  ∃ (bar : F →+* F) (g : GL (Fin 4) F), (∀ x, bar x = x ^ q) ∧
    (∃ c : F, (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F).map bar =
      c • (1 : Matrix (Fin 4) (Fin 4) F)) ∧
    ∀ k : ↥S, ((β k : ↥S) : GL (Fin 4) F) =
      g * Matrix.GeneralLinearGroup.map bar (k : GL (Fin 4) F) * g⁻¹

@[expose] def IsExoticLin (S : Subgroup (GL (Fin 4) F)) (β : MulAut ↥S) : Prop :=
  ∃ g : GL (Fin 4) F,
    (g : Matrix (Fin 4) (Fin 4) F)ᵀ = (g : Matrix (Fin 4) (Fin 4) F) ∧
    ¬ IsSquare (g : Matrix (Fin 4) (Fin 4) F).det ∧
    ∀ k : ↥S, ((β k : ↥S) : GL (Fin 4) F) =
      g * Matrix.GeneralLinearGroup.inverseTranspose (k : GL (Fin 4) F) * g⁻¹

@[expose] def IsExoticUni (S : Subgroup (GL (Fin 4) F)) (q : ℕ) (β : MulAut ↥S) : Prop :=
  ∃ (bar : F →+* F) (g : GL (Fin 4) F), (∀ x, bar x = x ^ q) ∧
    ((g : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ * (g : Matrix (Fin 4) (Fin 4) F) = 1 ∧
    (g : Matrix (Fin 4) (Fin 4) F)ᵀ = (g : Matrix (Fin 4) (Fin 4) F) ∧
    ¬ (∃ u : F, u ^ (q + 1) = 1 ∧ u * u = (g : Matrix (Fin 4) (Fin 4) F).det) ∧
    ∀ k : ↥S, ((β k : ↥S) : GL (Fin 4) F) =
      g * Matrix.GeneralLinearGroup.map bar (k : GL (Fin 4) F) * g⁻¹

end Native

@[expose] def IsReflectionAut {K : Type} [Group K] (α : MulAut K) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (e : K ≃* StatedSL 4 F), Nat.card F % 4 = 3 ∧
    IsReflection (StatedSL 4 F) (MulAut.congr e α)) ∨
  (∃ (q : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (e : K ≃* StatedSU 4 q F),
    Nat.card F = q ^ 2 ∧ q % 4 = 1 ∧ IsReflection (StatedSU 4 q F) (MulAut.congr e α))

@[expose] def IsGraphAut {K : Type} [Group K] (α : MulAut K) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (e : K ≃* StatedSL 4 F), Nat.card F % 4 = 3 ∧
    IsGraphLike (StatedSL 4 F) (MulAut.congr e α)) ∨
  (∃ (q : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (e : K ≃* StatedSU 4 q F),
    Nat.card F = q ^ 2 ∧ q % 4 = 1 ∧ IsGraphFieldLike (StatedSU 4 q F) q (MulAut.congr e α))

@[expose] def S1OuterClassification : Prop :=
  ∀ (K : Type) [Group K], IsSL4Model K → ∀ α : MulAut K, α * α = 1 → (∀ k : K, α ≠ MulAut.conj k) →
    GoodFixedCentral (ThreeModel K) α ∨ IsReflectionAut α ∨ IsGraphAut α

end CFSG.GH74.Generic.S1

module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ETwo
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Five
public import CFSG.LocalAnalysis.EvenBN.Common.ProdFactors

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

section Sections

variable {G : Type*} [Group G]

@[expose] def centralizerSection (X Y : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ normalizer (X : Set G) ∧ g ∈ normalizer (Y : Set G) ∧
    ∀ x ∈ X, x⁻¹ * (g * x * g⁻¹) ∈ Y}
  mul_mem' := by
    rintro a b ⟨haX, haY, ha⟩ ⟨hbX, hbY, hb⟩
    refine ⟨mul_mem haX hbX, mul_mem haY hbY, fun x hx => ?_⟩
    have hx' : b * x * b⁻¹ ∈ X := (mem_normalizer_iff.1 hbX x).1 hx
    have e : x⁻¹ * (a * b * x * (a * b)⁻¹) =
        (x⁻¹ * (b * x * b⁻¹)) * ((b * x * b⁻¹)⁻¹ * (a * (b * x * b⁻¹) * a⁻¹)) := by group
    rw [e]
    exact mul_mem (hb x hx) (ha _ hx')
  one_mem' := ⟨one_mem _, one_mem _, fun x _ => by
    rw [one_mul, inv_one, mul_one, inv_mul_cancel]
    exact one_mem _⟩
  inv_mem' := by
    rintro a ⟨haX, haY, ha⟩
    refine ⟨inv_mem haX, inv_mem haY, fun x hx => ?_⟩
    have hx' : a⁻¹ * x * a⁻¹⁻¹ ∈ X := (mem_normalizer_iff.1 (inv_mem haX) x).1 hx
    have e : x⁻¹ * (a⁻¹ * x * a⁻¹⁻¹) =
        ((a⁻¹ * x * a⁻¹⁻¹)⁻¹ * (a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹))⁻¹ := by group
    rw [e]
    exact inv_mem (ha _ hx')

@[expose] def IsNaturalSection (X A B : Subgroup G) (k : Type*) [Field k] : Prop :=
  ∃ (φ : X ≃* SL(2, k)) (θ : (Fin 2 → k) → G),
    (∀ v, θ v ∈ A) ∧ (∀ v w, (θ v * θ w)⁻¹ * θ (v + w) ∈ B) ∧ (∀ v, θ v ∈ B → v = 0) ∧
      (∀ a ∈ A, ∃ v, (θ v)⁻¹ * a ∈ B) ∧
      ∀ (x : X) (v : Fin 2 → k),
        (θ ((φ x : Matrix (Fin 2) (Fin 2) k).mulVec v))⁻¹ * ((x : G) * θ v * (x : G)⁻¹) ∈ B

end Sections

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K}

@[expose] def B₆ (d : Data G h) : Subgroup G :=
  CFSG.ABGTheoremB.pCoreIn 2 (normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G))

@[expose] def D (d : Data G h) : Subgroup G := ⁅d.B₆, d.I₁⁆

@[expose] def L₁ (d : Data G h) : Subgroup G :=
  d.D ⊔ closure {x | ∃ g ∈ normalizer (d.D : Set G), ∃ n ∈ d.N₁, x = g * n * g⁻¹}

@[expose] def L₂ (d : Data G h) : Subgroup G :=
  d.E ⊔ closure {x | ∃ g ∈ normalizer (d.E : Set G), ∃ n ∈ d.N₂, x = g * n * g⁻¹}

@[expose] def M₄ (d : Data G h) : Subgroup G :=
  (normalClosure ((d.N₄.subgroupOf (centralizer (d.I₄ : Set G)) :
    Subgroup (centralizer (d.I₄ : Set G))) : Set (centralizer (d.I₄ : Set G)))).map
    (centralizer (d.I₄ : Set G)).subtype

@[expose] def M₅ (d : Data G h) : Subgroup G :=
  (normalClosure ((d.N₅.subgroupOf (centralizer (d.I₅ : Set G)) :
    Subgroup (centralizer (d.I₅ : Set G))) : Set (centralizer (d.I₅ : Set G)))).map
    (centralizer (d.I₅ : Set G)).subtype

@[expose] def Kc (d : Data G h) (X : Subgroup G) : Subgroup G :=
  (normalClosure ((X.subgroupOf d.L₁ : Subgroup d.L₁) : Set d.L₁)).map d.L₁.subtype

@[expose] def Uc (d : Data G h) (S X : Subgroup G) : Subgroup G := S ⊓ (d.D ⊔ d.Kc X)

@[expose] def M₂Linear (d : Data G h) : Prop :=
  IsSimpleGroup (CFSG.layer (centralizer (d.I₂ : Set G) ⧸
    standardComponentOddCore (centralizer (d.I₂ : Set G))))

variable (d : Data G h)

@[expose] def Sec3_8 : Prop :=
  d.L₂ = d.E ⊔ d.M₂ ∧ d.V ≤ CFSG.centerIn d.L₂ ∧
    Odd (d.E.relIndex (centralizerSection d.L₂ d.E)) ∧
    (Subgroup.upperCentralSeries ↥(d.E ⊔ zpowers d.t) 2).map (d.E ⊔ zpowers d.t).subtype = d.V ∧
    ∀ X : Subgroup G,
      Maximal (fun Y : Subgroup G => d.V ≤ Y ∧ Y ≤ d.E ⊔ zpowers d.t ∧ ElemAbMod d.V Y) X ↔
        X = d.E ∨ X = d.V ⊔ d.B₂

@[expose] def Sec3_9_one : Prop :=
  ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S →
    S = d.E ⊔ d.D ∧ (d.E.subgroupOf S).Characteristic ∧ (d.D.subgroupOf S).Characteristic

@[expose] def Sec3_9_two : Prop :=
  ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S →
    CFSG.centerIn S = d.V ∧ (Subgroup.upperCentralSeries ↥S 2).map S.subtype = d.W ∧
      d.D = S ⊓ centralizer (d.W : Set G) ∧ CFSG.centerIn d.D = d.F ∧ ∀ x ∈ d.D, x * x ∈ d.F

@[expose] def Sec3_9_three : Prop :=
  d.L₁ = d.D ⊔ d.M₁ ∧ Odd (d.D.relIndex (centralizerSection (d.D ⊔ d.M₁) d.D))

@[expose] def Sec3_10_one : Prop :=
  ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S →
    d.V = S ⊓ centralizer (d.I₃ : Set G) ∧
    (d.W = d.V ⊔ (S ⊓ centralizer (d.I₄ : Set G)) ∧
      d.V ⊓ (S ⊓ centralizer (d.I₄ : Set G)) = ⊥) ∧
    (d.F = d.W ⊔ (S ⊓ centralizer (d.I₆ : Set G)) ∧
      d.W ⊓ (S ⊓ centralizer (d.I₆ : Set G)) = ⊥) ∧
    (d.F = (S ⊓ centralizer (d.I₄ : Set G)) ⊔
        (S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) ∧
      (S ⊓ centralizer (d.I₄ : Set G)) ⊓
        (S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) = ⊥) ∧
    (d.E = (d.E ⊓ d.D) ⊔ (S ⊓ centralizer (d.I₁ : Set G)) ∧
      (d.E ⊓ d.D) ⊓ (S ⊓ centralizer (d.I₁ : Set G)) = ⊥) ∧
    d.E = d.W ⊔ d.W.map (MulAut.conj d.s).toMonoidHom ⊔ (S ⊓ centralizer (d.I₅ : Set G)) ∧
    (d.D = (d.E ⊓ d.D) ⊔ (S ⊓ centralizer (d.I₂ : Set G)) ∧
      (d.E ⊓ d.D) ⊓ (S ⊓ centralizer (d.I₂ : Set G)) = ⊥) ∧
    d.D = d.F ⊔ (S ⊓ centralizer (d.I₂ : Set G)) ⊔ (S ⊓ centralizer (d.I₅ : Set G)) ∧
    d.E ⊓ d.D = d.W ⊔ (S ⊓ centralizer (d.I₅ : Set G)) ∧
    d.F ⊔ (d.E ⊓ d.D) = d.F ⊔ (S ⊓ centralizer (d.I₅ : Set G)) ∧
    (S = d.E ⊔ (S ⊓ centralizer (d.I₂ : Set G)) ∧ d.E ⊓ (S ⊓ centralizer (d.I₂ : Set G)) = ⊥) ∧
    (S = d.D ⊔ (S ⊓ centralizer (d.I₁ : Set G)) ∧ d.D ⊓ (S ⊓ centralizer (d.I₁ : Set G)) = ⊥)

@[expose] def Sec3_10_two : Prop :=
  ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S →
    (S ⊓ centralizer (d.I₁ : Set G) = S ⊓ d.M₁ ∧ IsSylowOf 2 (S ⊓ d.M₁) d.M₁) ∧
    (S ⊓ centralizer (d.I₂ : Set G) = S ⊓ d.M₂ ∧ IsSylowOf 2 (S ⊓ d.M₂) d.M₂) ∧
    (S ⊓ centralizer (d.I₄ : Set G) = S ⊓ d.M₄ ∧ IsSylowOf 2 (S ⊓ d.M₄) d.M₄) ∧
    (S ⊓ centralizer (d.I₅ : Set G) = S ⊓ d.M₅ ∧ IsSylowOf 2 (S ⊓ d.M₅) d.M₅) ∧
    d.F ⊓ d.M₂ = CFSG.centerIn (S ⊓ d.M₂) ∧ d.F ⊓ d.M₅ = CFSG.centerIn (S ⊓ d.M₅) ∧
    IsSylowOf 2 S d.L₁ ∧ IsSylowOf 2 S d.L₂

@[expose] def Sec3_11 : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 ∧
    ∃ (ψ : d.M₁ ≃* SL(2, k) × SL(2, k)) (α : d.N₁ ≃* SL(2, k)),
      (∀ (a : d.N₁) (x : d.M₁), (x : G) = a → ψ x = (α a, α a)) ∧
      ∀ (x y : d.M₁) (y₁ y₂ : SL(2, k)), (y : G) = d.t⁻¹ * x * d.t →
        ψ x = (y₁, y₂) → ψ y = (y₂, y₁)

@[expose] def Sec3_12 : Prop :=
  ∀ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 →
    ∀ ψ : d.M₁ ≃* SL(2, k) × SL(2, k),
      (d.F ⊔ d.Kc (Common.prodFactorOne ψ)) ⊔
          (d.F ⊔ (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom) = d.L₁ ∧
        (d.F ⊔ d.Kc (Common.prodFactorOne ψ)) ⊓
          (d.F ⊔ (d.Kc (Common.prodFactorOne ψ)).map (MulAut.conj d.t).toMonoidHom) = d.F ∧
        IsNaturalSection (d.M₁ ⊓ d.Kc (Common.prodFactorOne ψ))
          ((d.F ⊔ d.Kc (Common.prodFactorOne ψ)) ⊓ d.D) d.F k

@[expose] def Sec3_13_one : Prop :=
  ∀ S : Subgroup G, IsSylowOf 2 S d.L₂ → d.P ≤ S →
    ∀ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = (2 ^ f) ^ 2 →
      ∀ ψ : d.M₁ ≃* SL(2, k) × SL(2, k),
        Nat.card (CFSG.centerIn (d.Uc S (Common.prodFactorOne ψ))) ≤ (2 ^ f) ^ 4 →
          d.M₂Linear ∧ Nat.card (CFSG.centerIn (d.Uc S (Common.prodFactorOne ψ))) = (2 ^ f) ^ 4

end Data

end CFSG.LocalAnalysis.EvenBN.U5

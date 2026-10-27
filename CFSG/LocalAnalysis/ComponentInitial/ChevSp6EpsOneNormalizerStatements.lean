module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianStatements
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def aglAct : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative (Fin 3 → ZMod 2)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd ((g : M₃) *ᵥ v.toAdd)
      invFun := fun v => Multiplicative.ofAdd (((g⁻¹ : GL (Fin 3) (ZMod 2)) : M₃) *ᵥ v.toAdd)
      left_inv := fun v => by
        simp only [toAdd_ofAdd, mulVec_mulVec]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
        rfl
      right_inv := fun v => by
        simp only [toAdd_ofAdd, mulVec_mulVec]
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
        rfl
      map_mul' := fun v w => by
        simp only [toAdd_mul, mulVec_add, ofAdd_add] }
  map_one' := MulEquiv.ext fun v => by
    simp only [Units.val_one, one_mulVec, MulEquiv.coe_mk, Equiv.coe_fn_mk, ofAdd_toAdd]
    rfl
  map_mul' g h := MulEquiv.ext fun v => by
    simp only [Units.val_mul, MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply, toAdd_ofAdd,
      mulVec_mulVec]

abbrev AGL32 : Type := Multiplicative (Fin 3 → ZMod 2) ⋊[aglAct] GL (Fin 3) (ZMod 2)

@[expose] def aglLin (x : AGL32) (p : ZMod 2 × (Fin 3 → ZMod 2)) : ZMod 2 × (Fin 3 → ZMod 2) :=
  (p.1, (x.right : M₃) *ᵥ p.2 + p.1 • x.left.toAdd)

section Setup

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

@[expose] def sp6ν₂ (d : G) : ↥(binarySymMatrices 3) :=
  Classical.epsilon fun B : ↥(binarySymMatrices 3) =>
    z⁻¹ * (d⁻¹ * z * d) = tauHom φ he (Multiplicative.ofAdd B)

end Setup

section SetupPoint

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (z : G)

@[expose] def sp6C₁ (hb : b.IsAlt) : Subgroup G :=
  Classical.epsilon fun C : Subgroup G =>
    zpowers ((φ.symm (pointElt hb (mem_pairOrth_left (0 : pairOrth b (e (Sum.inl 0))
        (e (Sum.inr 0))).2) 1) : L) : G) ≤ C ∧
    C ≤ CFSG.Assembly.pCoreOf 2 (normalizer ((pullSub φ (pointRadical b hb (e (Sum.inl 0))
        (e (Sum.inr 0))) ⊔ zpowers z : Subgroup G) : Set G)) ∧
    Nat.card C = 1024 ∧
    (∀ x ∈ C, x ^ 2 ∈ zpowers ((φ.symm (pointElt hb (mem_pairOrth_left
      (0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))).2) 1) : L) : G)) ∧
    ∀ x ∈ C, ∀ y ∈ C, x⁻¹ * y⁻¹ * x * y ∈ zpowers ((φ.symm (pointElt hb (mem_pairOrth_left
      (0 : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))).2) 1) : L) : G)

end SetupPoint

open Classical in
@[expose] def EpsOneLagrangianNormalizerStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.oddCore G = ⊥ →
  ∀ (L : Subgroup G), CFSG.Assembly.ComponentType.IsStandardSubgroup L → ¬ L.Normal →
    center L = ⊥ → CFSG.Blueprint.LieModel L .PSp 3 2 1 →
  ∀ (T : Sylow 2 (centralizer (L : Set G))), IsCyclic (T : Subgroup (centralizer (L : Set G))) →
  ∀ z : G, z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype →
    orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥ →
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (b : BilinForm (ZMod 2) V) (hb : b.IsAlt), b.Nondegenerate → finrank (ZMod 2) V = 6 →
  ∀ (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V)
    (he : IsSymplecticBasis b e),
    conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G) →
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let Q : E → ZMod 2 := fun w =>
      e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)
    let r : E × ZMod 2 := (0, 1)
    let τ : ↥(binarySymMatrices 3) → G := fun B => tauHom φ he (Multiplicative.ofAdd B)
    let θ₁ : (E × ZMod 2) × ZMod 2 → G := fun x =>
      ((φ.symm (n x.1.1 (x.1.2 + Q x.1.1)) : L) : G) * z ^ x.2.val
    let N₂ := sp6N₂ φ e z
    let D₂ := sp6D₂ φ e z
    let F₂ := sp6F₂ φ he z
    let H := centralizer ({z} : Set G)
    let N₂₀ := N₂ ⊓ H
    let A₁ := pullSub φ (pointRadical b hb u f)
    let D₁ := CFSG.Assembly.pCoreOf 2 (normalizer ((A₁ ⊔ zpowers z : Subgroup G) : Set G))
    let E₂ := sp6E₂ φ he z
    let C₂ := sp6C₂ φ he z
    let ν₂ := sp6ν₂ φ he z
    (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
      d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
    Monoid.exponent C₂ = 4 →
    let κ : G → ZMod 2 × (Fin 3 → ZMod 2) := fun d =>
      (if d ∈ C₂ then 0 else 1, symThreeDiag (ν₂ d : M₃))
    let Q₂ := normalizer (D₂ : Set G)
    let Dhat₂ := CFSG.Assembly.pCoreOf 2 Q₂
    ((E₂ : Set G) ⊆ F₂ ∧ IsMulCommutative E₂ ∧ Nat.card E₂ = 512 ∧
      ∀ E' : Subgroup G, (E' : Set G) ⊆ F₂ → IsMulCommutative E' → Nat.card E' = 512 →
        E' = E₂) ∧
    (∀ d ∈ D₂, z⁻¹ * (d⁻¹ * z * d) = τ (ν₂ d)) ∧
    N₂ ≤ Q₂ ∧ (∀ x ∈ Q₂, ∀ c ∈ C₂, x * c * x⁻¹ ∈ C₂) ∧ (∀ x ∈ Q₂, ∀ y ∈ E₂, x * y * x⁻¹ ∈ E₂) ∧
    (∀ d ∈ D₂, ∀ d' ∈ D₂, κ (d * d') = κ d + κ d') ∧ (∀ d ∈ D₂, κ d = 0 ↔ d ∈ E₂) ∧
    (∀ p : ZMod 2 × (Fin 3 → ZMod 2), ∃ d ∈ D₂, κ d = p) ∧
    (∀ s : ZMod 2, ∀ c ∈ C₂, κ (z ^ s.val * c) = (s, symThreeDiag (ν₂ c : M₃))) ∧
    (∀ x ∈ Q₂, (∀ d ∈ D₂, κ (x * d * x⁻¹) = κ d) ↔ x ∈ D₂) ∧
    (∃ Ψ : Q₂ →* AGL32, Function.Surjective Ψ ∧ Ψ.ker = D₂.subgroupOf Q₂ ∧
      (∀ x : Q₂, ∀ d ∈ D₂, κ ((x : G) * d * (x : G)⁻¹) = aglLin (Ψ x) (κ d)) ∧
      (∀ g : GL (Fin 3) (ZMod 2), ∃ hg : leviHom φ he g ∈ Q₂,
        Ψ ⟨_, hg⟩ = SemidirectProduct.inr g) ∧
      (∀ x : Q₂, (x : G) ∈ N₂ ↔ (Ψ x).left = 1) ∧
      (∀ x : Q₂, (x : G) ∈ Dhat₂ ↔ (Ψ x).right = 1) ∧
      ∀ x : Q₂, (x : G) ∈ Dhat₂ → Ψ x = SemidirectProduct.inl (Multiplicative.ofAdd
        (symThreeDiag (ν₂ (z⁻¹ * ((x : G)⁻¹ * z * x)) : M₃)))) ∧
    N₂.relIndex Q₂ = 8 ∧ (∀ x ∈ Q₂, x ∈ N₂ ↔ x * z * x⁻¹ ∈ z • (E₂ : Set G)) ∧
    D₂ ≤ Dhat₂ ∧ Nat.card Dhat₂ = 2 ^ 16 ∧
    (∀ x ∈ Dhat₂, z⁻¹ * (x⁻¹ * z * x) ∈ C₂) ∧
    (∀ x ∈ Dhat₂, ∀ y ∈ Dhat₂, z⁻¹ * ((x * y)⁻¹ * z * (x * y)) *
      (z⁻¹ * (x⁻¹ * z * x) * (z⁻¹ * (y⁻¹ * z * y)))⁻¹ ∈ E₂) ∧
    (∀ x ∈ Dhat₂, z⁻¹ * (x⁻¹ * z * x) ∈ E₂ ↔ x ∈ D₂) ∧
    (∀ c ∈ C₂, ∃ x ∈ Dhat₂, (z⁻¹ * (x⁻¹ * z * x))⁻¹ * c ∈ E₂) ∧
    (∀ y ∈ Q₂, ∀ x ∈ Dhat₂, z⁻¹ * ((y * x * y⁻¹)⁻¹ * z * (y * x * y⁻¹)) *
      (y * (z⁻¹ * (x⁻¹ * z * x)) * y⁻¹)⁻¹ ∈ E₂) ∧
    C₂ ≤ Dhat₂ ∧ (∀ x ∈ Dhat₂, (∀ y ∈ Dhat₂, x⁻¹ * y⁻¹ * x * y ∈ E₂) ↔ x ∈ C₂) ∧
    Q₂ ⊓ H = N₂₀ ∧ conjClass Q₂ z = {x | x ∈ D₂ ∧ x ∉ C₂ ∧ x ^ 2 = 1} ∧
    Nat.card (conjClass Q₂ z) = 512 ∧
    Nat.card Q₂ = 2 ^ 19 * 21 ∧ ∃ P : Subgroup G, P ≤ Q₂ ∧ Nat.card P = 2 ^ 19

@[expose] def EpsOnePointNormalizerStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.oddCore G = ⊥ →
  ∀ (L : Subgroup G), CFSG.Assembly.ComponentType.IsStandardSubgroup L → ¬ L.Normal →
    center L = ⊥ → CFSG.Blueprint.LieModel L .PSp 3 2 1 →
  ∀ (T : Sylow 2 (centralizer (L : Set G))), IsCyclic (T : Subgroup (centralizer (L : Set G))) →
  ∀ z : G, z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype →
    orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥ →
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (b : BilinForm (ZMod 2) V) (hb : b.IsAlt), b.Nondegenerate → finrank (ZMod 2) V = 6 →
  ∀ (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V)
    (he : IsSymplecticBasis b e),
    conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G) →
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let Q : E → ZMod 2 := fun w =>
      e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)
    let r : E × ZMod 2 := (0, 1)
    let τ : ↥(binarySymMatrices 3) → G := fun B => tauHom φ he (Multiplicative.ofAdd B)
    let θ₂ : ↥(binarySymMatrices 3) × ZMod 2 → G := fun x => τ x.1 * z ^ x.2.val
    let θ₁ : (E × ZMod 2) × ZMod 2 → G := fun x =>
      ((φ.symm (n x.1.1 (x.1.2 + Q x.1.1)) : L) : G) * z ^ x.2.val
    let A₂ := sp6A₂ φ e
    let R₂ := sp6R₂ φ e z
    let N₂ := sp6N₂ φ e z
    let D₂ := sp6D₂ φ e z
    let F₂ := sp6F₂ φ he z
    let H := centralizer ({z} : Set G)
    let A₁ := pullSub φ (pointRadical b hb u f)
    let b₁ : G := ((φ.symm (n 0 1) : L) : G)
    let I₁ := zpowers b₁
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    let F₁ : Set G := {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ I₁}
    let E₂ := sp6E₂ φ he z
    let C₂ := sp6C₂ φ he z
    let ν₂ := sp6ν₂ φ he z
    (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
      d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
    Monoid.exponent C₂ = 4 →
    let C₁ := sp6C₁ φ e z hb
    let E₁ : Set G := (C₁ : Set G) ∩ F₁
    let Z₁ := (center C₁).map C₁.subtype
    let K₀ := C₁ ⊓ C₂
    let U₃ := (unitriangularGL 3 (ZMod 2)).map (leviHom φ he)
    let S_H := zpowers z ⊔ A₂ ⊔ U₃
    let S₁ := D₁ ⊔ S_H
    let S₂ := D₂ ⊔ S_H
    let P₁ := A₁ ⊔ K₀
    let P₂ := A₂ ⊔ K₀
    let A := P₁ ⊔ P₂
    let B := zpowers z ⊔ A
    let U₁ := B ⊓ D₁
    let U₂ := B ⊓ D₂
    let N := normalizer (B : Set G) ⊓ centralizer ({b₁} : Set G)
    let K₁ := N ⊓ normalizer (U₁ : Set G)
    let K₂ := N ⊓ normalizer (U₂ : Set G)
    ((E₂ : Set G) ⊆ F₂ ∧ IsMulCommutative E₂ ∧ Nat.card E₂ = 512 ∧
      ∀ E' : Subgroup G, (E' : Set G) ⊆ F₂ → IsMulCommutative E' → Nat.card E' = 512 →
        E' = E₂) ∧
    (I₁ ≤ C₁ ∧ C₁ ≤ D₁ ∧ Nat.card C₁ = 1024 ∧ (∀ x ∈ C₁, x ^ 2 ∈ I₁) ∧
      (∀ x ∈ C₁, ∀ y ∈ C₁, x⁻¹ * y⁻¹ * x * y ∈ I₁) ∧
      ∀ C' : Subgroup G, I₁ ≤ C' → C' ≤ D₁ → Nat.card C' = 1024 → (∀ x ∈ C', x ^ 2 ∈ I₁) →
        (∀ x ∈ C', ∀ y ∈ C', x⁻¹ * y⁻¹ * x * y ∈ I₁) → C' = C₁) ∧
    (∀ κ₂ : ZMod 2, (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = θ₂ (C, 1) → d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym
        (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε)) → κ₂ = 0) ∧
    ((∀ d ∈ D₂, z⁻¹ * (d⁻¹ * z * d) = τ (ν₂ d)) ∧
      (∀ d ∈ D₂, ∀ d' ∈ D₂, ν₂ (d * d') = ν₂ d + ν₂ d') ∧
      (∀ B : ↥(binarySymMatrices 3), ∃ d ∈ D₂, ν₂ d = B) ∧ (∀ d ∈ D₂, ν₂ d = 0 ↔ d ∈ R₂) ∧
      (∀ w : Fin 3 → ZMod 2, ∃ c ∈ C₂, symThreeDiag (ν₂ c : M₃) = w) ∧
      (∀ c ∈ C₂, symThreeDiag (ν₂ c : M₃) = 0 ↔ c ∈ E₂) ∧
      ∀ g : GL (Fin 3) (ZMod 2), ∀ c ∈ C₂, leviHom φ he g * c * (leviHom φ he g)⁻¹ ∈ C₂ ∧
        symThreeDiag (ν₂ (leviHom φ he g * c * (leviHom φ he g)⁻¹) : M₃) =
          (g : M₃) *ᵥ symThreeDiag (ν₂ c : M₃)) ∧
    (C₁.subgroupOf D₁).Characteristic ∧
    (∀ α : D₁ ≃* D₁, ∀ x : D₁, ((α x : D₁) : G) ∈ F₁ ↔ (x : G) ∈ F₁) ∧
    (E₂.subgroupOf D₂).Characteristic ∧ (C₂.subgroupOf D₂).Characteristic ∧
    E₂ ≤ N₂ ∧ IsElementaryAbelian 2 E₂ ∧
    (∀ X : Subgroup G, X ≤ N₂ → IsElementaryAbelian 2 X → Nat.card X = 512 → X = E₂) ∧
    (center C₂).map C₂.subtype = E₂ ∧ Nonempty (↥(center C₁) ≃* Multiplicative (ZMod 4)) ∧
    {x | ∃ y ∈ Z₁, y ^ 2 = x} = (I₁ : Set G) ∧ E₁ = ((A₁ ⊔ Z₁ : Subgroup G) : Set G) ∧
    (∀ t ∈ Z₁, zpowers t = Z₁ →
      F₁ = ((A₁ ⊔ closure {z, t} : Subgroup G) : Set G) ∧
      Nonempty (↥(A₁ ⊔ closure {z, t} : Subgroup G) ≃*
        DihedralGroup 4 × Multiplicative (Fin 4 → ZMod 2)) ∧
      ∀ X : Subgroup G, (X : Set G) ⊆ F₁ → IsElementaryAbelian 2 X → Nat.card X = 64 →
        X = B₁ ∨ X = A₁ ⊔ zpowers (z * t)) ∧
    (∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = S_H) ∧
    (∃ P : Sylow 2 N₁, (P : Subgroup N₁).map N₁.subtype = S₁) ∧
    (∃ P : Sylow 2 N₂, (P : Subgroup N₂).map N₂.subtype = S₂) ∧
    Nat.card S₁ = 2 ^ 15 ∧ Nat.card S₂ = 2 ^ 16 ∧
    Nat.card P₁ = 2 ^ 8 ∧ Nat.card P₂ = 2 ^ 9 ∧ Nat.card A = 2 ^ 11 ∧ Nat.card B = 2 ^ 12 ∧
    B = CFSG.Assembly.pCoreOf 2 (N₁ ⊓ N₂) ∧ Nat.card (S₁ ⊓ S₂ : Subgroup G) = 2 ^ 13 ∧
    U₁ = zpowers z ⊔ P₁ ∧ U₂ = zpowers z ⊔ P₂ ∧ P₁ = C₁ ⊓ S₂ ∧ P₂ = C₂ ⊓ S₁ ∧
    P₁ ≤ N ∧ (∀ m ∈ N, ∀ p ∈ P₁, m * p * m⁻¹ ∈ P₁) ∧
    P₂ ≤ N ∧ (∀ m ∈ N, ∀ p ∈ P₂, m * p * m⁻¹ ∈ P₂) ∧
    A ≤ N ∧ (∀ m ∈ N, ∀ p ∈ A, m * p * m⁻¹ ∈ A) ∧ S₁ ≤ N ∧ S₂ ≤ N ∧
    (N : Set G) = (S₁ : Set G) * (K₂ : Set G) ∧ (N : Set G) = (S₂ : Set G) * (K₁ : Set G) ∧
    S₁ ⊓ K₂ = S₁ ⊓ S₂ ∧ S₂ ⊓ K₁ = S₁ ⊓ S₂ ∧
    N ⊓ N₁ ≤ K₁ ∧ N ⊓ N₂ ≤ K₂ ∧ (N ⊓ N₁).relIndex K₁ = 2 ∧ (N ⊓ N₂).relIndex K₂ = 2 ∧
    normalizer (D₁ : Set G) = normalizer F₁ ∧ normalizer (D₁ : Set G) ≤ normalizer (C₁ : Set G) ∧
    N₁ ≤ normalizer (D₁ : Set G) ∧ N₁.relIndex (normalizer (D₁ : Set G)) = 2 ∧
    ∃ T₂ : Subgroup G, T₂ ≤ K₂ ∧ S₂ < T₂ ∧ T₂ ≤ normalizer (D₂ : Set G) ∧ Nat.card T₂ = 2 ^ 17

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianStatements
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64OtherParabolic

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem exists_sp6_action_parameters {G : Type} [Group G] [Finite G]
    (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
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
    let A₁ := pullSub φ (pointRadical b hb u f)
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    ∃ κ₂ lam : ZMod 2,
      (∀ d ∈ sp6D₂ φ e z, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
        d⁻¹ * z * d = θ₂ (C, 1) →
        d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C, ε)) ∧
      (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
        d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (lam * b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) := by
  intro u f E n Q r τ θ₂ θ₁ A₁ B₁ N₁ D₁
  obtain ⟨-, hzC, -, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, -, -, -, -, -, hker, -, -, -, ⟨σ, -, -, -, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ₂, D₂', F₂', ν₂, hD₂, -, -, -, -, -, -, -, hν₂z, -, -, hact₂, -⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ψ, θ₁', hψ, hθ₁', lam, D₁', F₁', ν₁, hD₁,
    -, -, -, -, -, -, -, -, -, -, hν₁z, -, -, hact₁, -⟩ :=
    standard_binary_symplectic_six_degree64_other_parabolic_normalizer hG hL hLn hZ hmodel T hT
      hzT hz hH hb hnd hV φ e he hfull
  refine ⟨κ₂, lam, ?_, ?_⟩
  · intro d hd C B ε hC
    have hd' : d ∈ D₂' := by
      rw [hD₂]
      exact hd
    have hθ₂ : ∀ x : ↥(binarySymMatrices 3) × ZMod 2,
        θ₂ x = radHom φ he hzC hz (Multiplicative.ofAdd x) := fun _ => rfl
    have hCν : C = ν₂ d := by
      have h1 := (hν₂z d hd').symm.trans (hC.trans (hθ₂ (C, 1)))
      have h2 := radHom_injective φ he hzC hz hinf h1
      exact (Prod.mk.inj (Multiplicative.ofAdd.injective h2)).1.symm
    subst hCν
    rw [hθ₂, hθ₂]
    exact hact₂ d hd' B ε
  · intro d hd a v ε ha
    have hd' : d ∈ D₁' := by
      rw [hD₁]
      exact hd
    have hθ₁ : ∀ (w : E × ZMod 2) (ε' : ZMod 2),
        θ₁ (w, ε') = ((θ₁'.symm (Multiplicative.ofAdd (w, ε')) : B₁) : G) := by
      intro w ε'
      rw [hθ₁']
      have h1 := hψ w.1 (w.2 + Q w.1)
      have h2 : w.2 + Q w.1 + Q w.1 = w.2 := by
        rw [add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]
      rw [h2] at h1
      change ((φ.symm (n w.1 (w.2 + Q w.1)) : L) : G) * z ^ ε'.val = _
      rw [← h1]
    have haν : a = ν₁ d := by
      have h1 := (hν₁z d hd').symm.trans (ha.trans (hθ₁ a 1))
      have h2 := θ₁'.symm.injective (Subtype.ext h1)
      exact (Prod.mk.inj (Multiplicative.ofAdd.injective h2)).1.symm
    subst haν
    rw [hθ₁, hθ₁]
    exact hact₁ d hd' v ε

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

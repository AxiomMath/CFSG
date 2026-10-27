module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64OtherParabolic

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.SteinbergCF

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem exists_sp6_action_parameters {G : Type} [Group G] [Finite G] (hG : CFSG.oddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (hfull : conjClass (normalizer ((pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔
        zpowers z : Subgroup G) : Set G)) z =
      z • (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G)) :
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
    let D₂ := CFSG.Assembly.pCoreOf 2 (normalizer
      ((pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔ zpowers z : Subgroup G) : Set G))
    let A₁ := pullSub φ (pointRadical b hb u f)
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    Function.Injective θ₂ ∧ (∀ C : ↥(binarySymMatrices 3), ∃ d ∈ D₂, d⁻¹ * z * d = θ₂ (C, 1)) ∧
    ∃ κ₂ lam : ZMod 2,
      (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2), d⁻¹ * z * d = θ₂ (C, 1) →
        d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C, ε)) ∧
      (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
        d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (lam * b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) := by
  intro u f E n Q r τ θ₂ θ₁ D₂ A₁ B₁ N₁ D₁
  obtain ⟨-, hzC, -, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, -, -, -, -, -, hker, -, -, -, ⟨σ, -, -, -, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ₂, D₂', -, ν₂, hD₂, -, -, -, -, -, -, -, hν₂z, -, hν₂surj, hact₂, -⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  have hθ₂ : ∀ x : ↥(binarySymMatrices 3) × ZMod 2,
      θ₂ x = radHom φ he hzC hz (Multiplicative.ofAdd x) := fun x => rfl
  have hθ₂inj : Function.Injective θ₂ := fun x y h => by
    rw [hθ₂, hθ₂] at h
    exact Multiplicative.ofAdd.injective (radHom_injective φ he hzC hz hinf h)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ψ, θ₁', hψ, hθ₁', lam, D₁', -, ν₁, hD₁, -,
    -, -, -, -, -, -, -, -, -, hν₁z, -, -, hact₁, -⟩ :=
    standard_binary_symplectic_six_degree64_other_parabolic_normalizer hG hL hLn hZ hmodel T hT
      hzT hz hH hb hnd hV φ e he hfull
  have hθ₁ : ∀ x : (E × ZMod 2) × ZMod 2,
      θ₁ x = ((θ₁'.symm (Multiplicative.ofAdd x) : B₁) : G) := by
    rintro ⟨⟨w, t⟩, ε⟩
    rw [hθ₁']
    have h := hψ w (t + Q w)
    rw [show t + Q w + Q w = t by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]] at h
    show ((φ.symm (n w (t + Q w)) : L) : G) * z ^ ε.val = _
    rw [h]
  have hθ₁inj : Function.Injective θ₁ := fun x y h => by
    rw [hθ₁, hθ₁] at h
    exact Multiplicative.ofAdd.injective (θ₁'.symm.injective (Subtype.ext h))
  refine ⟨hθ₂inj, fun C => ?_, κ₂, lam, fun d hd C B ε hdz => ?_, fun d hd a v ε hdz => ?_⟩
  · obtain ⟨d, hd, hdC⟩ := hν₂surj C
    have hd' : d ∈ CFSG.Assembly.pCoreOf 2 (normalizer ((radSub φ z e : Subgroup G) : Set G)) :=
      hD₂ ▸ hd
    refine ⟨d, hd', ?_⟩
    rw [hν₂z d hd, hdC]
    rfl
  · have hd' : d ∈ D₂' := hD₂ ▸ hd
    have hC : C = ν₂ d := by
      have h1 := hν₂z d hd'
      rw [← hθ₂] at h1
      exact (Prod.ext_iff.mp (hθ₂inj (hdz.symm.trans h1))).1
    rw [hθ₂, hθ₂, hact₂ d hd' B ε, hC]
  · have hd' : d ∈ D₁' := hD₁ ▸ hd
    have ha : a = ν₁ d := by
      have h1 := hν₁z d hd'
      rw [← hθ₁] at h1
      exact (Prod.ext_iff.mp (hθ₁inj (hdz.symm.trans h1))).1
    rw [hθ₁, hθ₁, hact₁ d hd' v ε, ha]

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.SteinbergCF

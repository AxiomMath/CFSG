module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerStatements
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64LagrangianCompletion
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NextBlock
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64Intersection

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem epsOne_kill_inputs (hQ : EpsOneLagrangianNormalizerStmt)
    {G : Type} [Group G] [Finite G] (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
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
    let A₂ := pullSub φ (pointwiseStabilizer b (lagrangianOf e))
    let R₂ := A₂ ⊔ zpowers z
    let N₂ := normalizer (R₂ : Set G)
    let D₂ := CFSG.Assembly.pCoreOf 2 N₂
    let A₁ := pullSub φ (pointRadical b hb u f)
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    ∀ κ₂ lam : ZMod 2,
      (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2), d⁻¹ * z * d = θ₂ (C, 1) →
        d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C, ε)) →
      (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
        d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (lam * b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
      lam = 1 → ¬ IsElementaryAbelian 2 (sp6C₂ φ he z) →
      let Q₂ := normalizer (D₂ : Set G)
      let Dhat₂ := CFSG.Assembly.pCoreOf 2 Q₂
      let Jh := Dhat₂ ⊓ centralizer (sp6E₂ φ he z : Set G)
      sp6E₂ φ he z ≤ Jh ∧ z ∈ normalizer (Jh : Set G) ∧ z * z = 1 ∧
        (∀ x ∈ sp6E₂ φ he z, z * x * z⁻¹ ∈ sp6E₂ φ he z) ∧ Nat.card Dhat₂ = 2 ^ 16 := by
  intro u f E n Q r τ θ₂ θ₁ A₂ R₂ N₂ D₂ A₁ B₁ N₁ D₁ κ₂ lam h₂ h₁ hlam hC₂ Q₂ Dhat₂ Jh
  obtain ⟨-, C₁, E₂', h4'⟩ := standard_binary_symplectic_six_degree64_lagrangian_subgroup_completion
    hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull κ₂ lam h₂ h₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE₂F, hE₂c, hE₂card, hE₂uniq, -,
    -, -, -, -, -, hDzC, -, -, hE₂C₂, -, -, -, -, -, ν, ε, -, -, -, -, -,
    -, -, -, -, hε0, hε1, -, -⟩ := h4'
  have hspec := Classical.epsilon_spec (p := fun E : Subgroup G =>
    (E : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E ∧ Nat.card E = 512) ⟨E₂', hE₂F, hE₂c, hE₂card⟩
  have hE : E₂' = sp6E₂ φ he z := (hE₂uniq _ hspec.1 hspec.2.1 hspec.2.2).symm
  subst hE
  have hε : ε = 1 := by
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) ε with h | h
    · exact absurd (elemAbelian_of_sq_eq_one (hε0 h).1) hC₂
    · exact h
  obtain ⟨hexp, -, -⟩ := hε1 hε
  have hlam1 : ∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
      d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (b (a.1 : V) (v.1 : V)) • r + ε • a, ε) := by
    intro d hd a v ε' hda
    have := h₁ d hd a v ε' hda
    rwa [hlam, one_mul] at this
  obtain ⟨-, -, -, -, hQE, -, -, -, -, -, -, -, -, hDDh, hDhcard, -, -, -, -, -, hCDh, -, -⟩ :=
    hQ G hG L hL hLn hZ hmodel T hT z hzT hz hH V b hb hnd hV φ e he hfull hlam1 hexp
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hzD : z ∈ D₂ :=
    (Set.ext_iff.1 hDzC z).2 ⟨z, mem_zpowers z, 1, one_mem _, mul_one z⟩
  have hzQ : z ∈ Q₂ := le_normalizer hzD
  have hcommE : ∀ x ∈ sp6E₂ φ he z, ∀ y ∈ sp6E₂ φ he z, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₂c.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEJ : sp6E₂ φ he z ≤ Jh := fun x hx =>
    ⟨hCDh (hE₂C₂ hx), mem_centralizer_iff.2 fun y hy => hcommE y hy x hx⟩
  have hconj : ∀ g ∈ Q₂, ∀ x ∈ Jh, g * x * g⁻¹ ∈ Jh := by
    intro g hg x hx
    refine ⟨conj_mem_pCoreOf 2 hg hx.1, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ sp6E₂ φ he z := hQE g⁻¹ (inv_mem hg) y hy
    rw [inv_inv] at hy'
    have hc := mem_centralizer_iff.1 hx.2 _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * y := by group
  have hzJ : z ∈ normalizer (Jh : Set G) :=
    mem_normalizer_iff.2 fun x => ⟨hconj z hzQ x, fun hx => by
      have := hconj z⁻¹ (inv_mem hzQ) _ hx
      simpa [mul_assoc] using this⟩
  exact ⟨hEJ, hzJ, hz2, fun x hx => hQE z hzQ x hx, hDhcard⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

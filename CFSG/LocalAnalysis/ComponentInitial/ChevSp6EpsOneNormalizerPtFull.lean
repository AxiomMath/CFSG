module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerSetup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2)

structure PtFull (D₂ C₂ E₂ : Subgroup G) (ν₂ : G → ↥(binarySymMatrices 3))
    (σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
      GL (Fin 3) (ZMod 2))
    (D₁ C₁ F₁ : Subgroup G) (ν₁ : G → pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2) :
    Prop extends PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁ where
  hσsurj : Function.Surjective σ
  hσker : σ.ker = (radSub φ z e).subgroupOf
    (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G))
  hσcol : ∀ (n : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer ({z} : Set G))) (hn : (n : G) ∈ L) (j : Fin 3),
    linOf (φ ⟨n, hn⟩) (e (Sum.inl j)) = ∑ i, (σ n : M₃) i j • e (Sum.inl i)
  hfull₁ : conjClass (normalizer ((ptSub φ z hb e : Subgroup G) : Set G)) z =
    z • (pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) : Set G)

theorem sigma_eq_of_congr {G : Type} [Group G] {L : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) {N₀ : Subgroup G}
    (σ σ' : N₀ →* GL (Fin 3) (ZMod 2))
    (hσ : ∀ (n : N₀) (a : G) (ha : a ∈ L) (B : M₃), Bᵀ = B →
      LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
      ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
        LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
          fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1)
    (hσ' : ∀ (n : N₀) (a : G) (ha : a ∈ L) (B : M₃), Bᵀ = B →
      LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
      ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
        LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
          fromBlocks 1 ((σ' n : M₃) * B * (σ' n : M₃)ᵀ) 0 1) (n : N₀) : σ n = σ' n := by
  refine symThreeCongrHom_injective (LinearEquiv.ext fun B => ?_)
  rw [symThreeCongrHom_apply, symThreeCongrHom_apply]
  have h1 := conj_tauHom_of_sigma φ he σ hσ n B
  have h2 := conj_tauHom_of_sigma φ he σ' hσ' n B
  exact Multiplicative.ofAdd.injective (tauHom_injective φ he (h1.symm.trans h2))

theorem ptFull_of_setting {G : Type} [Group G] [Finite G] (hG : CFSG.oddCore G = ⊥)
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
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let Q : E → ZMod 2 := fun w =>
      e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)
    let r : E × ZMod 2 := (0, 1)
    let θ₁ : (E × ZMod 2) × ZMod 2 → G := fun x =>
      ((φ.symm (n x.1.1 (x.1.2 + Q x.1.1)) : L) : G) * z ^ x.2.val
    let A₁ := pullSub φ (pointRadical b hb u f)
    let D₁ := CFSG.Assembly.pCoreOf 2 (normalizer ((A₁ ⊔ zpowers z : Subgroup G) : Set G))
    (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
      d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
    Monoid.exponent (sp6C₂ φ he z) = 4 →
    ∃ (hzC : z ∈ centralizer (L : Set G))
      (σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
        GL (Fin 3) (ZMod 2)),
      ∃ (C₁ F₁ : Subgroup G) (ν₁ : G → pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2),
      PtFull he hb φ hzC hz (sp6D₂ φ e z) (sp6C₂ φ he z) (sp6E₂ φ he z) (sp6ν₂ φ he z) σ
        (CFSG.Assembly.pCoreOf 2 (normalizer ((ptSub φ z hb e : Subgroup G) : Set G))) C₁ F₁ ν₁ ∧
      ((sp6E₂ φ he z : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative (sp6E₂ φ he z) ∧
        Nat.card (sp6E₂ φ he z) = 512 ∧
        ∀ E' : Subgroup G, (E' : Set G) ⊆ sp6F₂ φ he z → IsMulCommutative E' →
          Nat.card E' = 512 → E' = sp6E₂ φ he z) := by
  intro u f E n Q r θ₁ A₁ D₁ hlam hexp
  obtain ⟨hzC, σ, C₁, F₁, ν₁, hP, hE₂⟩ :=
    ptBase_of_setting hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull hlam hexp
  obtain ⟨-, -, -, -, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨σ', hσsurj, hσker, hσcol, hσ'⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  have hσσ : ∀ n, σ n = σ' n := sigma_eq_of_congr φ he σ σ' hP.hσ hσ'
  have hσeq : σ = σ' := MonoidHom.ext hσσ
  subst hσeq
  have hν₂eq : ∀ d ∈ sp6D₂ φ e z, ∀ d' ∈ sp6D₂ φ e z,
      sp6ν₂ φ he z d = sp6ν₂ φ he z d' ↔ d⁻¹ * d' ∈ radSub φ z e := by
    intro d hd d' hd'
    have hinv : sp6ν₂ φ he z d⁻¹ = sp6ν₂ φ he z d := by
      have h1 := hP.toLagBase.nu_mul hP.hinf hd (inv_mem hd)
      rw [mul_inv_cancel, hP.toLagBase.nu_eq_zero_of_mem hP.hinf (one_mem _)] at h1
      have h2 := eq_neg_of_add_eq_zero_right h1.symm
      rw [h2]
      exact Subtype.ext (by ext i j; exact ZModModule.neg_eq_self _)
    have hm := hP.toLagBase.nu_mul hP.hinf (inv_mem hd) hd'
    rw [hinv] at hm
    constructor
    · intro h0
      have hz0 : sp6ν₂ φ he z (d⁻¹ * d') = 0 := by
        rw [hm, h0]
        exact Subtype.ext (by ext i j; exact ZModModule.add_self _)
      have hzD := mul_mem (inv_mem hd) hd'
      have h3 := hP.hν₂z _ hzD
      have h4 : (d⁻¹ * d')⁻¹ * z * (d⁻¹ * d') = z := by
        rw [h3, hz0]
        exact radHom_z φ he hzC hz
      rw [← hP.hD₂H]
      refine mem_inf.2 ⟨hzD, mem_centralizer_singleton_iff.2 ?_⟩
      calc d⁻¹ * d' * z = d⁻¹ * d' * ((d⁻¹ * d')⁻¹ * z * (d⁻¹ * d')) := by rw [h4]
        _ = z * (d⁻¹ * d') := by group
    · intro hR
      have h0 := hP.toLagBase.nu_eq_zero_of_mem hP.hinf hR
      rw [hm] at h0
      have := eq_neg_of_add_eq_zero_left h0
      rw [this]
      exact Subtype.ext (by ext i j; exact ZModModule.neg_eq_self _)
  obtain ⟨-, hfull₁⟩ := degree64_point_fusion_of_lagrangian he hb hnd φ hzC hP.hsup hP.hinf hz hV
    (κ₂ := 0) hP.hD₂N hP.hD₂n hP.hν₂z hν₂eq
    (fun C => let ⟨c, hc, hcC⟩ := hP.hνs C; ⟨c, hP.toLagBase.C₂D₂ hc, hcC⟩)
    (fun d hd B ε => by rw [zero_smul, add_zero]; exact hP.hpure d hd B ε)
  exact ⟨hzC, σ, C₁, F₁, ν₁, ⟨hP, hσsurj, hσker, hσcol, hfull₁⟩, hE₂⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

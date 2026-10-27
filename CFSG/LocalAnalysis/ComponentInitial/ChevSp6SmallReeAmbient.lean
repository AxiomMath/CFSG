module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSp6EvenLinearAmbientNode
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCASp6SmallReeCore

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

variable {G : Type} [Group G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

namespace ChevSmallRee

theorem nonempty_sp6JLBar_mulEquiv {V₁ : Subgroup G}
    (hconc : Sp6LagrangianLayerConclusion φ he z V₁) :
    Nonempty (sp6JLBar φ he z ≃* GL (Fin 3) (ZMod 2)) := by
  obtain ⟨-, -, -, -, ⟨ι, -, hinj, hrange⟩, -, -, -, -, -, -, hθJ, -⟩ := hconc
  have hθι : Function.Injective ((sp6θ φ he z).comp ι) := by
    intro g g' h
    apply hinj
    exact hθJ (by rw [SetLike.mem_coe, ← hrange]; exact ⟨g, rfl⟩)
      (by rw [SetLike.mem_coe, ← hrange]; exact ⟨g', rfl⟩) h
  have hθrange : ((sp6θ φ he z).comp ι).range = sp6JLBar φ he z := by
    rw [MonoidHom.range_comp, hrange]
    rfl
  exact ⟨((MonoidHom.ofInjective hθι).trans (MulEquiv.subgroupCongr hθrange)).symm⟩

theorem sp6JLBar_isComponentOf {V₁ : Subgroup G}
    (hconc : Sp6LagrangianLayerConclusion φ he z V₁) :
    CFSG.Assembly.IsComponentOf (sp6JLBar φ he z)
      (centralizer ({sp6aBar φ he z} : Set (Sp6Y φ he z))) := by
  obtain ⟨ιJ⟩ := nonempty_sp6JLBar_mulEquiv φ he z hconc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hJC, -, hCaBar, -⟩ := hconc
  have hN : centralizer ({sp6aBar φ he z} : Set (Sp6Y φ he z)) ≤
      normalizer (sp6JLBar φ he z : Set (Sp6Y φ he z)) := by
    rw [← hCaBar]
    refine sup_le ((zpowers_le (G := Sp6Y φ he z)).2 ?_) le_normalizer
    rw [mem_normalizer_iff]
    intro j
    set a := sp6aBar φ he z
    constructor
    · intro hj
      have hc : j * a = a * j := mem_centralizer_singleton_iff.mp (hJC hj)
      have : a * j * a⁻¹ = j := by rw [← hc, mul_inv_cancel_right]
      rwa [this]
    · intro hj
      have hc : a * j * a⁻¹ * a = a * (a * j * a⁻¹) := mem_centralizer_singleton_iff.mp (hJC hj)
      have h2 : j = a * j * a⁻¹ := by
        apply mul_left_cancel (a := a)
        calc a * j = a * j * a⁻¹ * a := by group
          _ = a * (a * j * a⁻¹) := hc
      rwa [h2]
  exact SteinbergCA.isComponentOf_of_normal_of_equiv_GL_three_two hJC
    ((normal_subgroupOf_iff_le_normalizer hJC).2 hN) ιJ

end ChevSmallRee

section Node


theorem standard_binary_symplectic_six_elementary_lagrangian_small_Ree_ambient_exclusion
    [Finite G] (hF : Sp6LagrangianFullOddCoreStmt) (hGs : IsSimpleGroup G)
    (hGnab : ∃ x y : G, x * y ≠ y * x) (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hodd : ∀ t : G, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (_hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (_htype : CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ center L))
    (_hexc : ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ center L))
    (_hres : CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
    (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = zpowers z ∧
    z ∈ centralizer (L : Set G) ∧ L ⊔ zpowers z = centralizer ({z} : Set G) ∧
    L ⊓ zpowers z = ⊥ ∧
    (∃! E₂ : Subgroup G, (E₂ : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E₂ ∧
      Nat.card E₂ = 512) ∧
    IsElementaryAbelian 2 (sp6E₂ φ he z) ∧
    (∀ m ∈ sp6N₂ φ e z, ∀ c ∈ sp6C₂ φ he z, m * c * m⁻¹ ∈ sp6C₂ φ he z) ∧
    Nat.card (sp6C₂ φ he z) = 4096 ∧
    (IsElementaryAbelian 2 (sp6C₂ φ he z) → IsSimpleGroup (sp6Dstar φ he z) →
      (∃ x y : sp6Dstar φ he z, x * y ≠ y * x) →
      ∀ ℓ e' : ℕ, ¬ CFSG.Blueprint.ReeTitsModel (sp6Dstar φ he z) .twistedG2 ℓ e' ∧
        ¬ CFSG.Blueprint.LieModel (sp6Dstar φ he z) .twistedG2 0 ℓ e') := by
  obtain ⟨hTz, hzC, hsup, hinf, hE₂F, hE₂ab, hE₂card, hE₂uniq, hE₂el, hC₂N, hC₂card, hrest⟩ :=
    SteinbergBM.sp6_even_linear_branch φ he z hF hGs hGnab hKP hL hodd hZ hmodel T hT hzT hz hb
      hnd hV hfull
  refine ⟨hTz, hzC, hsup, hinf, ⟨sp6E₂ φ he z, ⟨hE₂F, hE₂ab, hE₂card⟩,
    fun E' ⟨h1, h2, h3⟩ => hE₂uniq E' h1 h2 h3⟩, hE₂el, hC₂N, hC₂card,
    fun hC₂el hDs hDn ℓ e' => ?_⟩
  obtain ⟨-, -, -, -, V₁, hconc⟩ := hrest hC₂el
  have hJcomp := ChevSmallRee.sp6JLBar_isComponentOf φ he z hconc
  have hJGL := ChevSmallRee.nonempty_sp6JLBar_mulEquiv φ he z hconc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, haBar2, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, hCD, -⟩ := hconc
  have : (sp6Dstar φ he z).Normal := Subgroup.normalClosure_normal
  exact SteinbergCA.not_reeTitsModel_twistedG2_of_GL_three_two_component hDs hDn hCD haBar2
    (fun x hx => Subgroup.subset_normalClosure hx) hJcomp hJGL ℓ e'

end Node

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

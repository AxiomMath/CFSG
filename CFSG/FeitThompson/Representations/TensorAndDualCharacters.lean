module
public import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped ComplexConjugate

namespace CFSG.FeitThompson

open Module TensorProduct

namespace Representation

variable {k G V W L : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup L] [Module k L]

theorem equiv_apply_apply {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) (g : G) (v : V) : e.toLinearEquiv (ρ g v) = σ g (e.toLinearEquiv v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v

def equivSubrepresentationOrderIso {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U := ⟨U.toSubmodule.map (e.toLinearEquiv : V →ₗ[k] W), fun g v hv => by
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨ρ g u, U.apply_mem_toSubmodule g hu, equiv_apply_apply e g u⟩⟩
  invFun U := ⟨U.toSubmodule.comap (e.toLinearEquiv : V →ₗ[k] W), fun g v hv => by
    change e.toLinearEquiv (ρ g v) ∈ U.toSubmodule
    rw [equiv_apply_apply e g v]
    exact U.apply_mem_toSubmodule g hv⟩
  left_inv _ :=
    Subrepresentation.ext (Submodule.comap_map_eq_of_injective e.toLinearEquiv.injective _)
  right_inv _ :=
    Subrepresentation.ext (Submodule.map_comap_eq_of_surjective e.toLinearEquiv.surjective _)
  map_rel_iff' := Submodule.map_le_map_iff_of_injective e.toLinearEquiv.injective _ _

theorem isIrreducible_of_equiv {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) (h : ρ.IsIrreducible) : σ.IsIrreducible :=
  (equivSubrepresentationOrderIso e).symm.isSimpleOrder

theorem exists_monoidHom_units_of_finrank_eq_one (σ : Representation k G L)
    (h : finrank k L = 1) : ∃ χ : G →* kˣ, ∀ (g : G) (v : L), σ g v = (χ g : k) • v := by
  set E := LinearEquiv.smul_id_of_finrank_eq_one (R := k) h with hE
  set c : G → k := fun g => E.symm (σ g) with hcdef
  have hc : ∀ g, σ g = c g • (LinearMap.id : L →ₗ[k] L) := by
    intro g
    rw [hcdef]
    have h1 : E (E.symm (σ g)) = σ g := E.apply_symm_apply _
    rw [hE, LinearEquiv.smul_id_of_finrank_eq_one_apply] at h1
    exact h1.symm
  have hinj : ∀ a b : k, a • (LinearMap.id : L →ₗ[k] L) = b • LinearMap.id → a = b := by
    intro a b hab
    refine E.injective ?_
    rw [hE, LinearEquiv.smul_id_of_finrank_eq_one_apply,
      LinearEquiv.smul_id_of_finrank_eq_one_apply]
    exact hab
  have hone : c 1 = 1 := by
    refine hinj _ _ ?_
    rw [← hc, σ.map_one, one_smul, Module.End.one_eq_id]
  have hmul : ∀ g g' : G, c (g * g') = c g * c g' := by
    intro g g'
    refine hinj _ _ ?_
    rw [← hc, σ.map_mul, hc g, hc g']
    ext v
    simp [smul_smul, mul_comm]
  refine ⟨MonoidHom.toHomUnits ⟨⟨c, hone⟩, hmul⟩, fun g v => ?_⟩
  rw [MonoidHom.coe_toHomUnits]
  conv_lhs => rw [hc g]
  simp

def twist (ρ : Representation k G V) (χ : G →* kˣ) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, ρ.map_mul]
    rw [smul_mul_assoc, mul_smul, mul_smul_comm]

@[simp]
theorem twist_apply (ρ : Representation k G V) (χ : G →* kˣ) (g : G) :
    twist ρ χ g = (χ g : k) • ρ g := (rfl)

theorem twist_apply_apply (ρ : Representation k G V) (χ : G →* kˣ) (g : G) (v : V) :
    twist ρ χ g v = (χ g : k) • ρ g v := by rw [twist_apply, LinearMap.smul_apply]

theorem character_twist (ρ : Representation k G V) (χ : G →* kˣ) (g : G) :
    (twist ρ χ).character g = (χ g : k) * ρ.character g := by
  rw [Representation.character, twist_apply, map_smul, smul_eq_mul, Representation.character]

def subrepresentationTwistOrderIso (ρ : Representation k G V) (χ : G →* kˣ) :
    Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule g hv
    rw [twist_apply_apply] at h
    simpa [smul_smul] using U.toSubmodule.smul_mem ((χ g : k)⁻¹) h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => by
    rw [twist_apply_apply]
    exact U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule g hv)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem IsIrreducible.twist {ρ : Representation k G V} (h : ρ.IsIrreducible) (χ : G →* kˣ) :
    (Representation.twist ρ χ).IsIrreducible :=
  (subrepresentationTwistOrderIso ρ χ).isSimpleOrder

noncomputable def equivTprodOfFinrankEqOne (ρ : Representation k G V) (σ : Representation k G L)
    {χ : G →* kˣ} (hχ : ∀ (g : G) (v : L), σ g v = (χ g : k) • v) (e : L ≃ₗ[k] k) :
    (ρ.tprod σ).Equiv (twist ρ χ) :=
  Representation.Equiv.mk
    ((TensorProduct.congr (LinearEquiv.refl k V) e).trans (TensorProduct.rid k V))
    (fun g => by
      apply TensorProduct.ext'
      intro v l
      simp [Representation.tprod_apply, hχ, TensorProduct.smul_tmul', smul_smul, mul_comm])

theorem IsIrreducible.tprod_of_finrank_eq_one {ρ : Representation k G V} (h : ρ.IsIrreducible)
    (σ : Representation k G L) (hL : finrank k L = 1) : (ρ.tprod σ).IsIrreducible := by
  obtain ⟨χ, hχ⟩ := exists_monoidHom_units_of_finrank_eq_one σ hL
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one (R := k) (M := L) hL
  exact isIrreducible_of_equiv (equivTprodOfFinrankEqOne ρ σ hχ e.symm).symm
    (IsIrreducible.twist h χ)

theorem character_dual_eq_conj {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) {g : G} (hg : IsOfFinOrder g) :
    ρ.dual.character g = conj (ρ.character g) := by
  rw [Representation.char_dual, Representation.character_inv ρ hg]

theorem character_dual_eq_conj_of_finite [Finite G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ρ.dual.character = conj ∘ ρ.character :=
  funext fun g => character_dual_eq_conj ρ (isOfFinOrder_of_finite g)

end Representation

end CFSG.FeitThompson

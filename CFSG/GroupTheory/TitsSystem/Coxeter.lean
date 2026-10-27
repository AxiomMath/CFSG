module

public import CFSG.GroupActions.ExchangeCoxeter
public import Mathlib.GroupTheory.Coxeter.Basic

public noncomputable section

namespace CFSG.GroupTheory.TitsSystem

open CFSG.GroupActions.Exchange

variable {W : Type*} [Group W] {S : Set W}

@[expose] def orderMatrix (hS2 : ∀ s ∈ S, orderOf s = 2) : CoxeterMatrix S where
  M := Matrix.of fun s t : S => orderOf ((s : W) * t)
  isSymm := by
    refine Matrix.IsSymm.ext fun s t => ?_
    simp only [Matrix.of_apply]
    rw [← orderOf_inv, mul_inv_rev, inv_eq_of_mul_eq_one_right (coe_mul_self_eq_one hS2 s),
      inv_eq_of_mul_eq_one_right (coe_mul_self_eq_one hS2 t)]
  diagonal s := by
    simp only [Matrix.of_apply]
    rw [coe_mul_self_eq_one hS2 s, orderOf_one]
  off_diagonal s t hst := by
    simp only [Matrix.of_apply]
    intro h1
    apply hst
    have h := orderOf_eq_one_iff.1 h1
    have ht : (t : W) = (s : W)⁻¹ := (eq_inv_of_mul_eq_one_right h)
    rw [inv_eq_of_mul_eq_one_right (coe_mul_self_eq_one hS2 s)] at ht
    exact Subtype.ext ht.symm

theorem exists_coxeterSystem (hS2 : ∀ s ∈ S, orderOf s = 2) (hgen : Subgroup.closure S = ⊤)
    (hex : ExchangeCondition S) :
    ∃ cs : CoxeterSystem (orderMatrix hS2) W, ∀ s : S, cs.simple s = s := by
  set M := orderMatrix hS2 with hM
  let cs₀ := M.toCoxeterSystem
  have hlift : M.IsLiftable (fun s : S => (s : W)) := fun s t => pow_orderOf_eq_one _
  let φ : M.Group →* W := cs₀.lift ⟨fun s => (s : W), hlift⟩
  have hφ : ∀ s : S, φ (M.simple s) = s := fun s => cs₀.lift_apply_simple hlift s
  obtain ⟨ψ, hψ, -⟩ := exchange_coxeter_universal_property hS2 hgen hex (M := M.Group)
    (fun s => M.simple s) (fun s => by rw [sq]; exact cs₀.simple_mul_simple_self s)
    (fun s t _ _ => (altProd_eq_altProd_iff (cs₀.simple_mul_simple_self s)
      (cs₀.simple_mul_simple_self t)).2 (cs₀.simple_mul_simple_pow s t))
  have h1 : ψ.comp φ = MonoidHom.id M.Group := cs₀.ext_simple fun s => by
    change ψ (φ (M.simple s)) = M.simple s
    rw [hφ, hψ]
  have h2 : φ.comp ψ = MonoidHom.id W := MonoidHom.eq_of_eqOn_dense hgen fun x hx => by
    change φ (ψ (⟨x, hx⟩ : S)) = x
    rw [hψ, hφ]
  refine ⟨⟨MonoidHom.toMulEquiv ψ φ h2 h1⟩, fun s => ?_⟩
  exact hφ s

end CFSG.GroupTheory.TitsSystem

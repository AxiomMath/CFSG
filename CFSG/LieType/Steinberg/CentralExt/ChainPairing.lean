module

public import CFSG.LieType.Steinberg.CentralExt.SpinTorus

public section

open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.ChainPairing

open CFSG.LieType.Steinberg

attribute [local instance] TorusLift.centerCommGroup

theorem list_eq_singleton {α : Type*} {l : List α} (hl : l.Nodup) {a : α}
    (h : ∀ p, p ∈ l ↔ p = a) : l = [a] := by
  rcases l with _ | ⟨b, l⟩
  · exact absurd ((h a).2 rfl) (List.not_mem_nil)
  · have hb : b = a := (h b).1 List.mem_cons_self
    subst hb
    rcases l with _ | ⟨c, l⟩
    · rfl
    · have hc : c = b := (h c).1 (List.mem_cons_of_mem _ List.mem_cons_self)
      subst hc
      exact absurd List.mem_cons_self (List.nodup_cons.1 hl).1

theorem list_eq_nil {α : Type*} {l : List α} (h : ∀ p, p ∉ l) : l = [] :=
  List.eq_nil_iff_forall_not_mem.2 h

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {k : Type*} [Field k]
  {K : Type*} [Group K] {x : (ι → ℤ) → k → K} {O : CommOrder Φ}
  {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ}

theorem commute_of_list_eq_nil (hC : CommutatorFormula x O C) {α β : ι → ℤ} (hα : α ∈ Φ.roots)
    (hβ : β ∈ Φ.roots) (hαβ : α + β ≠ 0) (h : O.list α β = []) (c d : k) :
    x α c * x β d = x β d * x α c := by
  have := hC α hα β hβ hαβ c d
  rw [h, List.map_nil, List.prod_nil] at this
  exact commutatorElement_eq_one_iff_mul_comm.1 this

theorem commutatorElement_of_list_eq_single (hC : CommutatorFormula x O C) {α β : ι → ℤ}
    (hα : α ∈ Φ.roots) (hβ : β ∈ Φ.roots) (hαβ : α + β ≠ 0) (h : O.list α β = [(1, 1)])
    (c d : k) : ⁅x α c, x β d⁆ = x (α + β) ((C α β (1, 1) : k) * c * d) := by
  rw [hC α hα β hβ hαβ c d, h]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_smul,
    pow_one]

variable {E : Type*} [Group E] {π : E →* K}

theorem commPairing_eq_zero_of_chain (hcen : π.ker ≤ Subgroup.center E)
    (hπ : Function.Surjective π) (hC : CommutatorFormula x O C) {α β : ι → ℤ}
    (hxadd : ∀ s t, x (α + β) (s + t) = x (α + β) s * x (α + β) t) (hα : α ∈ Φ.roots)
    (hβ : β ∈ Φ.roots) (hγ : α + β ∈ Φ.roots) (hαβ : α + β ≠ 0) (h1 : O.list α β = [(1, 1)])
    (hu : (C α β (1, 1) : k) ≠ 0) (hγα : α + β + α ≠ 0) (hγβ : α + β + β ≠ 0)
    (h2 : O.list (α + β) α = []) (h3 : O.list (α + β) β = []) :
    TorusLift.commPairing hcen hπ hxadd = 0 := by
  refine AddMonoidHom.ext fun s => AddMonoidHom.ext fun t => ?_
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [TorusLift.commPairing_apply, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, toMul_zero,
    Subgroup.coe_one]
  set a := TorusLift.lift hπ (x α ((C α β (1, 1) : k)⁻¹ * s))
  set b := TorusLift.lift hπ (x β 1)
  have hab : π ⁅a, b⁆ = x (α + β) s := by
    rw [map_commutatorElement, TorusLift.map_lift, TorusLift.map_lift,
      commutatorElement_of_list_eq_single hC hα hβ hαβ h1, mul_one, ← mul_assoc,
      mul_inv_cancel₀ hu, one_mul]
  rw [TorusLift.commutatorElement_eq_of_map_eq hcen ((TorusLift.map_lift hπ _).trans hab.symm)
    rfl, commutatorElement_eq_one_iff_mul_comm]
  refine (SpinTorus.commute_commutatorElement_of_central hcen ?_ ?_).symm
  · rw [TorusLift.map_lift, TorusLift.map_lift]
    exact commute_of_list_eq_nil hC hγ hα hγα h2 _ _
  · rw [TorusLift.map_lift, TorusLift.map_lift]
    exact commute_of_list_eq_nil hC hγ hβ hγβ h3 _ _

end CFSG.LieType.Steinberg.CentralExt.ChainPairing

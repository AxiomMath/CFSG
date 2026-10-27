module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionCentralizer

public section

namespace CFSG.GH74.GLS.IVK

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

@[expose] noncomputable def barEquiv (h : UnitaryFieldData p f E) : E ≃+* E :=
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩

theorem barEquiv_apply (h : UnitaryFieldData p f E) (c : E) : barEquiv h c = h.bar c := rfl

theorem barEquiv_ne_one (h : UnitaryFieldData p f E) : barEquiv h ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  exact hc (by rw [← barEquiv_apply, h1]; rfl)

section UnitaryOp

variable {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

theorem unitaryOp_mul (S S' : sesqUnitaryGroup B) :
    unitaryOp (S * S') = unitaryOp S * unitaryOp S' := rfl

theorem unitaryOp_inv_apply (S : sesqUnitaryGroup B) (v : V) :
    unitaryOp S⁻¹ (unitaryOp S v) = v := by
  have h1 : unitaryOp S⁻¹ * unitaryOp S = 1 := by rw [← unitaryOp_mul, inv_mul_cancel]; rfl
  exact LinearMap.congr_fun h1 v

theorem unitaryOp_apply_inv (S : sesqUnitaryGroup B) (v : V) :
    unitaryOp S (unitaryOp S⁻¹ v) = v := by
  have h1 : unitaryOp S * unitaryOp S⁻¹ = 1 := by rw [← unitaryOp_mul, mul_inv_cancel]; rfl
  exact LinearMap.congr_fun h1 v

theorem unitaryOp_injective (S : sesqUnitaryGroup B) : Function.Injective (unitaryOp S) := by
  intro x x' hxx
  rw [← unitaryOp_inv_apply S x, hxx, unitaryOp_inv_apply S x']

end UnitaryOp

structure PairedSL (h : UnitaryFieldData p f E) (B : V →ₛₗ[h.bar] V →ₗ[E] E)
    (Y : Subgroup (sesqUnitaryGroup B)) where
  T : sesqUnitaryGroup B
  l : E
  l_ne : l ≠ 0
  norm_l : h.norm l = -1
  Vp : Submodule E V
  Vm : Submodule E V
  isCompl : IsCompl Vp Vm
  Vm_ne : Vm ≠ ⊥
  T_p : ∀ v ∈ Vp, unitaryOp T v = l • v
  T_m : ∀ v ∈ Vm, unitaryOp T v = -(l • v)
  iso_p : ∀ v ∈ Vp, ∀ w ∈ Vp, B v w = 0
  pair_m : ∀ w ∈ Vm, (∀ v ∈ Vp, B v w = 0) → w = 0
  cp : Vp ≃ₗ[E] (Fin 2 → E)
  surj : ∀ g₀ : SpecialLinearGroup (Fin 2) E, ∃ y ∈ Y, ∀ u : Fin 2 → E,
    ((cp.symm ((g₀ : Matrix (Fin 2) (Fin 2) E) *ᵥ u) : Vp) : V) =
      unitaryOp y ((cp.symm u : Vp) : V)

namespace PairedSL

variable {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E} {Y : Subgroup (sesqUnitaryGroup B)}
  (P : PairedSL h B Y)

theorem exists_ne_zero : ∃ v ∈ P.Vp, v ≠ 0 := by
  refine ⟨((P.cp.symm (Pi.single 0 1) : P.Vp) : V), Subtype.coe_prop _, fun h0 => ?_⟩
  have h1 : P.cp.symm (Pi.single 0 1) = 0 := Subtype.ext h0
  have h2 : (Pi.single 0 1 : Fin 2 → E) = 0 := by
    have := congrArg P.cp h1
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  have h3 := congrFun h2 0
  simp at h3

theorem T_sq (v : V) : unitaryOp P.T (unitaryOp P.T v) = (P.l ^ 2) • v := by
  obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp P.isCompl.codisjoint v
  have e1 : unitaryOp P.T (unitaryOp P.T x) = P.l ^ 2 • x := by
    rw [P.T_p x hx, map_smul, P.T_p x hx, smul_smul, pow_two]
  have e2 : unitaryOp P.T (unitaryOp P.T y) = P.l ^ 2 • y := by
    rw [P.T_m y hy, map_neg, map_smul, P.T_m y hy, smul_neg, smul_smul, neg_neg, pow_two]
  rw [map_add, map_add, e1, e2, smul_add]

theorem mem_Vp_of_eigen (h2 : (2 : E) ≠ 0) {x : V} (hx : unitaryOp P.T x = P.l • x) :
    x ∈ P.Vp := by
  obtain ⟨a, b, ha, hb, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp P.isCompl.codisjoint x
  rw [map_add, P.T_p a ha, P.T_m b hb, smul_add] at hx
  have h4 : -(P.l • b) = P.l • b := add_left_cancel hx
  have h5 : (2 : E) • (P.l • b) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h4]
    exact neg_add_cancel _
  have h6 : P.l • b = 0 := (smul_eq_zero.mp h5).resolve_left h2
  have h7 : b = 0 := (smul_eq_zero.mp h6).resolve_left P.l_ne
  rw [h7, add_zero]
  exact ha

theorem mem_Vm_of_eigen (h2 : (2 : E) ≠ 0) {x : V} (hx : unitaryOp P.T x = -(P.l • x)) :
    x ∈ P.Vm := by
  obtain ⟨a, b, ha, hb, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp P.isCompl.codisjoint x
  rw [map_add, P.T_p a ha, P.T_m b hb, smul_add, neg_add] at hx
  have h4 : P.l • a = -(P.l • a) := by
    have := add_right_cancel hx
    exact this
  have h5 : (2 : E) • (P.l • a) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h4]
    exact add_neg_cancel _
  have h6 : P.l • a = 0 := (smul_eq_zero.mp h5).resolve_left h2
  have h7 : a = 0 := (smul_eq_zero.mp h6).resolve_left P.l_ne
  rw [h7, zero_add]
  exact hb

@[expose] def vec (u : Fin 2 → E) : V := ((P.cp.symm u : P.Vp) : V)

theorem vec_mem (u : Fin 2 → E) : P.vec u ∈ P.Vp := Subtype.coe_prop _

theorem vec_add (u u' : Fin 2 → E) : P.vec (u + u') = P.vec u + P.vec u' := by
  simp [vec]

theorem vec_zero : P.vec 0 = 0 := by simp [vec]

theorem vec_smul (a : E) (u : Fin 2 → E) : P.vec (a • u) = a • P.vec u := by
  simp [vec]

theorem vec_cp (v : P.Vp) : P.vec (P.cp v) = (v : V) := by
  simp [vec]

theorem vec_injective : Function.Injective P.vec := by
  intro u u' huu
  have h1 : P.cp.symm u = P.cp.symm u' := Subtype.ext huu
  exact P.cp.symm.injective h1

theorem exists_vec {v : V} (hv : v ∈ P.Vp) : ∃ u, P.vec u = v :=
  ⟨P.cp ⟨v, hv⟩, P.vec_cp ⟨v, hv⟩⟩

theorem surj_vec (g₀ : SpecialLinearGroup (Fin 2) E) :
    ∃ y ∈ Y, ∀ u : Fin 2 → E,
      P.vec ((g₀ : Matrix (Fin 2) (Fin 2) E) *ᵥ u) = unitaryOp y (P.vec u) :=
  P.surj g₀

theorem decomp (v : V) : ∃ a ∈ P.Vp, ∃ b ∈ P.Vm, a + b = v := by
  obtain ⟨a, b, ha, hb, hab⟩ := Submodule.codisjoint_iff_exists_add_eq.mp P.isCompl.codisjoint v
  exact ⟨a, ha, b, hb, hab⟩

end PairedSL

end CFSG.GH74.GLS.IVK

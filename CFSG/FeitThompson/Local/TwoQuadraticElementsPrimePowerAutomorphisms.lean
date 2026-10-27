module

public import Mathlib.RepresentationTheory.Irreducible
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
public import CFSG.FeitThompson.Local.PLengthOneNormalComplementElementSubgroup
public import CFSG.FeitThompson.Local.AbelianPlaneCentralizerNoncentralOrbit
import CFSG.FeitThompson.Local.PrimePowerActionFromNormalFactors
import CFSG.FeitThompson.Representations.CentralActionCasesComplementOrderBound
import CFSG.FeitThompson.Local.FrattiniQuotientAutomorphismKernelPGroup
import CFSG.FeitThompson.Representations.QuadraticPrimeElementsPrimePowerImage
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} {A : Type*} [Group A]

section General

variable {P : Type*} [Group P]

theorem isPGroup_range_of_forall_eq_one {ρ : A →* MulAut P} (h : ∀ b : A, ρ b = 1) :
    IsPGroup p ρ.range := by
  intro g
  obtain ⟨b, hb⟩ := g.2
  exact ⟨0, Subtype.ext (by simp [← hb, h b])⟩

end General

section Linearize

variable {P : Type*} [CommGroup P] [Module (ZMod p) (Additive P)]

def autRep (p : ℕ) {A P : Type*} [Group A] [CommGroup P] [Module (ZMod p) (Additive P)]
    (ρ : A →* MulAut P) : Representation (ZMod p) A (Additive P) :=
  (Units.coeHom (Module.End (ZMod p) (Additive P))).comp (mulAutToGL.comp ρ)

@[simp] theorem autRep_apply (ρ : A →* MulAut P) (b : A) (w : Additive P) :
    autRep p ρ b w = Additive.ofMul (ρ b (Additive.toMul w)) :=
  mulAutToGL_apply (p := p) (ρ b) w

theorem autRep_sub_one_apply (ρ : A →* MulAut P) (a : A) (w : Additive P) :
    (autRep p ρ a - 1) w = Additive.ofMul (ρ a (Additive.toMul w) * (Additive.toMul w)⁻¹) := by
  rw [LinearMap.sub_apply, autRep_apply, Module.End.one_apply, ← div_eq_mul_inv, ofMul_div]
  rfl

theorem ker_autRep_asGroupHom (ρ : A →* MulAut P) :
    (autRep p ρ).asGroupHom.ker = ρ.ker := by
  ext b
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : ((autRep p ρ).asGroupHom b : Module.End (ZMod p) (Additive P)) = 1 := by
      rw [h, Units.val_one]
    ext v
    have h2 := congrArg (fun f : Module.End (ZMod p) (Additive P) => f (Additive.ofMul v)) h1
    rw [Representation.asGroupHom_apply, autRep_apply] at h2
    simpa using Additive.ofMul.injective h2
  · intro h
    refine Units.ext ?_
    rw [Representation.asGroupHom_apply, Units.val_one]
    refine LinearMap.ext fun w => ?_
    rw [autRep_apply, h, Module.End.one_apply]
    simp

theorem sq_eq_zero_of_actsQuadratically {ρ : A →* MulAut P} {a : A} (h : ActsQuadratically ρ a) :
    (autRep p ρ a - 1) * (autRep p ρ a - 1) = 0 := by
  refine LinearMap.ext fun w => ?_
  rw [Module.End.mul_apply, autRep_sub_one_apply, autRep_sub_one_apply, LinearMap.zero_apply]
  set v := Additive.toMul w with hv
  have hu : ρ a (v⁻¹ * ρ a v) = v⁻¹ * ρ a v := actsQuadratically_iff_forall.1 h v
  have hcomm : ρ a v * v⁻¹ = v⁻¹ * ρ a v := mul_comm _ _
  rw [show Additive.toMul (Additive.ofMul (ρ a v * v⁻¹)) = ρ a v * v⁻¹ from rfl, hcomm, hu]
  simp

theorem mem_symm_subgroupOrderIsoSubmodule {U : Submodule (ZMod p) (Additive P)} {v : P} :
    v ∈ (subgroupOrderIsoSubmodule p P).symm U ↔ Additive.ofMul v ∈ U := by
  have h := mem_subgroupOrderIsoSubmodule (p := p)
    (L := (subgroupOrderIsoSubmodule p P).symm U) (x := Additive.ofMul v)
  rw [OrderIso.apply_symm_apply] at h
  exact h.symm

theorem isIrreducible_autRep [Fact p.Prime] (ρ : A →* MulAut P) [Nontrivial P]
    (hmin : ∀ N : Subgroup P, IsInvariantSubgroup ρ N → N = ⊥ ∨ N = ⊤) :
    (autRep p ρ).IsIrreducible := by
  have : Nontrivial (Additive P) := ‹Nontrivial P›
  refine isIrreducible_of_forall_eq_bot_or_eq_top _ fun U hU => ?_
  have hN : IsInvariantSubgroup ρ ((subgroupOrderIsoSubmodule p P).symm U) := by
    refine isInvariantSubgroup_of_forall fun b v hv => ?_
    rw [mem_symm_subgroupOrderIsoSubmodule] at hv ⊢
    have h2 := hU b _ hv
    rwa [autRep_apply] at h2
  have hU' : U = subgroupOrderIsoSubmodule p P ((subgroupOrderIsoSubmodule p P).symm U) :=
    (OrderIso.apply_symm_apply _ _).symm
  rcases hmin _ hN with h | h
  · exact Or.inl (by rw [hU', h, map_bot])
  · exact Or.inr (by rw [hU', h, map_top])

theorem isPGroup_range_of_module_of_forall_invariant [Fact p.Prime] [Finite P] [Nontrivial P]
    (hp : p.Prime) (hAodd : Odd (Nat.card A)) (ρ : A →* MulAut P) {x y : A}
    (hgen : Subgroup.closure ({x, y} : Set A) = ⊤)
    (hx : ∃ m, orderOf x ∣ p ^ m) (hy : ∃ m, orderOf y ∣ p ^ m)
    (hxq : ActsQuadratically ρ x) (hyq : ActsQuadratically ρ y)
    (hmin : ∀ N : Subgroup P, IsInvariantSubgroup ρ N → N = ⊥ ∨ N = ⊤) :
    IsPGroup p ρ.range := by
  have hfa : Finite (Additive P) := ‹Finite P›
  have hfd : FiniteDimensional (ZMod p) (Additive P) := Module.Finite.of_finite
  have hirr : (autRep p ρ).IsIrreducible := isIrreducible_autRep ρ hmin
  have hrange : IsPGroup p (autRep p ρ).asGroupHom.range :=
    isPGroup_range_of_quadratic_pElement_generators hp hAodd (autRep p ρ) hgen hx hy
      (sq_eq_zero_of_actsQuadratically hxq) (sq_eq_zero_of_actsQuadratically hyq)
  exact isPGroup_range_of_ker_eq ρ _ (ker_autRep_asGroupHom ρ).symm hrange

end Linearize

theorem isPGroup_range_of_forall_normal_invariant (hp : p.Prime) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (hAodd : Odd (Nat.card A)) (ρ : A →* MulAut P) {x y : A}
    (hgen : Subgroup.closure ({x, y} : Set A) = ⊤)
    (hx : ∃ m, orderOf x ∣ p ^ m) (hy : ∃ m, orderOf y ∣ p ^ m)
    (hxq : ActsQuadratically ρ x) (hyq : ActsQuadratically ρ y)
    (hmin : ∀ N : Subgroup P, N.Normal → IsInvariantSubgroup ρ N → N = ⊥ ∨ N = ⊤) :
    IsPGroup p ρ.range := by
  have hpf := Fact.mk hp
  by_cases hnt : Nontrivial P
  · have hZne : centerTorsionBy P p ≠ ⊥ := centerTorsionBy_ne_bot_of_isPGroup hp hP
    have hZtop : centerTorsionBy P p = ⊤ :=
      (hmin _ inferInstance (isInvariantSubgroup_of_characteristic ρ _)).resolve_left hZne
    have hexp : ∀ v : P, v ^ p = 1 := fun v =>
      pow_eq_one_of_mem_centerTorsionBy (by rw [hZtop]; exact Subgroup.mem_top v)
    have hcen : Subgroup.center P = ⊤ :=
      top_le_iff.1 (hZtop ▸ centerTorsionBy_le_center (R := P) p)
    have hmc : IsMulCommutative P := Subgroup.center_eq_top_iff.1 hcen
    let _ : CommGroup P := hmc.instCommGroup
    let _ : Module (ZMod p) (Additive P) := AddCommGroup.zmodModule (n := p) fun w => by
      calc p • w = Additive.ofMul ((Additive.toMul w) ^ p) := by simp
        _ = 0 := by rw [hexp]; rfl
    exact isPGroup_range_of_module_of_forall_invariant hp hAodd ρ hgen hx hy hxq hyq
      fun N hN => hmin N inferInstance hN
  · have : Subsingleton P := not_nontrivial_iff_subsingleton.1 hnt
    exact isPGroup_range_of_forall_eq_one fun _ => MulEquiv.ext fun _ => Subsingleton.elim _ _

private theorem isPGroup_range_aux (hp : p.Prime) (hAodd : Odd (Nat.card A)) {x y : A}
    (hgen : Subgroup.closure ({x, y} : Set A) = ⊤)
    (hx : ∃ m, orderOf x ∣ p ^ m) (hy : ∃ m, orderOf y ∣ p ^ m) (n : ℕ) :
    ∀ {P : Type*} [Group P] [Finite P], Nat.card P ≤ n → IsPGroup p P →
      ∀ ρ : A →* MulAut P, ActsQuadratically ρ x → ActsQuadratically ρ y →
        IsPGroup p ρ.range := by
  induction n with
  | zero =>
    intro P _ _ hcard _ _ _ _
    exact absurd hcard (by simpa using (Nat.card_pos (α := P)).ne')
  | succ n ih =>
    intro P _ _ hcard hP ρ hxq hyq
    by_cases hmin : ∀ N : Subgroup P, N.Normal → IsInvariantSubgroup ρ N → N = ⊥ ∨ N = ⊤
    · exact isPGroup_range_of_forall_normal_invariant hp hP hAodd ρ hgen hx hy hxq hyq hmin
    ·
      simp only [not_forall] at hmin
      obtain ⟨N, hNnorm, hNinv, hN⟩ := hmin
      have hNbot : N ≠ ⊥ := (not_or.1 hN).1
      have hNtop : N ≠ ⊤ := (not_or.1 hN).2
      have hNn : N.Normal := hNnorm
      have hcardN : Nat.card N ≤ n := by
        have h := natCard_lt_natCard_of_lt_top (H := N) (lt_of_le_of_ne le_top hNtop)
        omega
      have hcardQ : Nat.card (P ⧸ N) ≤ n := by
        have h := natCard_quotient_lt_natCard_of_bot_lt N (lt_of_le_of_ne bot_le (Ne.symm hNbot))
        omega
      refine isPGroup_range_of_isPGroup_factor_ranges hp hP hNinv ?_ ?_
      · exact ih hcardN (hP.to_subgroup N) hNinv.restrictAut (hxq.restrictAut hNinv)
          (hyq.restrictAut hNinv)
      · exact ih hcardQ (hP.to_quotient N) hNinv.quotientAut (hxq.quotientAut hNinv)
          (hyq.quotientAut hNinv)

theorem isPGroup_range_of_quadratic_pElement_generators_of_isPGroup (hp : p.Prime) {P : Type*}
    [Group P] [Finite P] (hP : IsPGroup p P) (hAodd : Odd (Nat.card A)) (ρ : A →* MulAut P)
    {x y : A} (hgen : Subgroup.closure ({x, y} : Set A) = ⊤)
    (hx : ∃ m, orderOf x ∣ p ^ m) (hy : ∃ m, orderOf y ∣ p ^ m)
    (hxq : ActsQuadratically ρ x) (hyq : ActsQuadratically ρ y) :
    IsPGroup p ρ.range :=
  isPGroup_range_aux hp hAodd hgen hx hy (Nat.card P) le_rfl hP ρ hxq hyq

theorem isPGroup_range_of_two_quadratic_pElements (hp : p.Prime) (_hpodd : Odd p) {P : Type*}
    [Group P] [Finite P] (hP : IsPGroup p P) (hAodd : Odd (Nat.card A)) (ρ : A →* MulAut P)
    {x y : A} (hgen : Subgroup.closure ({x, y} : Set A) = ⊤)
    (hx : x ∈ pElements p A) (hy : y ∈ pElements p A)
    (hxq : ActsQuadratically ρ x) (hyq : ActsQuadratically ρ y) :
    IsPGroup p ρ.range := by
  obtain ⟨m, hm⟩ := mem_pElements.1 hx
  obtain ⟨n, hn⟩ := mem_pElements.1 hy
  exact isPGroup_range_of_quadratic_pElement_generators_of_isPGroup hp hP hAodd ρ hgen
    ⟨m, hm ▸ dvd_rfl⟩ ⟨n, hn ▸ dvd_rfl⟩ hxq hyq

end

end CFSG.FeitThompson

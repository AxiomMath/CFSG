module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module

variable {p : ℕ} [Fact p.Prime] {Q : Type*} [AddCommGroup Q] [Module (ZMod p) Q]

@[expose] noncomputable def operatorAlgebra
    (T : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) Q)) :
    Subalgebra (ZMod p) (Module.End (ZMod p) Q) :=
  Algebra.adjoin (ZMod p)
    ((fun g : LinearMap.GeneralLinearGroup (ZMod p) Q => (g : Module.End (ZMod p) Q)) '' T)

variable {T : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) Q)}

theorem commute_of_mem_operatorAlgebra (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    {a : Module.End (ZMod p) Q} (ha : a ∈ operatorAlgebra T)
    {g : LinearMap.GeneralLinearGroup (ZMod p) Q} (hg : g ∈ T) :
    a * (g : Module.End (ZMod p) Q) = g * a := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    rw [← Units.val_mul, ← Units.val_mul, hcomm h hh g hg]
  | algebraMap r => exact Algebra.commutes (A := Module.End (ZMod p) Q) r _
  | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

theorem mul_comm_of_mem_operatorAlgebra (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    {a b : Module.End (ZMod p) Q} (ha : a ∈ operatorAlgebra T) (hb : b ∈ operatorAlgebra T) :
    a * b = b * a := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    exact commute_of_mem_operatorAlgebra hcomm ha hh
  | algebraMap r => exact (Algebra.commutes (A := Module.End (ZMod p) Q) r _).symm
  | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
  | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

theorem ker_invariant (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    {a : Module.End (ZMod p) Q} (ha : a ∈ operatorAlgebra T) :
    ∀ g ∈ T, ∀ w ∈ LinearMap.ker a, (g : Module.End (ZMod p) Q) w ∈ LinearMap.ker a := by
  intro g hg w hw
  rw [LinearMap.mem_ker] at hw ⊢
  have h := congrArg (fun f : Module.End (ZMod p) Q => f w)
    (commute_of_mem_operatorAlgebra hcomm ha hg)
  simp only [Module.End.mul_apply] at h
  rw [h, hw, map_zero]

theorem irreducible_abelian_operator_algebra_field [FiniteDimensional (ZMod p) Q] {n : ℕ}
    (hn : 1 ≤ n) (hdim : finrank (ZMod p) Q = n) (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    (hirr : ∀ W : Submodule (ZMod p) Q,
      (∀ g ∈ T, ∀ w ∈ W, (g : Module.End (ZMod p) Q) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ hF : IsField (operatorAlgebra T),
      Nat.card (operatorAlgebra T) = p ^ n ∧
      letI : Field (operatorAlgebra T) := hF.toField
      letI : Module (operatorAlgebra T) Q :=
        Module.compHom Q ((operatorAlgebra T).val : operatorAlgebra T →+* Module.End (ZMod p) Q)
      finrank (operatorAlgebra T) Q = 1 ∧
      ∀ s : Q, s ≠ 0 → ∃ e : operatorAlgebra T ≃ₗ[operatorAlgebra T] Q,
        ∀ a : operatorAlgebra T, e a = (a : Module.End (ZMod p) Q) s := by
  classical
  set F := operatorAlgebra T with hFdef
  have : Nontrivial Q := Module.nontrivial_of_finrank_pos (R := ZMod p) (by omega)
  have : Finite (ZMod p) := inferInstance
  have : Finite Q := Module.finite_of_finite (ZMod p)
  have : Finite (Module.End (ZMod p) Q) := Module.finite_of_finite (ZMod p)
  have : Finite F := Subtype.finite
  have hinj : ∀ a ∈ F, a ≠ 0 → LinearMap.ker a = ⊥ := by
    intro a ha ha0
    rcases hirr _ (ker_invariant hcomm ha) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) ha0
  have hev : ∀ s : Q, s ≠ 0 → Function.Bijective fun a : F => (a : Module.End (ZMod p) Q) s := by
    intro s hs
    refine ⟨fun a b hab => ?_, fun q => ?_⟩
    · by_contra hne
      have hne' : ((a : Module.End (ZMod p) Q) - (b : Module.End (ZMod p) Q)) ≠ 0 := fun h =>
        hne (Subtype.ext (sub_eq_zero.1 h))
      have hk := hinj _ (sub_mem a.2 b.2) hne'
      have : s ∈ LinearMap.ker ((a : Module.End (ZMod p) Q) - (b : Module.End (ZMod p) Q)) := by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
        exact hab
      rw [hk] at this
      exact hs ((Submodule.mem_bot _).1 this)
    ·
      let W : Submodule (ZMod p) Q :=
        { carrier := {x | ∃ a ∈ F, a s = x}
          add_mem' := by
            rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
            exact ⟨a + b, add_mem ha hb, rfl⟩
          zero_mem' := ⟨0, zero_mem _, rfl⟩
          smul_mem' := by
            rintro c _ ⟨a, ha, rfl⟩
            exact ⟨c • a, Subalgebra.smul_mem _ ha c, rfl⟩ }
      have hW : W = ⊤ := by
        rcases hirr W (by
          rintro g hg _ ⟨a, ha, rfl⟩
          exact ⟨(g : Module.End (ZMod p) Q) * a, mul_mem (Algebra.subset_adjoin ⟨g, hg, rfl⟩)
            ha, rfl⟩) with h | h
        · exfalso
          have : s ∈ W := ⟨1, one_mem _, rfl⟩
          rw [h] at this
          exact hs ((Submodule.mem_bot _).1 this)
        · exact h
      have hq : q ∈ W := hW ▸ Submodule.mem_top
      obtain ⟨a, ha, rfl⟩ := hq
      exact ⟨⟨a, ha⟩, rfl⟩
  have hF : IsField F := by
    refine ⟨⟨0, 1, fun h => ?_⟩, fun {a b} => Subtype.ext
      (mul_comm_of_mem_operatorAlgebra hcomm a.2 b.2), fun {a} ha => ?_⟩
    · have h1 := congrArg (fun x : F => (x : Module.End (ZMod p) Q)) h
      simp only [ZeroMemClass.coe_zero, OneMemClass.coe_one] at h1
      obtain ⟨v, hv⟩ := exists_ne (0 : Q)
      exact hv (by simpa using (congrArg (fun f : Module.End (ZMod p) Q => f v) h1).symm)
    ·
      have ha0 : (a : Module.End (ZMod p) Q) ≠ 0 := fun h => ha (Subtype.ext h)
      have hk := hinj _ a.2 ha0
      have hmul : Function.Injective fun b : F => a * b := by
        intro b c hbc
        have h' : (a : Module.End (ZMod p) Q) * b = a * c := congrArg Subtype.val hbc
        apply Subtype.ext
        apply LinearMap.ext
        intro v
        have := congrArg (fun f : Module.End (ZMod p) Q => f v) h'
        simp only [Module.End.mul_apply] at this
        exact LinearMap.ker_eq_bot.1 hk this
      obtain ⟨b, hb⟩ := Finite.surjective_of_injective hmul 1
      exact ⟨b, hb⟩
  refine ⟨hF, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := exists_ne (0 : Q)
    rw [Nat.card_congr (Equiv.ofBijective _ (hev s hs)),
      Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, hdim]
  · let : Field F := hF.toField
    let : Module F Q := Module.compHom Q (F.val : F →+* Module.End (ZMod p) Q)
    have hev' : ∀ s : Q, s ≠ 0 → ∃ e : F ≃ₗ[F] Q,
        ∀ a : F, e a = (a : Module.End (ZMod p) Q) s := by
      intro s hs
      let f : F →ₗ[F] Q :=
        { toFun := fun a => (a : Module.End (ZMod p) Q) s
          map_add' := fun a b => rfl
          map_smul' := fun b a => rfl }
      exact ⟨LinearEquiv.ofBijective f (hev s hs), fun a => rfl⟩
    obtain ⟨s, hs⟩ := exists_ne (0 : Q)
    obtain ⟨e, -⟩ := hev' s hs
    exact ⟨by rw [← e.finrank_eq, Module.finrank_self], hev'⟩

end CFSG.LocalAnalysis.ComponentInitial

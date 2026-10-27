module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Module

theorem card_mulEquiv_eq_of_elemAb16 {F : Type} [Group F] [Finite F]
    (hc : ∀ x y : F, x * y = y * x) (hs : ∀ x : F, x * x = 1) (hcard : Nat.card F = 16) :
    Nat.card (F ≃* F) = 20160 := by
  classical
  let _ : CommGroup F := { ‹Group F› with mul_comm := hc }
  have _ : Fintype F := Fintype.ofFinite F
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ∀ x : Additive F, (2 : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    simp [pow_two, hs]
  let _ : Module (ZMod 2) (Additive F) := AddCommGroup.zmodModule h2
  have _ : Fintype (Additive F) := inferInstanceAs (Fintype F)
  have hfin : Module.finrank (ZMod 2) (Additive F) = 4 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive F)
    have h3 : Fintype.card (Additive F) = 16 := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    rw [h3, ZMod.card] at h1
    have : (2:ℕ) ^ 4 = 2 ^ Module.finrank (ZMod 2) (Additive F) := by
      rw [← h1]; norm_num
    exact (Nat.pow_right_injective (le_refl 2) this).symm
  have _ : Module.Finite (ZMod 2) (Additive F) := Module.Finite.of_finite
  let b : Basis (Fin 4) (ZMod 2) (Additive F) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive F) hfin
  let lin : (F ≃* F) → (Additive F →ₗ[ZMod 2] Additive F) := fun σ =>
    AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive σ).toAddMonoidHom
  have hlin_inj : ∀ σ : F ≃* F, Function.Injective (lin σ) := by
    intro σ x y hxy
    exact (MulEquiv.toAdditive σ).injective hxy
  let g : (F ≃* F) → {s : Fin 4 → Additive F // LinearIndependent (ZMod 2) s} := fun σ =>
    ⟨fun i => lin σ (b i), b.linearIndependent.map' (lin σ)
      (LinearMap.ker_eq_bot.2 (hlin_inj σ))⟩
  have hg : Function.Injective g := by
    intro σ τ hστ
    have h1 : ∀ i, lin σ (b i) = lin τ (b i) := fun i => congrFun (congrArg Subtype.val hστ) i
    have h2 : lin σ = lin τ := b.ext h1
    ext x
    have := LinearMap.congr_fun h2 (Additive.ofMul x)
    exact congrArg Additive.toMul this
  have hgs : Function.Surjective g := by
    rintro ⟨s, hs'⟩
    let b' : Basis (Fin 4) (ZMod 2) (Additive F) :=
      basisOfLinearIndependentOfCardEqFinrank hs' (by simp [hfin])
    let φ : Additive F ≃ₗ[ZMod 2] Additive F := b.equiv b' (Equiv.refl (Fin 4))
    refine ⟨(MulEquiv.toAdditive).symm φ.toAddEquiv, Subtype.ext (funext fun i => ?_)⟩
    show lin ((MulEquiv.toAdditive).symm φ.toAddEquiv) (b i) = s i
    have : lin ((MulEquiv.toAdditive).symm φ.toAddEquiv) = φ.toLinearMap := by
      ext x
      rfl
    rw [this]
    show φ (b i) = s i
    rw [Basis.equiv_apply]
    simp [b']
  have hcardLI := card_linearIndependent (K := ZMod 2) (V := Additive F) (k := 4) hfin.ge
  rw [Nat.card_congr (Equiv.ofBijective g ⟨hg, hgs⟩), hcardLI, hfin, ZMod.card]
  simp [Fin.prod_univ_four]

end CFSG.EvenSporadicStandard.M23Std

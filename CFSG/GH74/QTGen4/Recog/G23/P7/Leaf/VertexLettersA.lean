module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.VL

@[expose] def zpw {X : Type*} [Group X] (x : X) (n : ZMod 3) : X := x ^ n.val

@[ext] structure VG (c : ZMod 3) where
  s : ZMod 3
  p₁ : ZMod 3
  p₂ : ZMod 3
  p₃ : ZMod 3
  p₄ : ZMod 3
deriving DecidableEq

namespace VG

variable {c : ZMod 3}

instance : Mul (VG c) :=
  ⟨fun x y => ⟨x.s + y.s - c * x.p₄ * y.p₂, x.p₁ + y.p₁, x.p₂ + y.p₂, x.p₃ + y.p₃, x.p₄ + y.p₄⟩⟩

instance : One (VG c) := ⟨⟨0, 0, 0, 0, 0⟩⟩

instance : Inv (VG c) :=
  ⟨fun x => ⟨-x.s - c * x.p₂ * x.p₄, -x.p₁, -x.p₂, -x.p₃, -x.p₄⟩⟩

theorem mul_def (x y : VG c) :
    x * y = ⟨x.s + y.s - c * x.p₄ * y.p₂, x.p₁ + y.p₁, x.p₂ + y.p₂, x.p₃ + y.p₃, x.p₄ + y.p₄⟩ :=
  rfl

theorem one_def : (1 : VG c) = ⟨0, 0, 0, 0, 0⟩ := rfl

theorem inv_def (x : VG c) :
    x⁻¹ = ⟨-x.s - c * x.p₂ * x.p₄, -x.p₁, -x.p₂, -x.p₃, -x.p₄⟩ := rfl

instance : Group (VG c) where
  mul_assoc x y w := by
    cases x; cases y; cases w
    simp only [mul_def, VG.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring
  one_mul x := by
    cases x
    simp [mul_def, one_def]
  mul_one x := by
    cases x
    simp [mul_def, one_def]
  inv_mul_cancel x := by
    cases x
    simp only [mul_def, inv_def, one_def, VG.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring

def equivProd : VG c ≃ ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 where
  toFun x := (x.s, x.p₁, x.p₂, x.p₃, x.p₄)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv x := by cases x; rfl

instance : Fintype (VG c) := Fintype.ofEquiv _ equivProd.symm

@[expose] def gσ : VG c := ⟨1, 0, 0, 0, 0⟩
@[expose] def g₁ : VG c := ⟨0, 1, 0, 0, 0⟩
@[expose] def g₂ : VG c := ⟨0, 0, 1, 0, 0⟩
@[expose] def g₃ : VG c := ⟨0, 0, 0, 1, 0⟩
@[expose] def g₄ : VG c := ⟨0, 0, 0, 0, 1⟩

@[expose] def ext5 (g₀ g₁ g₂ g₃ g₄ : VG c) (x : VG c) : VG c :=
  zpw g₀ x.s * (zpw g₁ x.p₁ * zpw g₃ x.p₃) * (zpw g₂ x.p₂ * zpw g₄ x.p₄)

@[expose] def tauV (η : VG c) : VG c → VG c := ext5 gσ g₃ g₄ (g₁ * g₃)⁻¹ η

@[expose] def alphaV (η : VG c) : VG c → VG c := ext5 gσ g₁ g₂ (g₁ * g₃) η⁻¹

@[expose] def relV (η : VG c) (x : VG c) : VG c :=
  alphaV η (tauV η (tauV η (alphaV η (alphaV η (tauV η (alphaV η (alphaV η (tauV η (tauV η x)))))))))

theorem classify : ∀ c : ZMod 3, c ≠ 0 → ∀ η : VG c, tauV η η = g₂ → relV η g₄ = g₄ →
    (c = 2 ∧ η = ⟨2, 2, 2, 1, 2⟩) ∨ (c = 2 ∧ η = ⟨2, 1, 2, 2, 2⟩) ∨ (c = 1 ∧ η = ⟨1, 1, 2, 2, 2⟩) ∨
    (c = 1 ∧ η = ⟨1, 2, 2, 1, 2⟩) ∨ (c = 1 ∧ η = ⟨1, 0, 2, 0, 2⟩) ∨ (c = 2 ∧ η = ⟨2, 0, 2, 0, 2⟩) := by
  decide +kernel

theorem eq_prod : ∀ c : ZMod 3, ∀ x : VG c,
    x = zpw gσ x.s * (zpw g₁ x.p₁ * zpw g₃ x.p₃) * (zpw g₂ x.p₂ * zpw g₄ x.p₄) := by
  decide +kernel

theorem central_aux : ∀ c : ZMod 3, c ≠ 0 → ∀ x : VG c, x * g₂ = g₂ * x → x * g₄ = g₄ * x →
    x.p₂ = 0 ∧ x.p₄ = 0 := by
  decide +kernel

theorem sigma_aux : ∀ c : ZMod 3, ∀ x : VG c, x.p₂ = 0 → x.p₄ = 0 →
    ext5 gσ g₁⁻¹ g₂⁻¹ g₃⁻¹ g₄⁻¹ x = x⁻¹ → x.s = 0 := by
  decide +kernel

theorem d2_aux : ∀ c : ZMod 3, ∀ p₁ p₃ : ZMod 3, ∀ η : VG c,
    ext5 gσ g₃ g₄ (⟨0, p₁, 0, p₃, 0⟩ : VG c) η ⟨0, p₁, 0, p₃, 0⟩ = g₁ → p₁ = 2 ∧ p₃ = 2 := by
  decide +kernel

@[expose] def hardUval (T : VG c → VG c) (y₀ y₁ y₂ : VG c) : VG c :=
  y₁ * y₀⁻¹ * y₂⁻¹ * T y₂⁻¹ * T (T (y₂⁻¹ * y₁⁻¹))

@[expose] def hardSval (T : VG c → VG c) (y₀ y₂ : VG c) : VG c :=
  y₂⁻¹ * y₀ * T y₂⁻¹ * T (T y₂⁻¹)

theorem check_k0 : hardUval (tauV (⟨2, 2, 2, 1, 2⟩ : VG 2)) gσ g₁ g₂ = 1 := by decide +kernel

theorem check_k1a : hardUval (tauV (⟨2, 1, 2, 2, 2⟩ : VG 2)) gσ g₁ g₂⁻¹ = 1 := by decide +kernel

theorem check_k1b : hardUval (tauV (⟨2, 1, 2, 2, 2⟩ : VG 2)) gσ g₁⁻¹ g₂ = 1 := by decide +kernel

theorem check_k2 : hardUval (fun x => tauV (⟨1, 1, 2, 2, 2⟩ : VG 1) (tauV ⟨1, 1, 2, 2, 2⟩ x))
    gσ g₁ g₂ = 1 := by decide +kernel

theorem check_k3 : hardUval (tauV (⟨1, 2, 2, 1, 2⟩ : VG 1)) gσ⁻¹ g₁ g₂ = 1 := by decide +kernel

theorem check_k4 : hardSval (tauV (⟨1, 0, 2, 0, 2⟩ : VG 1)) gσ g₂ = 1 := by decide +kernel

theorem check_k5 : hardSval (tauV (⟨2, 0, 2, 0, 2⟩ : VG 2)) gσ⁻¹ g₂ = 1 := by decide +kernel

theorem d2_eq : ∀ c : ZMod 3, (⟨0, 2, 0, 2, 0⟩ : VG c) = (g₁ * g₃)⁻¹ := by decide +kernel

theorem card_VG (c : ZMod 3) : Nat.card (VG c) = 243 := by
  rw [Nat.card_congr equivProd]
  simp [Nat.card_prod, Nat.card_zmod]

end VG

end CFSG.GH74.QTGen4.Recog.G23.P7.VL

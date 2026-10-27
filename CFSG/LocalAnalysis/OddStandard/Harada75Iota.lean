module

public import CFSG.LocalAnalysis.OddStandard.Harada75Heis
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.OddStandard.Harada75

variable {S : Type*} [Group S]

@[expose] def pw (g : S) (a : ZMod 2) : S := if a = 0 then 1 else g

structure Pres (e₁ e₂ f₁ f₂ z : S) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_cent : ∀ s : S, s * z = z * s
  e₁_sq : e₁ * e₁ = 1
  e₂_sq : e₂ * e₂ = 1
  f₁_sq : f₁ * f₁ = 1
  f₂_sq : f₂ * f₂ = 1
  e₁e₂ : e₁ * e₂ = e₂ * e₁
  f₁f₂ : f₁ * f₂ = f₂ * f₁
  e₁f₁ : e₁ * f₁ = f₁ * e₁ * z
  e₂f₂ : e₂ * f₂ = f₂ * e₂ * z
  e₁f₂ : e₁ * f₂ = f₂ * e₁
  e₂f₁ : e₂ * f₁ = f₁ * e₂

theorem pw_zero (g : S) : pw g 0 = 1 := by simp [pw]
theorem pw_one (g : S) : pw g 1 = g := by simp [pw]

theorem pw_add {g : S} (hg : g * g = 1) (a b : ZMod 2) : pw g a * pw g b = pw g (a + b) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [pw_zero]
  · simp [pw_zero, pw_one]
  · simp [pw_zero, pw_one]
  · have : (1 : ZMod 2) + 1 = 0 := by decide
    rw [this, pw_zero, pw_one, hg]

theorem pw_comm {g h : S} (hgh : g * h = h * g) (a b : ZMod 2) :
    pw g a * pw h b = pw h b * pw g a := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [pw_zero]
  · simp [pw_zero]
  · simp [pw_zero]
  · simpa [pw_one] using hgh

namespace Pres

variable {e₁ e₂ f₁ f₂ z : S} (P : Pres e₁ e₂ f₁ f₂ z)
include P

theorem f₁e₁ : f₁ * e₁ = e₁ * f₁ * z := by
  have h := P.e₁f₁
  calc f₁ * e₁ = f₁ * e₁ * (z * z) := by rw [P.z_sq, mul_one]
    _ = (f₁ * e₁ * z) * z := (mul_assoc _ _ _).symm
    _ = (e₁ * f₁) * z := by rw [← h]
    _ = e₁ * f₁ * z := rfl

theorem f₂e₂ : f₂ * e₂ = e₂ * f₂ * z := by
  have h := P.e₂f₂
  calc f₂ * e₂ = f₂ * e₂ * (z * z) := by rw [P.z_sq, mul_one]
    _ = (f₂ * e₂ * z) * z := (mul_assoc _ _ _).symm
    _ = (e₂ * f₂) * z := by rw [← h]
    _ = e₂ * f₂ * z := rfl

theorem f₂e₁ : f₂ * e₁ = e₁ * f₂ := P.e₁f₂.symm

theorem f₁e₂ : f₁ * e₂ = e₂ * f₁ := P.e₂f₁.symm

end Pres

@[expose] def Ee (e₁ e₂ : S) (a b : ZMod 2) : S := pw e₁ a * pw e₂ b

@[expose] def Ff (f₁ f₂ : S) (a b : ZMod 2) : S := pw f₁ a * pw f₂ b

namespace Pres

variable {e₁ e₂ f₁ f₂ z : S} (P : Pres e₁ e₂ f₁ f₂ z)
include P

theorem pw_z_comm (a : ZMod 2) (s : S) : s * pw z a = pw z a * s := by
  rcases zmod2_cases a with rfl | rfl
  · simp [pw_zero]
  · simpa [pw_one] using P.z_cent s

theorem r1 (x : S) : f₁ * (e₁ * x) = e₁ * (f₁ * (z * x)) := by
  rw [← mul_assoc, P.f₁e₁]; simp [mul_assoc]

theorem r3 (x : S) : f₂ * (e₁ * x) = e₁ * (f₂ * x) := by
  rw [← mul_assoc, P.f₂e₁]; simp [mul_assoc]

theorem r4 (x : S) : f₁ * (e₂ * x) = e₂ * (f₁ * x) := by
  rw [← mul_assoc, P.f₁e₂]; simp [mul_assoc]

theorem r7e₂ (x : S) : z * (e₂ * x) = e₂ * (z * x) := by
  rw [← mul_assoc, ← P.z_cent e₂]; simp [mul_assoc]
theorem r7f₂ (x : S) : z * (f₂ * x) = f₂ * (z * x) := by
  rw [← mul_assoc, ← P.z_cent f₂]; simp [mul_assoc]

theorem swap (x₁ x₂ y₁ y₂ : ZMod 2) :
    Ff f₁ f₂ y₁ y₂ * Ee e₁ e₂ x₁ x₂ =
      Ee e₁ e₂ x₁ x₂ * Ff f₁ f₂ y₁ y₂ * pw z (x₁ * y₁ + x₂ * y₂) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases x₁ with rfl | rfl <;> rcases zmod2_cases x₂ with rfl | rfl <;>
    rcases zmod2_cases y₁ with rfl | rfl <;> rcases zmod2_cases y₂ with rfl | rfl <;>
    simp [Ee, Ff, pw_zero, pw_one, mul_assoc, h11, P.r1, P.r3, P.r4, P.r7e₂, P.r7f₂, P.f₁e₁,
      P.f₂e₂, P.f₂e₁, P.f₁e₂, P.z_sq, (P.z_cent e₂).symm, (P.z_cent f₂).symm]

theorem zc (c : ZMod 2) (s : S) : pw z c * s = s * pw z c := (P.pw_z_comm c s).symm

theorem Ee_mul (a b a' b' : ZMod 2) :
    Ee e₁ e₂ a b * Ee e₁ e₂ a' b' = Ee e₁ e₂ (a + a') (b + b') := by
  unfold Ee
  calc pw e₁ a * pw e₂ b * (pw e₁ a' * pw e₂ b')
      = pw e₁ a * (pw e₂ b * pw e₁ a') * pw e₂ b' := by simp only [mul_assoc]
    _ = pw e₁ a * (pw e₁ a' * pw e₂ b) * pw e₂ b' := by
        rw [← pw_comm P.e₁e₂ a' b]
    _ = (pw e₁ a * pw e₁ a') * (pw e₂ b * pw e₂ b') := by simp only [mul_assoc]
    _ = pw e₁ (a + a') * pw e₂ (b + b') := by rw [pw_add P.e₁_sq, pw_add P.e₂_sq]

theorem Ff_mul (a b a' b' : ZMod 2) :
    Ff f₁ f₂ a b * Ff f₁ f₂ a' b' = Ff f₁ f₂ (a + a') (b + b') := by
  unfold Ff
  calc pw f₁ a * pw f₂ b * (pw f₁ a' * pw f₂ b')
      = pw f₁ a * (pw f₂ b * pw f₁ a') * pw f₂ b' := by simp only [mul_assoc]
    _ = pw f₁ a * (pw f₁ a' * pw f₂ b) * pw f₂ b' := by
        rw [← pw_comm P.f₁f₂ a' b]
    _ = (pw f₁ a * pw f₁ a') * (pw f₂ b * pw f₂ b') := by simp only [mul_assoc]
    _ = pw f₁ (a + a') * pw f₂ (b + b') := by rw [pw_add P.f₁_sq, pw_add P.f₂_sq]

theorem zpow_mul (c c' : ZMod 2) : pw z c * pw z c' = pw z (c + c') := pw_add P.z_sq c c'

end Pres

@[expose] def iotaFun (e₁ e₂ f₁ f₂ z : S) (h : Heis) : S :=
  Ee e₁ e₂ h.w.1 h.w.2.1 * Ff f₁ f₂ h.w.2.2.1 h.w.2.2.2 * pw z h.k

namespace Pres

variable {e₁ e₂ f₁ f₂ z : S} (P : Pres e₁ e₂ f₁ f₂ z)
include P

theorem iotaFun_mul (a b : Heis) :
    iotaFun e₁ e₂ f₁ f₂ z (a * b) = iotaFun e₁ e₂ f₁ f₂ z a * iotaFun e₁ e₂ f₁ f₂ z b := by
  unfold iotaFun
  have hs := P.swap b.w.1 b.w.2.1 a.w.2.2.1 a.w.2.2.2
  have hE := P.Ee_mul a.w.1 a.w.2.1 b.w.1 b.w.2.1
  have hF := P.Ff_mul a.w.2.2.1 a.w.2.2.2 b.w.2.2.1 b.w.2.2.2
  have hza := P.zc a.k
  have hzb := P.zc b.k
  have hzc := P.zc (b.w.1 * a.w.2.2.1 + b.w.2.1 * a.w.2.2.2)
  simp only [Heis.mul_w, Heis.mul_k, Prod.fst_add, Prod.snd_add, beta]
  rw [← hE, ← hF, ← P.zpow_mul, ← P.zpow_mul]
  generalize Ee e₁ e₂ a.w.1 a.w.2.1 = Ea at *
  generalize Ee e₁ e₂ b.w.1 b.w.2.1 = Eb at *
  generalize Ff f₁ f₂ a.w.2.2.1 a.w.2.2.2 = Fa at *
  generalize Ff f₁ f₂ b.w.2.2.1 b.w.2.2.2 = Fb at *
  generalize pw z a.k = za at *
  generalize pw z b.k = zb at *
  generalize pw z (b.w.1 * a.w.2.2.1 + b.w.2.1 * a.w.2.2.2) = zc' at *
  have hcc : za * zb * zc' = zc' * zb * za := by
    calc za * zb * zc' = zb * za * zc' := by rw [hza zb]
      _ = zb * (za * zc') := mul_assoc _ _ _
      _ = zb * (zc' * za) := by rw [hzc za]
      _ = zb * zc' * za := (mul_assoc _ _ _).symm
      _ = zc' * zb * za := by rw [hzc zb]
  calc Ea * Eb * (Fa * Fb) * (za * zb * zc')
      = Ea * Eb * Fa * Fb * (zc' * zb * za) := by rw [hcc]; simp only [mul_assoc]
    _ = Ea * Eb * Fa * (zc' * Fb) * zb * za := by rw [hzc Fb]; simp only [mul_assoc]
    _ = Ea * (Eb * Fa * zc') * Fb * zb * za := by simp only [mul_assoc]
    _ = Ea * (Fa * Eb) * Fb * zb * za := by rw [hs]
    _ = Ea * Fa * ((Eb * Fb * zb) * za) := by simp only [mul_assoc]
    _ = Ea * Fa * (za * (Eb * Fb * zb)) := by rw [hza (Eb * Fb * zb)]
    _ = Ea * Fa * za * (Eb * Fb * zb) := by simp only [mul_assoc]

@[expose] def iota : Heis →* S where
  toFun := iotaFun e₁ e₂ f₁ f₂ z
  map_one' := by
    simp [iotaFun, Ee, Ff, pw_zero, Heis.one_w, Heis.one_k]
  map_mul' := P.iotaFun_mul

theorem iota_apply (h : Heis) :
    P.iota h = Ee e₁ e₂ h.w.1 h.w.2.1 * Ff f₁ f₂ h.w.2.2.1 h.w.2.2.2 * pw z h.k := rfl

theorem iota_Zc (k : ZMod 2) : P.iota (Heis.Zc k) = pw z k := by
  simp [iota_apply, Heis.Zc, Ee, Ff, pw_zero]

theorem pw_eq_one {c : ZMod 2} (h : pw z c = 1) : c = 0 := by
  rcases zmod2_cases c with rfl | rfl
  · rfl
  · rw [pw_one] at h; exact absurd h P.z_ne

theorem iota_injective : Function.Injective P.iota := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have key : ∀ g : Heis, b₀ g.w h.w = 0 := by
    intro g
    have h1 := congrArg P.iota (Heis.comm_formula g h)
    rw [iota_Zc] at h1
    simp only [map_mul, map_inv, hh, mul_one, inv_one, mul_inv_cancel] at h1
    exact P.pw_eq_one h1.symm
  have hx1 := key ⟨e1, 0⟩
  have hx2 := key ⟨e2, 0⟩
  have hy1 := key ⟨f1, 0⟩
  have hy2 := key ⟨f2, 0⟩
  simp only [b₀, e1, e2, f1, f2] at hx1 hx2 hy1 hy2
  simp only [zero_mul, one_mul, add_zero, zero_add] at hx1 hx2 hy1 hy2
  have hw : h.w = 0 := by
    ext <;> simp [hy1, hy2, hx1, hx2]
  have hk : h.k = 0 := by
    have h2 : P.iota (Heis.Zc h.k) = 1 := by
      have : Heis.Zc h.k = h := by
        refine Heis.ext ?_ rfl
        simpa [Heis.Zc] using hw.symm
      rw [this, hh]
    rw [iota_Zc] at h2
    exact P.pw_eq_one h2
  refine Heis.ext hw ?_
  simpa using hk

end Pres

end CFSG.OddStandard.Harada75

module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

structure Fi22CoverData {S : Type*} [Group S] (p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n : S) : Prop where
  heis : HeisCfg 3 3 ![p₀, p₁, p₂] ![q₀, q₁, q₂] z
  hq₀ : q₀ ^ 3 = 1
  hq₁ : q₁ ^ 3 = 1
  hq₂ : q₂ ^ 3 = 1
  dBp₀ : dB * p₀ = p₀ * (p₀ * dB)
  dBp₁ : dB * p₁ = p₁ * (p₁ * dB)
  dBp₂ : dB * p₂ = p₂ * dB
  dBq₀ : dB * q₀ = q₀ * (q₀ * dB)
  dBq₁ : dB * q₁ = q₁ * (q₁ * (z * dB))
  dBq₂ : dB * q₂ = q₂ * dB
  dBz : dB * z = z * dB
  dAp₀ : dA * p₀ = p₀ * (p₀ * dA)
  dAp₁ : dA * p₁ = p₁ * dA
  dAp₂ : dA * p₂ = p₂ * (p₂ * dA)
  dAq₀ : dA * q₀ = q₀ * (q₀ * (z * (z * dA)))
  dAq₁ : dA * q₁ = q₁ * dA
  dAq₂ : dA * q₂ = q₂ * (q₂ * (z * (z * dA)))
  dAz : dA * z = z * dA
  np₀ : n * p₀ = p₁ * (p₁ * n)
  nq₀ : n * q₀ = p₁ * (q₁ * (q₁ * (z * (z * n))))
  np₁ : n * p₁ = q₂ * n
  nq₁ : n * q₁ = p₂ * (p₂ * n)
  nz : n * z = z * n

theorem Fi22CoverData.map {S S' : Type*} [Group S] [Group S'] (e : S →* S')
    {p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n : S} (h : Fi22CoverData p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n)
    (hz : e z ≠ 1) :
    Fi22CoverData (e p₀) (e p₁) (e p₂) (e q₀) (e q₁) (e q₂) (e z) (e dA) (e dB) (e n) := by
  have hm := h.heis.map e hz
  have hq : ∀ {q : S}, q ^ 3 = 1 → e q ^ 3 = 1 := fun {q} hq => by
    rw [← map_pow, hq, map_one]
  refine ⟨?_, hq h.hq₀, hq h.hq₁, hq h.hq₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hx : (fun i => e (![p₀, p₁, p₂] i)) = ![e p₀, e p₁, e p₂] := by
      funext i; fin_cases i <;> rfl
    have hy : (fun i => e (![q₀, q₁, q₂] i)) = ![e q₀, e q₁, e q₂] := by
      funext i; fin_cases i <;> rfl
    rw [hx, hy] at hm
    exact hm
  · simpa only [map_mul] using congrArg e h.dBp₀
  · simpa only [map_mul] using congrArg e h.dBp₁
  · simpa only [map_mul] using congrArg e h.dBp₂
  · simpa only [map_mul] using congrArg e h.dBq₀
  · simpa only [map_mul] using congrArg e h.dBq₁
  · simpa only [map_mul] using congrArg e h.dBq₂
  · simpa only [map_mul] using congrArg e h.dBz
  · simpa only [map_mul] using congrArg e h.dAp₀
  · simpa only [map_mul] using congrArg e h.dAp₁
  · simpa only [map_mul] using congrArg e h.dAp₂
  · simpa only [map_mul] using congrArg e h.dAq₀
  · simpa only [map_mul] using congrArg e h.dAq₁
  · simpa only [map_mul] using congrArg e h.dAq₂
  · simpa only [map_mul] using congrArg e h.dAz
  · simpa only [map_mul] using congrArg e h.np₀
  · simpa only [map_mul] using congrArg e h.nq₀
  · simpa only [map_mul] using congrArg e h.np₁
  · simpa only [map_mul] using congrArg e h.nq₁
  · simpa only [map_mul] using congrArg e h.nz

theorem pow_three_of_word {G : Type*} [Monoid G] {g : G} (h : g * (g * g) = 1) :
    g ^ 3 = 1 := by
  rw [← h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem heisCfg_three_three {G : Type*} [Group G] {x₁ x₂ x₃ y₁ y₂ y₃ z : G}
    (hx₁ : x₁ ^ 3 = 1) (hx₂ : x₂ ^ 3 = 1) (hx₃ : x₃ ^ 3 = 1) (hz : z ^ 3 = 1)
    (hzx₁ : x₁ * z = z * x₁) (hzx₂ : x₂ * z = z * x₂) (hzx₃ : x₃ * z = z * x₃)
    (hzy₁ : y₁ * z = z * y₁) (hzy₂ : y₂ * z = z * y₂) (hzy₃ : y₃ * z = z * y₃)
    (hyx₁ : x₁ * y₁ = y₁ * (x₁ * z)) (hyx₂ : x₂ * y₂ = y₂ * (x₂ * z))
    (hyx₃ : x₃ * y₃ = y₃ * (x₃ * z))
    (hx₁₂ : x₁ * x₂ = x₂ * x₁) (hx₁₃ : x₁ * x₃ = x₃ * x₁) (hx₂₃ : x₂ * x₃ = x₃ * x₂)
    (hy₁₂ : y₁ * y₂ = y₂ * y₁) (hy₁₃ : y₁ * y₃ = y₃ * y₁) (hy₂₃ : y₂ * y₃ = y₃ * y₂)
    (hxy₁₂ : x₁ * y₂ = y₂ * x₁) (hxy₁₃ : x₁ * y₃ = y₃ * x₁) (hxy₂₁ : x₂ * y₁ = y₁ * x₂)
    (hxy₂₃ : x₂ * y₃ = y₃ * x₂) (hxy₃₁ : x₃ * y₁ = y₁ * x₃) (hxy₃₂ : x₃ * y₂ = y₂ * x₃)
    (hz1 : z ≠ 1) :
    HeisCfg 3 3 ![x₁, x₂, x₃] ![y₁, y₂, y₃] z where
  xp i := by fin_cases i <;> assumption
  zp := hz
  zx i := by fin_cases i <;> assumption
  zy i := by fin_cases i <;> assumption
  yx i := by
    have key : ∀ x y : G, x * y = y * (x * z) → y⁻¹ * x * y = x * z := fun x y h => by
      rw [mul_assoc, h]
      group
    fin_cases i
    · exact key _ _ hyx₁
    · exact key _ _ hyx₂
    · exact key _ _ hyx₃
  xx i j := by
    fin_cases i <;> fin_cases j <;> simp <;> first | assumption | exact (by assumption : _ = _).symm
  yy i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first | assumption | exact (by assumption : _ = _).symm
  xy i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> assumption
  z1 := hz1

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

module

public import Mathlib.Algebra.Group.Hom.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoHS

structure FyRel {Λ : Type*} [Group Λ] (σ : Λ →* Λ) (z R A l : Λ) (c : ℕ → Λ) : Prop where
  z_central : ∀ x : Λ, z * x = x * z
  z_sq : z * z = 1
  r3 : R ^ 3 = 1
  r_ne : R ≠ 1
  c_sq : ∀ i < 4, c i * c i = z
  c_r : ∀ i < 4, c i * R = R * c i
  c_a : ∀ i < 4, c i * A = z * A * σ (c i)
  braid : ∀ i < 3, c i * c (i + 1) * c i = c (i + 1) * c i * c (i + 1)
  comm02 : c 0 * c 2 = c 2 * c 0
  comm03 : c 0 * c 3 = c 3 * c 0
  comm13 : c 1 * c 3 = c 3 * c 1
  a_sig : A * σ A = 1
  a_r : A * σ R = R * A
  c01 : c 0 ≠ c 1
  c20 : c 2 ≠ c 0
  c20z : c 2 ≠ c 0 * z
  fusion : l * A = A * σ (c 0) * z * σ l

end CFSG.EvenSporadicStandard.TwoHS

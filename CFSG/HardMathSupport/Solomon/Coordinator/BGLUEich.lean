module

public import CFSG.ClassicalGroups.Unitary.Elements

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem eichler_mul_eichler_add (hσ : ∀ c, σ (σ c) = c) {e y y' : Fin n → K}
    (he : herm σ e e = 0) (hey : herm σ e y = 0) (hey' : herm σ e y' = 0)
    (hey'' : herm σ e (y + y') = 0) {c c' c'' : K} (hc : c + σ c = -herm σ y y)
    (hc' : c' + σ c' = -herm σ y' y') (hc'' : c'' + σ c'' = -herm σ (y + y') (y + y'))
    (hcc : c'' = c + c' - herm σ y y') :
    eichler hσ he hey hc * eichler hσ he hey' hc' = eichler hσ he hey'' hc'' := by
  have hye : herm σ y e = 0 := herm_eq_zero_comm σ hσ hey
  have hy'e : herm σ y' e = 0 := herm_eq_zero_comm σ hσ hey'
  apply ext_smul
  intro x
  rw [mul_smul, eichler_smul, eichler_smul, eichler_smul]
  simp only [herm_add_right, herm_sub_right, herm_smul_right, herm_add_left, he, hey', hye,
    mul_zero, add_zero, sub_zero, hcc]
  match_scalars <;> ring

theorem mul_eichler_mul_inv (hσ : ∀ c, σ (σ c) = c) (g : SUid σ n) {e y : Fin n → K}
    (he : herm σ e e = 0) (hey : herm σ e y = 0) {c : K} (hc : c + σ c = -herm σ y y)
    (he' : herm σ (g • e) (g • e) = 0) (hey' : herm σ (g • e) (g • y) = 0)
    (hc' : c + σ c = -herm σ (g • y) (g • y)) :
    g * eichler hσ he hey hc * g⁻¹ = eichler hσ he' hey' hc' := by
  apply ext_smul
  intro x
  have hx : herm σ (g • e) x = herm σ e (g⁻¹ • x) := by
    conv_lhs => rw [← smul_inv_smul g x]
    exact herm_smul_smul σ g e (g⁻¹ • x)
  have hy : herm σ (g • y) x = herm σ y (g⁻¹ • x) := by
    conv_lhs => rw [← smul_inv_smul g x]
    exact herm_smul_smul σ g y (g⁻¹ • x)
  rw [mul_smul, mul_smul, eichler_smul, eichler_smul, hx, hy]
  simp only [smul_add, smul_sub, smul_inv_smul, smul_comm g]

theorem eichler_smul_left (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} {c : K} (t : K)
    (he : herm σ (t • e) (t • e) = 0) (hey : herm σ (t • e) y = 0)
    (hc : c + σ c = -herm σ y y) (he0 : herm σ e e = 0) (hey0 : herm σ e (σ t • y) = 0)
    (hc0 : σ t * t * c + σ (σ t * t * c) = -herm σ (σ t • y) (σ t • y)) :
    eichler hσ he hey hc = eichler hσ he0 hey0 hc0 := by
  apply ext_smul
  intro x
  rw [eichler_smul, eichler_smul]
  simp only [herm_smul_left, hσ]
  match_scalars <;> ring

theorem eichler_self_eq_tv (hσ : ∀ c, σ (σ c) = c) {e : Fin n → K} (he : herm σ e e = 0)
    (ν : K) (hey : herm σ e (ν • e) = 0) {c : K} (hc : c + σ c = -herm σ (ν • e) (ν • e))
    (hc0 : (c + ν - σ ν) + σ (c + ν - σ ν) = 0) :
    eichler hσ he hey hc = tv hσ he hc0 := by
  apply ext_smul
  intro x
  rw [eichler_smul, tv_smul]
  simp only [herm_smul_left]
  match_scalars <;> ring

end CFSG.HardMathSupport.Solomon.Coordinator.BGL

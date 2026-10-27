module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthExt

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_e_of_mem_hypPerp (P : HypPair Q) {w : V} (hw : w ∈ hypPerp P) :
    polar Q P.e w = 0 := by
  rw [polar_comm]
  exact hw.1

@[expose] noncomputable def eichlerRadical (P : HypPair Q) :
    Multiplicative (hypPerp P) →* elementaryGroup Q where
  toFun w := ⟨eichler Q P.e (Multiplicative.toAdd w : hypPerp P),
    eichler_mem_elementaryGroup Q _ _⟩
  map_one' := by
    apply Subtype.ext
    simp [eichler_zero_right]
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, toAdd_mul, Submodule.coe_add]
    exact (eichler_mul (polar_e_of_mem_hypPerp P (Multiplicative.toAdd a).2)
      (polar_e_of_mem_hypPerp P (Multiplicative.toAdd b).2)).symm

theorem eq_zero_of_eichler_eq_smul (P : HypPair Q) {w : V} (hw : w ∈ hypPerp P) {c : K}
    (hc : ∀ v, eichler Q P.e w v = c • v) : w = 0 := by
  have hwe := polar_e_of_mem_hypPerp P hw
  have h1 : c = 1 := by
    have := hc P.e
    rw [eichler_apply_self] at this
    have h' : (1 - c) • P.e = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
    rcases smul_eq_zero.1 h' with h | h
    · exact (sub_eq_zero.1 h).symm
    · exact absurd h P.e_ne_zero
  subst h1
  have h2 := hc P.f
  have hfw : polar Q P.f w = 0 := by rw [polar_comm]; exact hw.2
  rw [eichler_apply P.Q_e hwe, one_smul, P.polar_fe, one_smul, hfw, mul_one, zero_add] at h2
  have h3 : w = Q w • P.e := by
    linear_combination (norm := module) h2
  have h4 : Q w = 0 := by
    have := hw.2
    rw [h3, polar_smul_left_eq, P.polar_ef, mul_one] at this
    exact this
  rw [h3, h4, zero_smul]

theorem extHom_mul_eichler_mul_inv (P : HypPair Q) {g : hypPerp P ≃ₗ[K] hypPerp P}
    (hg : g ∈ elementaryGroup (perpForm P)) (w : hypPerp P) :
    extHom P g * eichler Q P.e w * (extHom P g)⁻¹ = eichler Q P.e (g w) := by
  have hO := elementaryGroup_le_orthogonalGroup Q (extHom_mem_elementaryGroup P hg)
  rw [eichler_conj hO, extHom_apply_e, extHom_apply_mem P g w.2]

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

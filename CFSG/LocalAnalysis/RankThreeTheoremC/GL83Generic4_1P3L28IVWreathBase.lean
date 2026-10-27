module

public import CFSG.RankThree.PartTwo.Sec11.Wreath

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.RankThree.PartTwo.Sec11

private theorem l28iv_z3_orbit : ∀ q x y : Multiplicative (ZMod 3), q ≠ 1 →
    y = x ∨ y = q * x ∨ y = q * (q * x) := by
  decide

private theorem l28iv_z3_cube : ∀ a : Multiplicative (ZMod 3), a * a * a = 1 := by
  decide

theorem l28iv_w33_left_const {b h : W33} (hb : b.right = 1) (hh : h.right ≠ 1)
    (hbh : b * h = h * b) : ∀ x, b.left x = b.left 1 := by
  have hinv : ∀ x, b.left x = b.left (h.right⁻¹ * x) := by
    intro x
    have h1 := congrArg (fun w : W33 => w.left x) hbh
    simp [RegularWreathProduct.mul_def, hb] at h1
    rw [mul_comm (h.left x)] at h1
    exact mul_right_cancel h1
  have hq : h.right⁻¹ ≠ 1 := inv_ne_one.mpr hh
  intro x
  rcases l28iv_z3_orbit (h.right⁻¹) 1 x hq with h1 | h1 | h1
  · rw [h1]
  · rw [h1, ← hinv]
  · rw [h1, ← hinv, ← hinv]

theorem l28iv_w33_pow_three_of_abelian {H : Subgroup W33}
    (hab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hcard : 27 ≤ Nat.card H) :
    ∀ h ∈ H, h ^ 3 = 1 := by
  by_cases hbase : ∀ h ∈ H, h.right = 1
  · intro h hh
    have hr := hbase h hh
    have h3 : h ^ 3 = h * h * h := by rw [pow_succ, pow_succ, pow_one]
    rw [h3]
    apply RegularWreathProduct.ext
    · funext x
      simp [RegularWreathProduct.mul_def, hr]
      exact l28iv_z3_cube (h.left x)
    · simp [RegularWreathProduct.mul_def, hr]
  · push Not at hbase
    obtain ⟨h₀, hh₀, hr₀⟩ := hbase
    exfalso
    set ρ : W33 →* Multiplicative (ZMod 3) := RegularWreathProduct.rightHom with hρ
    have hρapp : ∀ w : W33, ρ w = w.right := fun w => rfl
    have hZ3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by simp
    have h1 : Nat.card (H.map ρ) ≤ 3 := (Subgroup.card_le_card_group _).trans hZ3.le
    have h2 : Nat.card ↥(ρ.ker ⊓ H) ≤ 3 := by
      let F : ↥(ρ.ker ⊓ H) → Multiplicative (ZMod 3) := fun b => (b : W33).left 1
      have hF : Function.Injective F := by
        rintro ⟨b, hbk, hbH⟩ ⟨b', hbk', hbH'⟩ hbb
        have hb1 : b.right = 1 := by rw [← hρapp]; exact hbk
        have hb1' : b'.right = 1 := by rw [← hρapp]; exact hbk'
        have hc := l28iv_w33_left_const hb1 hr₀ (hab b hbH h₀ hh₀)
        have hc' := l28iv_w33_left_const hb1' hr₀ (hab b' hbH' h₀ hh₀)
        apply Subtype.ext
        apply RegularWreathProduct.ext
        · funext x
          rw [hc, hc']
          exact hbb
        · rw [hb1, hb1']
      exact (Nat.card_le_card_of_injective F hF).trans hZ3.le
    have h3 : Nat.card H = Nat.card (H.map ρ) * Nat.card ↥(ρ.ker ⊓ H) := by
      have e1 := Subgroup.relIndex_mul_card ρ.ker H
      rw [Subgroup.relIndex_ker] at e1
      exact e1.symm
    have h4 : Nat.card H ≤ 9 := by
      rw [h3]
      calc Nat.card (H.map ρ) * Nat.card ↥(ρ.ker ⊓ H) ≤ 3 * 3 := Nat.mul_le_mul h1 h2
        _ = 9 := by norm_num
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC

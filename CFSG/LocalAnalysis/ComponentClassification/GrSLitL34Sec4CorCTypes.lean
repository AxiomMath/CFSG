module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

theorem ordA_one_ne_held {m : ℕ} (hm : Odd m) : Open.ordA 1 m ≠ 4030387200 := by
  unfold Open.ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  obtain ⟨k, rfl⟩ := hm
  have hg : Nat.gcd (1 + 1) (2 * k + 1 - 1) = 2 := by
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    simp
  rw [hg]
  intro h
  have hmod := Nat.div_add_mod ((2 * k + 1) * ((2 * k + 1) ^ 2 - 1)) 2
  have hlt := Nat.mod_lt ((2 * k + 1) * ((2 * k + 1) ^ 2 - 1)) (show 2 > 0 by norm_num)
  rw [h] at hmod
  rcases Nat.lt_or_ge (2 * k + 1) 2006 with hk | hk
  · have h1 : (2 * k + 1) * ((2 * k + 1) ^ 2 - 1) ≤ 2005 * (2005 ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
    norm_num at h1
    omega
  · have h1 : 2006 * (2006 ^ 2 - 1) ≤ (2 * k + 1) * ((2 * k + 1) ^ 2 - 1) :=
      Nat.mul_le_mul hk (Nat.sub_le_sub_right (Nat.pow_le_pow_left hk 2) 1)
    norm_num at h1
    omega

omit [Finite X] in
theorem fusionZStar_ne_top {K : Type*} [Group K]
    (h : Nat.card (K ⧸ Open.fusionZStar K) ≠ 1) : Open.fusionZStar K ≠ ⊤ := by
  intro htop
  apply h
  rw [htop]
  exact Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, inferInstance⟩

end CFSG.ComponentClassification.GSThmB.CorC

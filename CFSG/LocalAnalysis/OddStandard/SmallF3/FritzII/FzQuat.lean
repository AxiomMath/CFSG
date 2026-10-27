module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalQuaternion

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G] {a b : G}

theorem fz_q8_range (h : IsQ8Pair a b) : (q8Hom h).range = closure {a, b} := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    have ha : a ∈ closure ({a, b} : Set G) := subset_closure (by simp)
    have hb : b ∈ closure ({a, b} : Set G) := subset_closure (by simp)
    rcases q with k | k
    · exact pow_mem ha _
    · exact mul_mem hb (pow_mem ha _)
  · rw [closure_le]
    rintro g (rfl | rfl)
    · refine ⟨QuaternionGroup.a 1, ?_⟩
      have h1 : (1 : ZMod 4).val = 1 := rfl
      change zmod4Pow g 1 = g
      rw [zmod4Pow, h1, pow_one]
    · refine ⟨QuaternionGroup.xa 0, ?_⟩
      have h0 : (0 : ZMod 4).val = 0 := rfl
      change g * zmod4Pow a 0 = g
      rw [zmod4Pow, h0, pow_zero, mul_one]

theorem fz_q8_nonempty_equiv (h : IsQ8Pair a b) :
    Nonempty (closure {a, b} ≃* QuaternionGroup 2) :=
  ⟨(MulEquiv.subgroupCongr (fz_q8_range h).symm).trans
    (MonoidHom.ofInjective (q8Hom_injective h)).symm⟩

theorem fz_q8_mem_zpowers_sq_of_central (h : IsQ8Pair a b) {g : G} (hg : g ∈ closure {a, b})
    (hc : ∀ r ∈ closure {a, b}, g * r = r * g) : g ∈ zpowers (a ^ 2) := by
  rw [← fz_q8_range h] at hg hc
  obtain ⟨q, rfl⟩ := hg
  have hq : ∀ p : QuaternionGroup 2, q * p = p * q := fun p =>
    q8Hom_injective h (by simpa using hc (q8Hom h p) ⟨p, rfl⟩)
  have key : ∀ q : QuaternionGroup 2, (∀ p : QuaternionGroup 2, q * p = p * q) →
      q = QuaternionGroup.a 0 ∨ q = QuaternionGroup.a 2 := by decide
  rcases key q hq with rfl | rfl
  · rw [show (QuaternionGroup.a (0 : ZMod 4) : QuaternionGroup 2) = 1 from rfl, map_one]
    exact one_mem _
  · have h2 : (2 : ZMod 4).val = 2 := rfl
    have : q8Hom h (QuaternionGroup.a 2) = a ^ 2 := by
      change zmod4Pow a 2 = a ^ 2
      rw [zmod4Pow, h2]
    rw [this]
    exact mem_zpowers _

end CFSG.OddStandard.SmallF3.FritzII

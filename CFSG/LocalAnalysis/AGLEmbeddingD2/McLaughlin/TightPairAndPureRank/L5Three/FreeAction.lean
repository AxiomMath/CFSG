module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

variable {G : Type*} [Group G] [Finite G]

theorem prime_dvd_ncard_of_free {p : ℕ} [Fact p.Prime] {x : G} (hx : x ^ p = 1) (T : Set G)
    (hT : ∀ t ∈ T, x * t * x⁻¹ ∈ T) (hfree : ∀ t ∈ T, x * t * x⁻¹ ≠ t) :
    p ∣ T.ncard := by
  classical
  let f : Function.End T := fun t => ⟨x * t * x⁻¹, hT t t.2⟩
  have hf : f ^ p ^ 1 = 1 := by
    have hit : ∀ n : ℕ, ∀ t : T, ((f ^ n) t : G) = x ^ n * t * (x ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro t; show ((id t : T) : G) = _; simp
      | succ n ih =>
        intro t
        have : (f ^ (n + 1)) t = (f ^ n) (f t) := by rw [pow_succ]; rfl
        rw [this, ih]
        simp [f, pow_succ, mul_assoc]
    funext t
    apply Subtype.ext
    rw [pow_one, hit]
    simp [hx]
    rfl
  have hfp : Function.fixedPoints f = ∅ := by
    ext t
    simp only [Function.IsFixedPt, Set.mem_empty_iff_false, iff_false]
    intro ht
    exact hfree t t.2 (congrArg Subtype.val ht)
  have : Fintype T := Fintype.ofFinite T
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  have hc : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨a, ha⟩ => by rw [hfp] at ha; exact ha⟩
  rw [hc] at h
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact (Nat.modEq_zero_iff_dvd.mp h)

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three

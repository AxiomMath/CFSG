module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Tr

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace A3

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
  {B K L1 : Subgroup G}

theorem ab_comm (h : Sec8T84L1 G t L S z g B K L1) (hsq : ∀ l ∈ L1, l * l = tauFn t l) {x y : G}
    (hx : x ∈ L1) (hy : y ∈ L1) : x * y = y * x := by
  have h1 : (x * y) * (x * y) = (x * x) * (y * y) := by
    rw [hsq _ (L1.mul_mem hx hy), tau_mul_L1 h hx hy, hsq x hx, hsq y hy]
  have h2 := (cl2_of h.K_data).sq_mul (h.le hx) (h.le hy)
  have h3 : (x * x) * (y * y) * (y * x * y⁻¹ * x⁻¹) = (x * x) * (y * y) * 1 := by
    rw [← h2, mul_one, h1]
  have h4 : y * x * y⁻¹ * x⁻¹ = 1 := mul_left_cancel h3
  calc x * y = (y * x * y⁻¹ * x⁻¹) * (x * y) := by rw [h4, one_mul]
    _ = y * x := by group

theorem ab_pow4 (h : Sec8T84L1 G t L S z g B K L1) (hsq : ∀ l ∈ L1, l * l = tauFn t l) {x : G}
    (hx : x ∈ L1) : x ^ 4 = 1 := by
  have hb : tauFn t x ∈ B := (cl2_of h.K_data).tau_mem (t_mem_K h.K_data) (h.le hx)
  have h2 : tauFn t x * tauFn t x = 1 := (cl2_of h.K_data).B_sq _ hb
  calc x ^ 4 = (x * x) * (x * x) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    _ = tauFn t x * tauFn t x := by rw [hsq x hx]
    _ = 1 := h2

theorem ab_sq_eq_one_iff (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1)
    (hsq : ∀ l ∈ L1, l * l = tauFn t l) {x : G} (hx : x ∈ L1) : x * x = 1 ↔ x ∈ B := by
  rw [hsq x hx]
  exact tau_eq_one_iff hctx h hx

theorem ab_squares (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1)
    (hsq : ∀ l ∈ L1, l * l = tauFn t l) : {u : G | ∃ x ∈ L1, u = x * x} = (B : Set G) := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hsq x hx]
    exact (cl2_of h.K_data).tau_mem (t_mem_K h.K_data) (h.le hx)
  · intro hu
    obtain ⟨l, hl, hlu⟩ := tau_exists hctx h hu
    exact ⟨l, hl, by rw [hsq l hl, hlu]⟩

theorem ab_sq_card (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1)
    (hsq : ∀ l ∈ L1, l * l = tauFn t l) :
    Nat.card ↥(Subgroup.closure {u : G | ∃ x ∈ L1, u = x * x}) = 16 := by
  rw [ab_squares hctx h hsq, Subgroup.closure_eq, hctx.B_e16.2]
  norm_num

end A3

end CFSG.OddStandard.SmallF3.Omega

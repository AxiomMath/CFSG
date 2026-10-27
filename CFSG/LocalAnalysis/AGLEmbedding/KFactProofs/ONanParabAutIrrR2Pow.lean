module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrDefs

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

variable {Y : Type*} [Group Y]

theorem mul_pow_mul_inv_pow_mem {S : Subgroup Y} {x s : Y}
    (hx : x ∈ Subgroup.normalizer (S : Set Y)) (hs : s ∈ S) (m : ℕ) :
    (s * x) ^ m * (x ^ m)⁻¹ ∈ S := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hxm : x ^ m ∈ Subgroup.normalizer (S : Set Y) := Subgroup.pow_mem _ hx m
    have hconj : x ^ m * s * (x ^ m)⁻¹ ∈ S := ((Subgroup.mem_normalizer_iff.1 hxm) s).1 hs
    have e : (s * x) ^ (m + 1) * (x ^ (m + 1))⁻¹ =
        ((s * x) ^ m * (x ^ m)⁻¹) * (x ^ m * s * (x ^ m)⁻¹) := by
      simp only [pow_succ, mul_inv_rev]
      group
    rw [e]
    exact S.mul_mem ih hconj

theorem aut_pow_power_map {S : Subgroup Y} {τ : MulAut Y} (hS : ∀ w, w ∈ S ↔ τ w ∈ S) {k : ℕ}
    (hk : ∀ b ∈ Subgroup.normalizer (S : Set Y), τ b * (b ^ k)⁻¹ ∈ S) (j : ℕ) :
    (∀ w, w ∈ S ↔ (τ ^ j) w ∈ S) ∧
      ∀ b ∈ Subgroup.normalizer (S : Set Y), (τ ^ j) b * (b ^ (k ^ j))⁻¹ ∈ S := by
  induction j with
  | zero => exact ⟨fun w => Iff.rfl, fun b _ => by simp⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun w => ?_, fun b hb => ?_⟩
    · rw [pow_succ', MulAut.mul_apply]
      exact (h1 w).trans (hS _)
    · have ht : (τ ^ j) b * (b ^ (k ^ j))⁻¹ ∈ S := h2 b hb
      have hs : τ b * (b ^ k)⁻¹ ∈ S := hk b hb
      have hbk : b ^ k ∈ Subgroup.normalizer (S : Set Y) := Subgroup.pow_mem _ hb k
      have hτ : ∀ w, w ∈ S → τ w ∈ S := fun w hw => (hS w).1 hw
      set t := (τ ^ j) b * (b ^ (k ^ j))⁻¹ with ht_def
      have hb' : (τ ^ j) b = t * b ^ (k ^ j) := by rw [ht_def]; group
      have e1 : (τ ^ (j + 1)) b = τ t * (τ b) ^ (k ^ j) := by
        rw [pow_succ', MulAut.mul_apply, hb', map_mul, map_pow]
      have e2 : τ b = (τ b * (b ^ k)⁻¹) * b ^ k := by group
      have h3 := mul_pow_mul_inv_pow_mem hbk hs (k ^ j)
      rw [← e2] at h3
      have e3 : (τ ^ (j + 1)) b * (b ^ (k ^ (j + 1)))⁻¹ =
          τ t * ((τ b) ^ (k ^ j) * ((b ^ k) ^ (k ^ j))⁻¹) := by
        rw [e1, ← pow_mul, ← pow_succ' k j, mul_assoc]
      rw [e3]
      exact S.mul_mem (hτ _ ht) h3

end CFSG.AGLEmbedding.ParabAutIrr

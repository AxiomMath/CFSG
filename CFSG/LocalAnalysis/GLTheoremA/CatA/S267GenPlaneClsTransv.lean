module

public import Mathlib.LinearAlgebra.Center

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open Module

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W]

theorem exists_dual_eq_zero_eq_one [FiniteDimensional E W] (hW : 2 ≤ finrank E W) (w : W) :
    ∃ (f : Dual E W) (v : W), f w = 0 ∧ f v = 1 := by
  have hlt : Submodule.span E {w} < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have h1 : finrank E (Submodule.span E ({w} : Set W)) ≤ 1 := by
      simpa using finrank_span_le_card ({w} : Set W)
    rw [htop, finrank_top] at h1
    omega
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hfw : f w = 0 := by
    have : f w ∈ (Submodule.span E ({w} : Set W)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span rfl)
    rwa [hf, Submodule.mem_bot] at this
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf0 (LinearMap.ext hcon)
  refine ⟨f, (f v)⁻¹ • v, hfw, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]

theorem exists_smul_eq_of_commute_transvection [FiniteDimensional E W]
    (hW : 2 ≤ finrank E W) (s : W →+ W)
    (hs : ∀ (f : Dual E W) (u : W), f u = 0 → ∀ w, s (w + f w • u) = s w + f (s w) • u) :
    ∃ c : E, ∀ w, s w = c • w := by
  have hkey : ∀ w : W, ∃ a : E, ∀ c : E, s (c • w) = a • (c • w) := by
    intro w
    obtain ⟨f, v, hfw, hfv⟩ := exists_dual_eq_zero_eq_one hW w
    refine ⟨f (s v), fun c => ?_⟩
    have hu : f (c • w) = 0 := by rw [map_smul, hfw, smul_zero]
    have h1 := hs f (c • w) hu v
    rw [hfv, one_smul, map_add] at h1
    exact add_left_cancel h1
  have hsmul : ∀ (c : E) (w : W), s (c • w) = c • s w := by
    intro c w
    obtain ⟨a, ha⟩ := hkey w
    rw [ha c, show s w = s ((1 : E) • w) by rw [one_smul], ha 1, one_smul, smul_comm]
  let sl : W →ₗ[E] W :=
    { toFun := s
      map_add' := s.map_add
      map_smul' := hsmul }
  have hdep : ∀ w, ¬ LinearIndependent E ![w, sl w] := by
    intro w hli
    obtain ⟨a, ha⟩ := hkey w
    have hsw : sl w = a • w := by
      change s w = a • w
      simpa using ha 1
    have h0 := LinearIndependent.pair_iff.1 hli a (-1) (by rw [hsw, neg_one_smul, add_neg_cancel])
    exact one_ne_zero (neg_eq_zero.1 h0.2)
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
  refine ⟨c, fun w => ?_⟩
  have := LinearMap.congr_fun hc w
  simpa [sl] using this

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen

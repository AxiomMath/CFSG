module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614KTwo

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner congr_conj)

@[expose] def OutTwoCyclic (K : Type) [Group K] : Prop :=
  ∃ (C : Type) (_ : Group C) (_ : IsCyclic C) (Θ : MulAut K →* C),
    ∀ α ∈ Θ.ker, (∃ k : ℕ, α ^ 2 ^ k = 1) → α ∈ (MulAut.conj : K →* MulAut K).range

variable {K L : Type} [Group K] [Group L]

theorem OutTwoCyclic.isCyclic (h : OutTwoCyclic K) {R : Subgroup (MulAut K)}
    (hR : IsPGroup 2 R) (hRI : R ⊓ (MulAut.conj : K →* MulAut K).range = ⊥) : IsCyclic R := by
  obtain ⟨C, _, _, Θ, hΘ⟩ := h
  refine isCyclic_of_injective (Θ.comp R.subtype) ((injective_iff_map_eq_one _).2 fun r hr => ?_)
  obtain ⟨k, hk⟩ := hR r
  have hinn : (r : MulAut K) ∈ (MulAut.conj : K →* MulAut K).range :=
    hΘ r (MonoidHom.mem_ker.2 hr) ⟨k, by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩
  have hmem : (r : MulAut K) ∈ R ⊓ (MulAut.conj : K →* MulAut K).range := ⟨r.2, hinn⟩
  rw [hRI, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem OutTwoCyclic.of_mulEquiv (e : K ≃* L) (h : OutTwoCyclic L) : OutTwoCyclic K := by
  obtain ⟨C, _, hC, Θ, hΘ⟩ := h
  refine ⟨C, inferInstance, hC, Θ.comp (MulAut.congr e).toMonoidHom, fun α hα ⟨k, hk⟩ => ?_⟩
  obtain ⟨l, hl⟩ := hΘ (MulAut.congr e α) (MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hα))
    ⟨k, by rw [← map_pow, hk, map_one]⟩
  refine ⟨e.symm l, (MulAut.congr e).injective ?_⟩
  rw [congr_conj, MulEquiv.apply_symm_apply, hl]

theorem outTwoCyclic_of_isCyclic_outer (h : IsCyclic (Outer K)) : OutTwoCyclic K :=
  ⟨Outer K, inferInstance, h, QuotientGroup.mk' (inner K), fun α hα _ => by
    rw [QuotientGroup.ker_mk'] at hα
    exact hα⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614KTwo

module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolutionRankTwo
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapQuasi

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem map_center_eq_of_mulEquiv (e : A ≃* B) : (center A).map e.toMonoidHom = center B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_center_iff]
    intro b'
    obtain ⟨a', rfl⟩ := e.surjective b'
    change e a' * e a = e a * e a'
    rw [← map_mul, ← map_mul, mem_center_iff.1 ha a']
  · intro hb
    refine ⟨e.symm b, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro a'
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, mem_center_iff.1 hb (e a')]

@[expose] def quotientCenterCongr (e : A ≃* B) : A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr (center A) (center B) e (map_center_eq_of_mulEquiv e)

end Transport

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem map_conj_eq_of_conj_mem_normalizer (hS : Setting h L η t Q T) {G₁ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple G₁) (ψ : G₁ ⧸ center G₁ ≃* gramSU h (miyamotoJ4 K))
    (hZ : Odd (Nat.card (center G₁)))
    (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G)) (g : G)
    (hg : g⁻¹ * t * g ∈
      normalizer ((G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    G₁.map (MulAut.conj (g⁻¹ * t * g)).toMonoidHom = G₁.map (MulAut.conj t).toMonoidHom := by
  set G₂ := G₁.map (MulAut.conj t).toMonoidHom with hG₂
  obtain ⟨hperf, hbot, hn₁⟩ := SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hq
  have hn₂ := SeitzReduction.F4Pilot.dichotomy_map_mulAut (MulAut.conj t) hn₁
  rcases SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect h₁₂ hperf hbot hn₁ hn₂ hg with
    h1 | h2
  · exfalso
    have hy₁ : g⁻¹ * t * g ∈ normalizer (G₁ : Set G) := mem_normalizer_iff_map_conj_eq.2 h1
    have hG₂perf : ⁅G₂, G₂⁆ = G₂ := by rw [hG₂, ← map_commutator, hperf]
    have hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a := fun a ha b hb =>
      mem_centralizer_iff.1 (h₁₂ hb) a ha
    have hy₂ := mem_normalizer_of_mem_normalizer_sup hcomm hG₂perf hg hy₁
    let e : G₁ ≃* G₂ := Subgroup.equivMapOfInjective G₁ _ (MulAut.conj t).injective
    have hZ₂ : Odd (Nat.card (center G₂)) := by
      rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact hZ
    exact hS.false_of_conj_mem_normalizer_two_covers hcomm ψ ((quotientCenterCongr e).symm.trans ψ)
      hZ hZ₂ g⁻¹ (by rwa [inv_inv]) (by rwa [inv_inv])
  · exact h2

end Setting

end CFSG.LocalAnalysis.EvenBN.U4

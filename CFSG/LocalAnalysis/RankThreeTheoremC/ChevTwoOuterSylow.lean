module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter

@[expose] def IsPByAbelian (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ IsPGroup p N ∧ ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N

namespace IsPByAbelian

variable {p : ℕ} {G H : Type*} [Group G] [Group H]

theorem of_commutative (h : ∀ x y : G, x * y = y * x) : IsPByAbelian p G := by
  refine ⟨⊥, inferInstance, IsPGroup.of_bot, fun x y => ?_⟩
  rw [h x y, mul_inv_cancel_right, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem map_equiv (e : G ≃* H) (h : IsPByAbelian p G) : IsPByAbelian p H := by
  obtain ⟨N, hN, hp, hc⟩ := h
  refine ⟨N.map e.toMonoidHom, hN.map e.toMonoidHom e.surjective, hp.map e.toMonoidHom,
    fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  exact ⟨a * b * a⁻¹ * b⁻¹, hc a b, by simp⟩

theorem normal_of_le {N S : Subgroup G} (hc : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N) (hNS : N ≤ S) :
    S.Normal where
  conj_mem s hs g := by
    have h := S.mul_mem (hNS (hc g s)) hs
    rwa [inv_mul_cancel_right] at h

theorem normal_sylow [Fact p.Prime] (h : IsPByAbelian p G) (S : Sylow p G) :
    (S : Subgroup G).Normal := by
  obtain ⟨N, hN, hp, hc⟩ := h
  exact normal_of_le hc (hp.le_sylow_of_normal S)

end IsPByAbelian

end CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter

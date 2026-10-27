module

public import CFSG.GH74.KGroups.Generic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Emb

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.GH74.KGroups

theorem ι_conj {D G : Type*} [Group D] [Group G] (M : AutModel D G)
    (hcent : ∀ c : G, (∀ x ∈ M.P, c * x = x * c) → c = 1) (k : D) :
    M.ι (MulAut.conj k) = (M.e k : G) := by
  have h1 : (M.e k : G)⁻¹ * M.ι (MulAut.conj k) = 1 := by
    apply hcent
    intro x hx
    obtain ⟨d, hd⟩ : ∃ d : D, (M.e d : G) = x := ⟨M.e.symm ⟨x, hx⟩, by simp⟩
    have h2 := M.spec (MulAut.conj k) d
    have h3 : (M.e (MulAut.conj k d) : G) = (M.e k : G) * x * (M.e k : G)⁻¹ := by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, ← hd]
      rfl
    rw [h3] at h2
    change (M.e k : G) * x * (M.e k : G)⁻¹ = M.ι (MulAut.conj k) * (M.e d : G) *
      (M.ι (MulAut.conj k))⁻¹ at h2
    rw [hd] at h2
    calc (M.e k : G)⁻¹ * M.ι (MulAut.conj k) * x
        = (M.e k : G)⁻¹ * (M.ι (MulAut.conj k) * x * (M.ι (MulAut.conj k))⁻¹) *
          M.ι (MulAut.conj k) := by group
      _ = (M.e k : G)⁻¹ * ((M.e k : G) * x * (M.e k : G)⁻¹) * M.ι (MulAut.conj k) := by rw [h2]
      _ = x * ((M.e k : G)⁻¹ * M.ι (MulAut.conj k)) := by group
  exact (inv_mul_eq_one.1 h1).symm

theorem exists_embedding {Γ D G : Type*} [Group Γ] [Group D] [Group G] (N : Subgroup Γ)
    [N.Normal] (hC : centralizer (N : Set Γ) = ⊥) (e : N ≃* D) (M : AutModel D G)
    (hcent : ∀ c : G, (∀ x ∈ M.P, c * x = x * c) → c = 1) :
    ∃ ρ : Γ →* G, Function.Injective ρ ∧ ρ.range ≤ M.A ∧ M.P ≤ ρ.range := by
  refine ⟨M.ι.comp (conjEmb N e), M.ι_injective.comp (conjEmb_injective N e hC), ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact M.ι_mem _
  · intro p hp
    set k : D := M.e.symm ⟨p, hp⟩ with hk
    refine ⟨((e.symm k : N) : Γ), ?_⟩
    have hconj : conjEmb N e ((e.symm k : N) : Γ) = MulAut.conj k := by
      ext x
      rw [conjEmb_apply]
      simp [MulAut.conj_apply]
    show M.ι (conjEmb N e ((e.symm k : N) : Γ)) = p
    rw [hconj, ι_conj M hcent k, hk]
    simp

end CFSG.EvenSporadicStandard.HSStd.PumpTC7

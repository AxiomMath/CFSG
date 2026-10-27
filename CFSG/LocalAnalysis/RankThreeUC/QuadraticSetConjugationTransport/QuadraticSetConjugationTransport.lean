module

public import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks

public section

namespace CFSG.LocalAnalysis.RankThreeUC.QuadraticSetConjugationTransport

open Subgroup

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem mem_fixedSubmodule_iff (ρ : Representation (ZMod 2) G V) (N : Subgroup G) (v : V) :
    v ∈ fixedSubmodule ρ N ↔ ∀ n ∈ N, ρ n v = v := by
  unfold fixedSubmodule
  simp only [Representation.mem_invariants]
  constructor
  · intro h n hn
    exact h ⟨n, hn⟩
  · intro h n
    exact h n n.2

theorem fixedSubmodule_map_conj (ρ : Representation (ZMod 2) G V) (g : G) (E : Subgroup G) :
    fixedSubmodule ρ (E.map (MulAut.conj g).toMonoidHom) = (fixedSubmodule ρ E).map (ρ g) := by
  ext v
  rw [mem_fixedSubmodule_iff, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨ρ g⁻¹ v, ?_, ?_⟩
    · rw [mem_fixedSubmodule_iff]
      intro n hn
      have h1 := h (g * n * g⁻¹) ⟨n, hn, by simp⟩
      have e : ρ n (ρ g⁻¹ v) = ρ g⁻¹ (ρ (g * n * g⁻¹) v) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2; group
      rw [e, h1]
    · rw [← Module.End.mul_apply, ← map_mul]; simp
  · rintro ⟨w, hw, rfl⟩
    rintro _ ⟨n, hn, rfl⟩
    rw [mem_fixedSubmodule_iff] at hw
    have e : ρ ((MulAut.conj g).toMonoidHom n) (ρ g w) = ρ g (ρ n w) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2; simp [MulAut.conj_apply]
    rw [e, hw n hn]

end CFSG.LocalAnalysis.RankThreeUC.QuadraticSetConjugationTransport

module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSwapChain
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFPT

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.Permutation.SymmetricCoxeter

variable {G : Type*} [Group G]

theorem symOvergroup {z : G} {m : ℕ} (hm : 7 ≤ m) (hz : orderOf z = 2)
    (D : SwapData z (m + 1)) :
    ∃ (M : Subgroup G) (e : Perm (Fin (m + 1 + 2)) ≃* M), centralizer ({z} : Set G) ≤ M ∧
      ∀ g : G, ∀ hg : g⁻¹ * z * g ∈ M, (e.symm ⟨g⁻¹ * z * g, hg⟩).IsSwap := by
  obtain ⟨M, e, hC, hez⟩ := exists_symmetric_overgroup hm hz D
  refine ⟨M, e, hC, fun g hg => ?_⟩
  have hz2 : z * z = 1 := by rw [← sq, ← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hconjx : IsConj z (g⁻¹ * z * g) := isConj_iff.2 ⟨g⁻¹, by simp⟩
  obtain ⟨Dx⟩ := D.nonempty_of_isConj hconjx
  refine Dx.isSwap_of_conj e hg ?_ ?_ ?_
  · intro h
    apply hz1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  · intro s hs
    have hconj : IsConj (adjSwap (m + 2) (m + 1)) s := by
      rw [adjSwap_of_lt (by omega)]
      obtain ⟨p, q, hpq, rfl⟩ := hs
      exact isConj_swap (by simp [Fin.ext_iff]) hpq
    have h2 : IsConj z (e s : G) := by
      rw [← hez]
      exact (M.subtype.comp e.toMonoidHom).map_isConj hconj
    exact hconjx.symm.trans h2

theorem false_of_swapData [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {z : G} {n : ℕ} (hn : 8 ≤ n) (hz : orderOf z = 2) (D : SwapData z n) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨M, e, hC, hsw⟩ := symOvergroup (by omega) hz D
  exact false_of_symmetric_overgroup hnonab e hz hC hsw

end CFSG.OddStandard.AltStdSec

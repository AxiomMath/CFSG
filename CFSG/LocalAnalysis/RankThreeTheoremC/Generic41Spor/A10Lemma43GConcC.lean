module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GConcA
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GConcDefs
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GConcDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Cent
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Swap

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

namespace A10Perm

open Equiv Equiv.Perm Subgroup

theorem a10t1_cc_mem_L1 {σ : A10} :
    σ ∈ L1 ↔ ∀ i : Fin 10, 5 ≤ (i : ℕ) → (σ : Perm (Fin 10)) i = i := Iff.rfl

theorem a10t1_cc_mem_L2 {σ : A10} :
    σ ∈ L2 ↔ ∀ i : Fin 10, (i : ℕ) < 5 → (σ : Perm (Fin 10)) i = i := Iff.rfl

theorem a10t1_cc_ν₂_lt :
    ∀ i : Fin 10, (i : ℕ) < 5 → 5 ≤ (((ν₂ : A10) : Perm (Fin 10)) i : ℕ) := by decide

theorem a10t1_cc_ν₂_ge :
    ∀ i : Fin 10, 5 ≤ (i : ℕ) → (((ν₂ : A10) : Perm (Fin 10)) i : ℕ) < 5 := by decide

theorem a10t1_cc_swap_aux (n : A10)
    (h1 : ∀ i : Fin 10, (i : ℕ) < 5 → 5 ≤ ((n : Perm (Fin 10)) i : ℕ))
    (h2 : ∀ i : Fin 10, 5 ≤ (i : ℕ) → ((n : Perm (Fin 10)) i : ℕ) < 5) :
    L1.map (MulAut.conj n).toMonoidHom = L2 := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [a10t1_cc_mem_L2]
    intro i hi
    have hj : 5 ≤ ((((n : A10) : Perm (Fin 10))⁻¹ i : Fin 10) : ℕ) := by
      by_contra h
      have h' := h1 (((n : A10) : Perm (Fin 10))⁻¹ i) (by omega)
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h'
      omega
    have hfix := (a10t1_cc_mem_L1.1 hσ) _ hj
    show ((n : A10) : Perm (Fin 10)) ((σ : Perm (Fin 10)) (((n : A10) : Perm (Fin 10))⁻¹ i)) = i
    rw [hfix]
    exact Equiv.apply_symm_apply _ _
  · intro hy
    rw [a10t1_cc_mem_L2] at hy
    refine ⟨n⁻¹ * y * n, ?_, ?_⟩
    · rw [a10t1_cc_mem_L1]
      intro i hi
      have hlt := h2 i hi
      have hfix := hy (((n : A10) : Perm (Fin 10)) i) hlt
      show (((n : A10) : Perm (Fin 10))⁻¹ ((y : Perm (Fin 10)) (((n : A10) : Perm (Fin 10)) i))) = i
      rw [hfix]
      exact Equiv.symm_apply_apply _ _
    · show n * (n⁻¹ * y * n) * n⁻¹ = y
      group

theorem cent_L : ∀ s ∈ S₀, s ≠ 1 → (s ∈ L1 ∨ s ∈ L2) →
    Nat.card ↥(Subgroup.centralizer ({s} : Set A10)) = 300 := by
  intro s hs hs1 h
  rcases h with h | h
  · have h1 : s ∈ line₁ := by rw [← S₀_inf_L1]; exact ⟨hs, h⟩
    exact a10c_card_line₁ h1 hs1
  · have h2 : s ∈ line₂ := by rw [← S₀_inf_L2]; exact ⟨hs, h⟩
    exact a10c_card_line₂ h2 hs1

theorem cent_diag : ∀ s ∈ S₀, s ∉ L1 → s ∉ L2 →
    Nat.card ↥(Subgroup.centralizer ({s} : Set A10)) = 25 := by
  intro s hs h1 h2
  refine a10c_card_diag hs (fun h => h1 ?_) (fun h => h2 ?_)
  · have h' : s ∈ S₀ ⊓ L1 := by rw [S₀_inf_L1]; exact h
    exact h'.2
  · have h' : s ∈ S₀ ⊓ L2 := by rw [S₀_inf_L2]; exact h
    exact h'.2

theorem swap_L : ∃ n ∈ Subgroup.normalizer (S₀ : Set A10),
    L1.map (MulAut.conj n).toMonoidHom = L2 :=
  ⟨ν₂, spt_ν₂_mem, a10t1_cc_swap_aux ν₂ a10t1_cc_ν₂_lt a10t1_cc_ν₂_ge⟩

end A10Perm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

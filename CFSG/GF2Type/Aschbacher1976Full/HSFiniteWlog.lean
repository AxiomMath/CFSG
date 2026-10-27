module

public import CFSG.GF2Type.Aschbacher1976Full.HSFiniteDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Six

open Equiv

@[expose] def dA : Perm (Fin 6) := dt 0 1 2 3

@[expose] def eA : Perm (Fin 6) := dt 0 1 4 5

@[expose] def dB : Perm (Fin 6) := dt 0 1 2 3

@[expose] def eB : Perm (Fin 6) := dt 0 2 1 3

@[expose] def invsT : List (List ℕ) := (allT 6).filter (fun a => decide (mulT a a = oneT 6))

theorem wlogT : ∀ a ∈ invsT, ∀ b ∈ invsT, suppT 6 b = suppT 6 a → a ≠ b → mulT a b = mulT b a →
    suppT 6 (mulT a b) = suppT 6 a →
    suppT 6 a = 4 ∧ ∃ s ∈ allT 6, (mulT s a = mulT (tab dA) s ∧ mulT s b = mulT (tab eA) s) ∨
      (mulT s a = mulT (tab dB) s ∧ mulT s b = mulT (tab eB) s) := by
  decide +kernel

theorem tab_mem_invsT {s : Perm (Fin 6)} (hs : s * s = 1) : tab s ∈ invsT := by
  simp only [invsT, List.mem_filter, decide_eq_true_eq]
  exact ⟨mem_allT s, by rw [← tab_mul, hs, tab_one]⟩

theorem conj_eq_of_mulT {σ d x : Perm (Fin 6)} (h : mulT (tab σ) (tab d) = mulT (tab x) (tab σ)) :
    σ * d * σ⁻¹ = x := by
  rw [← tab_mul, ← tab_mul] at h
  rw [tab_injective h, mul_inv_cancel_right]

theorem wlog_pair {d e : Perm (Fin 6)} (hd : d * d = 1) (he : e * e = 1) (hne : d ≠ e)
    (hc : d * e = e * d) (h1 : e.support.card = d.support.card)
    (h2 : (d * e).support.card = d.support.card) :
    d.support.card = 4 ∧ ∃ σ : Perm (Fin 6),
      (σ * d * σ⁻¹ = dA ∧ σ * e * σ⁻¹ = eA) ∨ (σ * d * σ⁻¹ = dB ∧ σ * e * σ⁻¹ = eB) := by
  obtain ⟨h4, s, hs, hcases⟩ := wlogT (tab d) (tab_mem_invsT hd) (tab e) (tab_mem_invsT he)
    (by rw [suppT_tab, suppT_tab, h1]) (fun h => hne (tab_injective h))
    (by rw [← tab_mul, ← tab_mul, hc]) (by rw [← tab_mul, suppT_tab, suppT_tab, h2])
  obtain ⟨σ, rfl⟩ := exists_of_mem_allT hs
  refine ⟨by rwa [suppT_tab] at h4, σ, ?_⟩
  rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨conj_eq_of_mulT ha, conj_eq_of_mulT hb⟩
  · exact Or.inr ⟨conj_eq_of_mulT ha, conj_eq_of_mulT hb⟩

end CFSG.GF2Type.Aschbacher1976Full.HS.Six

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57R3

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Equiv

variable {S : Type} [CommGroup S] [Finite S] {ρ : Perm (Fin 7) →* MulAut S}
  {E₀ : Subgroup (Perm (Fin 7))}

@[expose] def V0 : Subgroup (Perm (Fin 7)) :=
  Subgroup.closure ({swap 0 1 * swap 2 3, swap 0 2 * swap 1 3} : Set (Perm (Fin 7)))

theorem card_V0 : Nat.card V0 = 4 := by
  unfold V0
  exact card_closure_pair (x := swap 0 1 * swap 2 3) (y := swap 0 2 * swap 1 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem x01_mem : swap 0 1 * swap 2 3 ∈ V0 := Subgroup.subset_closure (by simp)

theorem x02_mem : swap 0 2 * swap 1 3 ∈ V0 := Subgroup.subset_closure (by simp)

theorem x03_mem : swap 0 3 * swap 1 2 ∈ V0 := by
  have : swap (0 : Fin 7) 3 * swap 1 2 = (swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3) := by
    decide +kernel
  rw [this]
  exact V0.mul_mem x01_mem x02_mem

omit [Finite S] in
theorem key4 (D : MinOffData ρ E₀) (hcard : Nat.card E₀ = 8) {a b c d e f : Fin 7}
    (hnd : [a, b, c, d, e, f].Nodup) (h1 : swap e f ∈ E₀) (h2 : swap a b * swap c d ∈ E₀)
    (h3 : swap a c * swap b d ∈ E₀) {e' f' : Fin 7} (hn : [(0 : Fin 7), 1, 2, 3, e', f'].Nodup) :
    ∃ σ : Perm (Fin 7), Cs ρ V0 = Cs ρ (conjE σ E₀) ∧ swap e' f' ∈ conjE σ E₀ := by
  obtain ⟨σ, hσ⟩ := exists_perm_list [a, b, c, d, e, f] [0, 1, 2, 3, e', f'] hnd hn rfl
  have s0 : σ a = 0 := hσ 0 (by simp)
  have s1 : σ b = 1 := hσ 1 (by simp)
  have s2 : σ c = 2 := hσ 2 (by simp)
  have s3 : σ d = 3 := hσ 3 (by simp)
  have s4 : σ e = e' := hσ 4 (by simp)
  have s5 : σ f = f' := hσ 5 (by simp)
  have m1 : swap e' f' ∈ conjE σ E₀ := swap_mem_conjE s4 s5 h1
  have m2 : swap 0 1 * swap 2 3 ∈ conjE σ E₀ := by
    have := conj_mem_conjE (σ := σ) h2
    rwa [conj_swap_mul_swap, s0, s1, s2, s3] at this
  have m3 : swap 0 2 * swap 1 3 ∈ conjE σ E₀ := by
    have := conj_mem_conjE (σ := σ) h3
    rwa [conj_swap_mul_swap, s0, s2, s1, s3] at this
  have hle : V0 ≤ conjE σ E₀ := by
    unfold V0
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact m2
    · exact m3
  exact ⟨σ, cs_eq_of_index_two D hcard σ hle card_V0, m1⟩

theorem R4_false (D : MinOffData ρ E₀) (hcard : Nat.card E₀ = 8) {a b c d e f : Fin 7}
    (hnd : [a, b, c, d, e, f].Nodup) (h1 : swap e f ∈ E₀) (h2 : swap a b * swap c d ∈ E₀)
    (h3 : swap a c * swap b d ∈ E₀) : False := by
  obtain ⟨σ1, hσ1, m45⟩ := key4 D hcard hnd h1 h2 h3 (e' := 4) (f' := 5) (by decide)
  obtain ⟨σ2, hσ2, m46⟩ := key4 D hcard hnd h1 h2 h3 (e' := 4) (f' := 6) (by decide)
  obtain ⟨σ3, hσ3, m56⟩ := key4 D hcard hnd h1 h2 h3 (e' := 5) (f' := 6) (by decide)
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Subgroup S, F₀ = Cs ρ V0 := ⟨_, rfl⟩
  have hF : ∀ x ∈ x4, ∀ w ∈ F₀, ρ x w = w := by
    intro x hx w hw
    simp only [x4, List.mem_cons, List.not_mem_nil, or_false] at hx
    have hw' : w ∈ Cs ρ V0 := by
      rw [← hF₀]
      exact hw
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (mem_Cs ρ).1 hw' _ x01_mem
    · exact (mem_Cs ρ).1 hw' _ x02_mem
    · exact (mem_Cs ρ).1 hw' _ x03_mem
    · have : w ∈ Cs ρ (conjE σ1 E₀) := by
        rw [← hσ1]
        exact hw'
      exact (mem_Cs ρ).1 this _ m45
    · have : w ∈ Cs ρ (conjE σ2 E₀) := by
        rw [← hσ2]
        exact hw'
      exact (mem_Cs ρ).1 this _ m46
    · have : w ∈ Cs ρ (conjE σ3 E₀) := by
        rw [← hσ3]
        exact hw'
      exact (mem_Cs ρ).1 this _ m56
  have hcF : Nat.card F₀ = Nat.card (Cs ρ E₀) := by
    rw [hF₀, hσ1, card_Cs_conj]
  have hS := D.card_S
  rw [hcard, ← hcF] at hS
  have hbig := D.big
  exact family_false D hF xt4 cj4 tab4 ent4_ok tab4_cover (by omega) hS

end CFSG.QuasithinUnique.B42A57

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57FamArg
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57FamData
public import Certificates.Certificate17023

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Equiv

variable {S : Type} [CommGroup S] [Finite S] {ρ : Perm (Fin 7) →* MulAut S}
  {E₀ : Subgroup (Perm (Fin 7))}

omit [Finite S] in
theorem cs_eq_of_index_two (D : MinOffData ρ E₀) (hcard : Nat.card E₀ = 8) (σ : Perm (Fin 7))
    {B : Subgroup (Perm (Fin 7))} (hB : B ≤ conjE σ E₀) (hc : Nat.card B = 4) :
    Cs ρ B = Cs ρ (conjE σ E₀) := by
  apply D.max σ B hB
  · intro h
    rw [h] at hc
    simp at hc
  · rw [card_conjE, hcard, hc]

theorem conj_mem_conjE {σ x : Perm (Fin 7)} (h : x ∈ E₀) : σ * x * σ⁻¹ ∈ conjE σ E₀ := by
  rw [mem_conjE]
  have : σ⁻¹ * (σ * x * σ⁻¹) * σ = x := by group
  rw [this]
  exact h

theorem conj_swap_mul_swap (σ : Perm (Fin 7)) (a b c d : Fin 7) :
    σ * (swap a b * swap c d) * σ⁻¹ = swap (σ a) (σ b) * swap (σ c) (σ d) := by
  have hsw : ∀ a b : Fin 7, σ * swap a b * σ⁻¹ = swap (σ a) (σ b) := fun a b => by
    rw [Equiv.swap_apply_apply]
  rw [← hsw, ← hsw]
  group

theorem card_swap_pair {a b c d : Fin 7} (h : [a, b, c, d].Nodup) :
    Nat.card (Subgroup.closure ({swap a b, swap c d} : Set (Perm (Fin 7)))) = 4 := by
  have h' := h
  simp at h'
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := h'
  have hcomm : swap a b * swap c d = swap c d * swap a b :=
    (Equiv.Perm.disjoint_swap_swap h).commute
  have hne : swap a b ≠ swap c d := by
    intro heq
    have h1 := congrArg (fun f : Perm (Fin 7) => f a) heq
    simp only [Equiv.swap_apply_left] at h1
    rw [Equiv.swap_apply_of_ne_of_ne hac had] at h1
    exact hab h1.symm
  exact card_closure_pair (swap_mul_self' a b) (swap_mul_self' c d) hcomm (swap_ne_one' hab)
    (swap_ne_one' hcd) hne

omit [Finite S] in
theorem triple_cs (D : MinOffData ρ E₀) (hcard : Nat.card E₀ = 8) {a b c d e f : Fin 7}
    (hnd : [a, b, c, d, e, f].Nodup) (h1 : swap a b ∈ E₀) (h2 : swap c d ∈ E₀)
    (h3 : swap e f ∈ E₀) {a' b' c' d' e' f' : Fin 7} (hnd' : [a', b', c', d', e', f'].Nodup) :
    ∃ σ : Perm (Fin 7),
      Cs ρ (Subgroup.closure ({swap a' b', swap c' d'} : Set (Perm (Fin 7)))) =
        Cs ρ (conjE σ E₀) ∧
      Cs ρ (Subgroup.closure ({swap a' b', swap e' f'} : Set (Perm (Fin 7)))) =
        Cs ρ (conjE σ E₀) := by
  obtain ⟨σ, hσ⟩ := exists_perm_list [a, b, c, d, e, f] [a', b', c', d', e', f'] hnd hnd' rfl
  have s0 : σ a = a' := hσ 0 (by simp)
  have s1 : σ b = b' := hσ 1 (by simp)
  have s2 : σ c = c' := hσ 2 (by simp)
  have s3 : σ d = d' := hσ 3 (by simp)
  have s4 : σ e = e' := hσ 4 (by simp)
  have s5 : σ f = f' := hσ 5 (by simp)
  have hm1 := swap_mem_conjE s0 s1 h1
  have hm2 := swap_mem_conjE s2 s3 h2
  have hm3 := swap_mem_conjE s4 s5 h3
  have n1 : [a', b', c', d'].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnd' ⊢
    tauto
  have n2 : [a', b', e', f'].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnd' ⊢
    tauto
  refine ⟨σ, ?_, ?_⟩
  · refine cs_eq_of_index_two D hcard σ ?_ (card_swap_pair n1)
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hm1
    · exact hm2
  · refine cs_eq_of_index_two D hcard σ ?_ (card_swap_pair n2)
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hm1
    · exact hm3

omit [Finite S] in
theorem K_eq (D : MinOffData ρ E₀) (hcard : Nat.card E₀ = 8) {a b c d e f : Fin 7}
    (hnd : [a, b, c, d, e, f].Nodup) (h1 : swap a b ∈ E₀) (h2 : swap c d ∈ E₀)
    (h3 : swap e f ∈ E₀) {i j k l : Fin 7} (h : [0, 1, i, j, k, l].Nodup) :
    Cs ρ (Subgroup.closure ({swap 0 1, swap i j} : Set (Perm (Fin 7)))) =
      Cs ρ (Subgroup.closure ({swap 0 1, swap k l} : Set (Perm (Fin 7)))) := by
  obtain ⟨σ, hσ1, hσ2⟩ := triple_cs D hcard hnd h1 h2 h3 h
  rw [hσ1, hσ2]

theorem chain3 : ∀ i j : Fin 7, 2 ≤ i.val → i < j →
    (i = 2 ∧ j = 3) ∨ [0, 1, 2, 3, i, j].Nodup ∨
      ∃ k l : Fin 7, [0, 1, 2, 3, k, l].Nodup ∧ [0, 1, i, j, k, l].Nodup :=
  Certificates.certificate17023

theorem R3_false
    (D : MinOffData ρ E₀) (hcard : Nat.card E₀ = 8) {a b c d e f : Fin 7}
    (hnd : [a, b, c, d, e, f].Nodup) (h1 : swap a b ∈ E₀) (h2 : swap c d ∈ E₀)
    (h3 : swap e f ∈ E₀) : False := by
  have hnd0 : [(0 : Fin 7), 1, 2, 3, 4, 5].Nodup := by decide
  obtain ⟨σ, hσ1, -⟩ := triple_cs D hcard hnd h1 h2 h3 hnd0
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Subgroup S,
      F₀ = Cs ρ (Subgroup.closure ({swap 0 1, swap 2 3} : Set (Perm (Fin 7)))) := ⟨_, rfl⟩
  have Kij : ∀ i j : Fin 7, 2 ≤ i.val → i < j →
      F₀ = Cs ρ (Subgroup.closure ({swap 0 1, swap i j} : Set (Perm (Fin 7)))) := by
    intro i j hi hij
    rcases chain3 i j hi hij with ⟨rfl, rfl⟩ | hn | ⟨k, l, hk, hk'⟩
    · exact hF₀
    · rw [hF₀]
      exact K_eq D hcard hnd h1 h2 h3 hn
    · rw [hF₀]
      exact (K_eq D hcard hnd h1 h2 h3 hk).trans (K_eq D hcard hnd h1 h2 h3 hk').symm
  have fix : ∀ i j : Fin 7, 2 ≤ i.val → i < j → ∀ w ∈ F₀, ρ (swap i j) w = w := by
    intro i j hi hij w hw
    rw [Kij i j hi hij] at hw
    exact (mem_Cs_closure ρ).1 hw (swap i j) (by simp)
  have hF : ∀ x ∈ x3, ∀ w ∈ F₀, ρ x w = w := by
    intro x hx w hw
    simp only [x3, List.mem_cons, List.not_mem_nil, or_false] at hx
    have hw' : w ∈ Cs ρ (Subgroup.closure ({swap 0 1, swap 2 3} : Set (Perm (Fin 7)))) := by
      rw [← hF₀]
      exact hw
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (mem_Cs_closure ρ).1 hw' _ (by simp)
    · exact (mem_Cs_closure ρ).1 hw' _ (by simp)
    · exact fix 2 4 (by decide) (by decide) w hw
    · exact fix 2 5 (by decide) (by decide) w hw
    · exact fix 2 6 (by decide) (by decide) w hw
    · exact fix 3 4 (by decide) (by decide) w hw
    · exact fix 3 5 (by decide) (by decide) w hw
    · exact fix 3 6 (by decide) (by decide) w hw
    · exact fix 4 5 (by decide) (by decide) w hw
    · exact fix 4 6 (by decide) (by decide) w hw
    · exact fix 5 6 (by decide) (by decide) w hw
  have hcF : Nat.card F₀ = Nat.card (Cs ρ E₀) := by
    rw [hF₀, hσ1, card_Cs_conj]
  have hS := D.card_S
  rw [hcard, ← hcF] at hS
  have hbig := D.big
  exact family_false D hF xt3 cj3 tab3 ent3_ok tab3_cover (by omega) hS

end CFSG.QuasithinUnique.B42A57

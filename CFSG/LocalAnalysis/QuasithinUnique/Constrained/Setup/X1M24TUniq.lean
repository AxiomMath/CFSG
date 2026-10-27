module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightGen

public section

namespace CFSG.QuasithinUnique.Setup.X1

section Union

theorem le_or_le_of_forall_mem {G : Type*} [Group G] {B E₁ E₂ : Subgroup G}
    (h : ∀ x ∈ B, x ∈ E₁ ∨ x ∈ E₂) : B ≤ E₁ ∨ B ≤ E₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  obtain ⟨a, haB, haE⟩ := IsConcreteLE.not_le_iff_exists.1 hn1
  obtain ⟨b, hbB, hbE⟩ := IsConcreteLE.not_le_iff_exists.1 hn2
  have ha2 : a ∈ E₂ := (h a haB).resolve_left haE
  have hb1 : b ∈ E₁ := (h b hbB).resolve_right hbE
  rcases h (a * b) (B.mul_mem haB hbB) with hab | hab
  · exact haE (by simpa using E₁.mul_mem hab (E₁.inv_mem hb1))
  · exact hbE (by simpa using E₂.mul_mem (E₂.inv_mem ha2) hab)

theorem card_eq_length_of_list_subgroup {S : Type} [Group S] {E : Subgroup S} {El : List S}
    (hEl : ∀ x, x ∈ E ↔ x ∈ El) (hnd : El.Nodup) : Nat.card E = El.length := by
  classical
  have hset : (E : Set S) = ↑El.toFinset := by
    ext x
    simp [hEl x]
  have : Nat.card E = (E : Set S).ncard := Nat.card_coe_set_eq _
  rw [this, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

end Union

variable {S : Type} [Group S] [Finite S] [DecidableEq S] {a m : ℕ} {Rl : List S}

theorem SylowData.unique64 (h : SylowData S a m Rl) (E₁ E₂ : Subgroup S) (El₁ El₂ : List S)
    (hEl₁ : ∀ x, x ∈ E₁ ↔ x ∈ El₁) (hEl₂ : ∀ x, x ∈ E₂ ↔ x ∈ El₂)
    (hE₁ : Nat.card E₁ = 64) (hE₂ : Nat.card E₂ = 64)
    (hheavy : heavyList Rl (El₁ ++ El₂) 62 = [])
    (B : Subgroup S) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hB : Nat.card B = 64) :
    ∃ g : S, (∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ E₁) ∨ (∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ E₂) := by
  classical
  obtain ⟨g, hg⟩ := h.conj_into B hsq
  set B' : Subgroup S := B.map (MulAut.conj g).toMonoidHom with hB'
  have hB'card : Nat.card B' = 64 := by
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj g).injective, hB]
  have hB'R : ∀ y ∈ B', y ∈ Rl := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := conj_map_mem.1 hy
    exact hg x hx
  have hB'sq : ∀ y ∈ B', y * y = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := conj_map_mem.1 hy
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hsq x hx]; group
  have hB'comm : ∀ y ∈ B', ∀ z ∈ B', y * z = z * y := by
    intro y hy z hz
    obtain ⟨x, hx, rfl⟩ := conj_map_mem.1 hy
    obtain ⟨x', hx', rfl⟩ := conj_map_mem.1 hz
    calc g * x * g⁻¹ * (g * x' * g⁻¹) = g * (x * x') * g⁻¹ := by group
      _ = g * (x' * x) * g⁻¹ := by rw [hcomm x hx x' hx']
      _ = _ := by group
  have hcov : ∀ y ∈ B', y ∈ E₁ ∨ y ∈ E₂ := by
    intro y hyB
    by_contra hcon
    push Not at hcon
    obtain ⟨hy1, hy2⟩ := hcon
    have hyn : y ∉ El₁ ++ El₂ := by
      simp only [List.mem_append, not_or]
      exact ⟨fun hm => hy1 ((hEl₁ y).2 hm), fun hm => hy2 ((hEl₂ y).2 hm)⟩
    have hy1' : y ≠ 1 := fun h1 => hy1 (h1 ▸ E₁.one_mem)
    have hmem : y ∈ heavyList Rl (El₁ ++ El₂) 62 := by
      simp only [heavyList, List.mem_filter, decide_eq_true_eq]
      refine ⟨⟨mem_invG.2 ⟨hB'R y hyB, hy1', hB'sq y hyB⟩, hyn⟩, ?_⟩
      have hsub2 : ((B' : Set S) \ {1, y}) ⊆
          ↑((invG Rl).filter fun z => z ≠ y ∧ y * z = z * y).toFinset := by
        rintro z ⟨hzB, hz1⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz1
        simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
        exact ⟨mem_invG.2 ⟨hB'R z hzB, hz1.1, hB'sq z hzB⟩, hz1.2, hB'comm y hyB z hzB⟩
      have hc2 : ({1, y} : Set S).ncard = 2 := by
        rw [Set.ncard_pair (Ne.symm hy1')]
      have hsub3 : ({1, y} : Set S) ⊆ (B' : Set S) := by
        intro z hz
        rcases hz with rfl | rfl
        · exact B'.one_mem
        · exact hyB
      have hc62 : ((B' : Set S) \ {1, y}).ncard = 62 := by
        rw [Set.ncard_sdiff hsub3, hc2]
        have : (B' : Set S).ncard = 64 := by rw [← Nat.card_coe_set_eq]; exact hB'card
        omega
      calc 62 = ((B' : Set S) \ {1, y}).ncard := hc62.symm
        _ ≤ (↑((invG Rl).filter fun z => z ≠ y ∧ y * z = z * y).toFinset : Set S).ncard :=
            Set.ncard_le_ncard hsub2 (Finset.finite_toSet _)
        _ = ((invG Rl).filter fun z => z ≠ y ∧ y * z = z * y).toFinset.card :=
            Set.ncard_coe_finset _
        _ ≤ ((invG Rl).filter fun z => z ≠ y ∧ y * z = z * y).length :=
            List.toFinset_card_le _
    rw [hheavy] at hmem
    simp at hmem
  have hconj : ∀ E : Subgroup S, B' = E → ∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ E := by
    intro E hE x
    rw [← hE, hB']
    constructor
    · intro hx
      exact conj_map_mem.2 ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨x', hx', hxx'⟩ := conj_map_mem.1 hx
      have : x' = x := by
        have := mul_left_cancel (mul_right_cancel (hxx'.trans rfl : g * x' * g⁻¹ = g * x * g⁻¹))
        exact this
      rw [← this]
      exact hx'
  rcases le_or_le_of_forall_mem hcov with hle | hle
  · exact ⟨g, Or.inl (hconj E₁ (Subgroup.eq_of_le_of_card_ge hle (by rw [hB'card, hE₁])))⟩
  · exact ⟨g, Or.inr (hconj E₂ (Subgroup.eq_of_le_of_card_ge hle (by rw [hB'card, hE₂])))⟩

end CFSG.QuasithinUnique.Setup.X1

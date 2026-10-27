module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open Finset

theorem exists_even_perm_of_emb {m : ℕ} (hm : m ≤ 6) (x y : Fin m ↪ Fin 8) :
    ∃ g : Equiv.Perm (Fin 8), Equiv.Perm.sign g = 1 ∧ ∀ i, g (x i) = y i := by
  haveI h6 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) 6 := by
    have := alternatingGroup.isMultiplyPretransitive (Fin 8)
    simpa using this
  haveI : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) m :=
    MulAction.isMultiplyPretransitive_of_le hm (by simp)
  obtain ⟨g, hg⟩ := MulAction.isMultiplyPretransitive_iff.mp this x y
  refine ⟨g, g.2, fun i => ?_⟩
  have := congrArg (fun e : Fin m ↪ Fin 8 => e i) hg
  simpa [Function.Embedding.smul_apply, Subgroup.smul_def, Equiv.Perm.smul_def] using this

theorem exists_even_perm_card {k : ℕ} (hk : k ≤ 6) {S T : Finset (Fin 8)} (hS : S.card = k)
    (hT : T.card = k) :
    ∃ g : Equiv.Perm (Fin 8), Equiv.Perm.sign g = 1 ∧ ∀ z, g z ∈ T ↔ z ∈ S := by
  obtain ⟨g, hg, hgx⟩ := exists_even_perm_of_emb hk (S.orderEmbOfFin hS).toEmbedding
    (T.orderEmbOfFin hT).toEmbedding
  refine ⟨g, hg, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · have h1 : g z ∈ Set.range (T.orderEmbOfFin hT) := by
      rw [Finset.range_orderEmbOfFin]; exact hz
    obtain ⟨j, hj⟩ := h1
    have h2 : g (S.orderEmbOfFin hS j) = g z := by
      have := hgx j
      simp only [RelEmbedding.coe_toEmbedding] at this
      rw [this]; exact hj
    rw [← g.injective h2]
    exact Finset.orderEmbOfFin_mem S hS j
  · have h1 : z ∈ Set.range (S.orderEmbOfFin hS) := by
      rw [Finset.range_orderEmbOfFin]; exact hz
    obtain ⟨j, rfl⟩ := h1
    have := hgx j
    simp only [RelEmbedding.coe_toEmbedding] at this
    rw [this]
    exact Finset.orderEmbOfFin_mem T hT j

theorem exists_cell_emb {A B : Finset (Fin 8)} (hA : A.card = 4) (hB : B.card = 4)
    (hAB : (A ∩ B).card = 2) :
    ∃ e : Fin 6 ↪ Fin 8, (∀ z, z ∈ A ↔ (z = e 0 ∨ z = e 1 ∨ z = e 2 ∨ z = e 3)) ∧
      (∀ z, z ∈ B ↔ (z = e 0 ∨ z = e 1 ∨ z = e 4 ∨ z = e 5)) := by
  have h2 : (A \ B).card = 2 := by
    have := Finset.card_sdiff_add_card_inter A B
    omega
  have h3 : (B \ A).card = 2 := by
    have := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at this
    omega
  obtain ⟨p₁, p₂, h12, e1⟩ := Finset.card_eq_two.mp hAB
  obtain ⟨p₃, p₄, h34, e2⟩ := Finset.card_eq_two.mp h2
  obtain ⟨p₅, p₆, h56, e3⟩ := Finset.card_eq_two.mp h3
  have m1 : ∀ z, (z ∈ A ∧ z ∈ B) ↔ (z = p₁ ∨ z = p₂) := by
    intro z
    rw [← Finset.mem_inter, e1]
    simp
  have m2 : ∀ z, (z ∈ A ∧ z ∉ B) ↔ (z = p₃ ∨ z = p₄) := by
    intro z
    rw [← Finset.mem_sdiff, e2]
    simp
  have m3 : ∀ z, (z ∈ B ∧ z ∉ A) ↔ (z = p₅ ∨ z = p₆) := by
    intro z
    rw [← Finset.mem_sdiff, e3]
    simp
  have a1 : p₁ ∈ A ∧ p₁ ∈ B := (m1 p₁).2 (Or.inl rfl)
  have a2 : p₂ ∈ A ∧ p₂ ∈ B := (m1 p₂).2 (Or.inr rfl)
  have a3 : p₃ ∈ A ∧ p₃ ∉ B := (m2 p₃).2 (Or.inl rfl)
  have a4 : p₄ ∈ A ∧ p₄ ∉ B := (m2 p₄).2 (Or.inr rfl)
  have a5 : p₅ ∈ B ∧ p₅ ∉ A := (m3 p₅).2 (Or.inl rfl)
  have a6 : p₆ ∈ B ∧ p₆ ∉ A := (m3 p₆).2 (Or.inr rfl)
  have hneB : ∀ x y : Fin 8, x ∈ B → y ∉ B → x ≠ y := fun x y hx hy h => hy (h ▸ hx)
  have hneA : ∀ x y : Fin 8, x ∈ A → y ∉ A → x ≠ y := fun x y hx hy h => hy (h ▸ hx)
  have inj : Function.Injective ![p₁, p₂, p₃, p₄, p₅, p₆] := by
    intro i j hij
    have n13 := hneB _ _ a1.2 a3.2
    have n14 := hneB _ _ a1.2 a4.2
    have n23 := hneB _ _ a2.2 a3.2
    have n24 := hneB _ _ a2.2 a4.2
    have n15 := hneA _ _ a1.1 a5.2
    have n16 := hneA _ _ a1.1 a6.2
    have n25 := hneA _ _ a2.1 a5.2
    have n26 := hneA _ _ a2.1 a6.2
    have n35 := hneA _ _ a3.1 a5.2
    have n36 := hneA _ _ a3.1 a6.2
    have n45 := hneA _ _ a4.1 a5.2
    have n46 := hneA _ _ a4.1 a6.2
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first
      | exact absurd hij ‹_›
      | exact absurd hij.symm ‹_›
  refine ⟨⟨_, inj⟩, fun z => ?_, fun z => ?_⟩
  · show z ∈ A ↔ (z = p₁ ∨ z = p₂ ∨ z = p₃ ∨ z = p₄)
    by_cases hz : z ∈ B
    · constructor
      · intro h
        rcases (m1 z).1 ⟨h, hz⟩ with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · intro h
        rcases h with h | h | h | h
        · exact h ▸ a1.1
        · exact h ▸ a2.1
        · exact absurd hz (h ▸ a3.2)
        · exact absurd hz (h ▸ a4.2)
    · constructor
      · intro h
        rcases (m2 z).1 ⟨h, hz⟩ with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · intro h
        rcases h with h | h | h | h
        · exact h ▸ a1.1
        · exact h ▸ a2.1
        · exact h ▸ a3.1
        · exact h ▸ a4.1
  · show z ∈ B ↔ (z = p₁ ∨ z = p₂ ∨ z = p₅ ∨ z = p₆)
    by_cases hz : z ∈ A
    · constructor
      · intro h
        rcases (m1 z).1 ⟨hz, h⟩ with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · intro h
        rcases h with h | h | h | h
        · exact h ▸ a1.2
        · exact h ▸ a2.2
        · exact absurd hz (h ▸ a5.2)
        · exact absurd hz (h ▸ a6.2)
    · constructor
      · intro h
        rcases (m3 z).1 ⟨h, hz⟩ with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · intro h
        rcases h with h | h | h | h
        · exact h ▸ a1.2
        · exact h ▸ a2.2
        · exact h ▸ a5.1
        · exact h ▸ a6.1

theorem exists_even_perm_cross {A B A' B' : Finset (Fin 8)} (hA : A.card = 4) (hB : B.card = 4)
    (hAB : (A ∩ B).card = 2) (hA' : A'.card = 4) (hB' : B'.card = 4) (hAB' : (A' ∩ B').card = 2) :
    ∃ g : Equiv.Perm (Fin 8), Equiv.Perm.sign g = 1 ∧ (∀ z, g z ∈ A' ↔ z ∈ A) ∧
      ∀ z, g z ∈ B' ↔ z ∈ B := by
  obtain ⟨e, he1, he2⟩ := exists_cell_emb hA hB hAB
  obtain ⟨e', he1', he2'⟩ := exists_cell_emb hA' hB' hAB'
  obtain ⟨g, hg, hge⟩ := exists_even_perm_of_emb (le_refl 6) e e'
  refine ⟨g, hg, fun z => ?_, fun z => ?_⟩
  · rw [he1, he1']
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl (g.injective (h.trans (hge 0).symm))
      · exact Or.inr (Or.inl (g.injective (h.trans (hge 1).symm)))
      · exact Or.inr (Or.inr (Or.inl (g.injective (h.trans (hge 2).symm))))
      · exact Or.inr (Or.inr (Or.inr (g.injective (h.trans (hge 3).symm))))
    · rintro (h | h | h | h)
      · exact Or.inl (h ▸ hge 0)
      · exact Or.inr (Or.inl (h ▸ hge 1))
      · exact Or.inr (Or.inr (Or.inl (h ▸ hge 2)))
      · exact Or.inr (Or.inr (Or.inr (h ▸ hge 3)))
  · rw [he2, he2']
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl (g.injective (h.trans (hge 0).symm))
      · exact Or.inr (Or.inl (g.injective (h.trans (hge 1).symm)))
      · exact Or.inr (Or.inr (Or.inl (g.injective (h.trans (hge 4).symm))))
      · exact Or.inr (Or.inr (Or.inr (g.injective (h.trans (hge 5).symm))))
    · rintro (h | h | h | h)
      · exact Or.inl (h ▸ hge 0)
      · exact Or.inr (Or.inl (h ▸ hge 1))
      · exact Or.inr (Or.inr (Or.inl (h ▸ hge 4)))
      · exact Or.inr (Or.inr (Or.inr (h ▸ hge 5)))

theorem exists_mid_aux : ∀ S ∈ powersetCard 4 (univ : Finset (Fin 8)),
    ∀ T ∈ powersetCard 4 (univ : Finset (Fin 8)), (S ∩ T).card ≠ 2 → T ≠ S → T ≠ Sᶜ →
      ∃ R ∈ powersetCard 4 (univ : Finset (Fin 8)), (S ∩ R).card = 2 ∧ (T ∩ R).card = 2 := by
  decide +kernel

theorem exists_mid {S T : Finset (Fin 8)} (hS : S.card = 4) (hT : T.card = 4)
    (h2 : (S ∩ T).card ≠ 2) (h1 : T ≠ S) (h3 : T ≠ Sᶜ) :
    ∃ R : Finset (Fin 8), R.card = 4 ∧ (S ∩ R).card = 2 ∧ (T ∩ R).card = 2 := by
  obtain ⟨R, hR, hSR, hTR⟩ := exists_mid_aux S (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩)
    T (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩) h2 h1 h3
  exact ⟨R, (Finset.mem_powersetCard.mp hR).2, hSR, hTR⟩

theorem exists_small (S : Finset (Fin 8)) (hS : Even S.card) :
    ∃ T : Finset (Fin 8), (T = S ∨ T = Sᶜ) ∧ (T.card = 0 ∨ T.card = 2 ∨ T.card = 4) := by
  have hle : S.card ≤ 8 := by
    have := Finset.card_le_univ S
    simpa using this
  obtain ⟨m, hm⟩ := hS
  have hc : Sᶜ.card = 8 - S.card := by
    rw [Finset.card_compl]
    simp
  by_cases h : S.card ≤ 4
  · exact ⟨S, Or.inl rfl, by omega⟩
  · exact ⟨Sᶜ, Or.inr rfl, by omega⟩

@[expose] def a₀ : Finset (Fin 8) := {0, 1, 2, 3}

@[expose] def B₀ : Finset (Fin 8) := {0, 1, 4, 5}

@[expose] def π₀ : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7

@[expose] def ind (S : Finset (Fin 8)) : Fin 8 → ZMod 2 := fun z => if z ∈ S then 1 else 0

theorem std_comm : ∀ v : Fin 8 → ZMod 2, ∑ z, v z = 0 →
    ∃ c₁ c₂ e : ZMod 2, ∀ w, v w + v (π₀ w) = c₁ * ind a₀ w + c₂ * ind B₀ w + e := by
  decide +kernel

theorem std_ind_a₀ : ∀ w, ind {0, 2} w + ind {0, 2} (π₀ w) = ind a₀ w := by
  decide +kernel

theorem std_ind_B₀ : ∀ w, ind {0, 4} w + ind {0, 4} (π₀ w) = ind B₀ w := by
  decide +kernel

theorem a₀_B₀_cross : a₀.card = 4 ∧ B₀.card = 4 ∧ (a₀ ∩ B₀).card = 2 := by decide +kernel

theorem exists_std {A : Finset (Fin 8)} (hA : A.card = 4) {π : Equiv.Perm (Fin 8)}
    (hπ : ∀ z, π (π z) = z) (hfix : ∀ z, π z ≠ z) (hpres : ∀ z, π z ∈ A ↔ z ∈ A) :
    ∃ g : Equiv.Perm (Fin 8), Equiv.Perm.sign g = 1 ∧ (∀ z, g z ∈ a₀ ↔ z ∈ A) ∧
      ∀ z, g (π z) = π₀ (g z) := by
  obtain ⟨p₁, hp₁⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
  have hp₂A : π p₁ ∈ A := (hpres p₁).2 hp₁
  obtain ⟨p₃, hp₃A, hp₃⟩ : ∃ p₃ ∈ A, p₃ ∉ ({p₁, π p₁} : Finset (Fin 8)) := by
    by_contra hcon
    push Not at hcon
    have h1 : A ⊆ {p₁, π p₁} := hcon
    have h2 := Finset.card_le_card h1
    have h3 : ({p₁, π p₁} : Finset (Fin 8)).card ≤ 2 := Finset.card_le_two
    omega
  have hp₄A : π p₃ ∈ A := (hpres p₃).2 hp₃A
  obtain ⟨q₁, hq₁⟩ : Aᶜ.Nonempty := Finset.card_pos.mp (by rw [Finset.card_compl]; simp [hA])
  have hq₁A : q₁ ∉ A := Finset.mem_compl.mp hq₁
  have hq₂A : π q₁ ∉ A := fun h => hq₁A ((hpres q₁).1 h)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp₃
  obtain ⟨hp₃1, hp₃2⟩ := hp₃
  have n12 : p₁ ≠ π p₁ := fun h => hfix p₁ h.symm
  have n34 : p₃ ≠ π p₃ := fun h => hfix p₃ h.symm
  have n56 : q₁ ≠ π q₁ := fun h => hfix q₁ h.symm
  have n14 : p₁ ≠ π p₃ := by
    intro h
    apply hp₃2
    calc p₃ = π (π p₃) := (hπ p₃).symm
      _ = π p₁ := by rw [← h]
  have n24 : π p₁ ≠ π p₃ := fun h => hp₃1 (π.injective h).symm
  have hneA : ∀ x y : Fin 8, x ∈ A → y ∉ A → x ≠ y := fun x y hx hy h => hy (h ▸ hx)
  have inj : Function.Injective ![p₁, π p₁, p₃, π p₃, q₁, π q₁] := by
    intro i j hij
    have n15 := hneA _ _ hp₁ hq₁A
    have n16 := hneA _ _ hp₁ hq₂A
    have n25 := hneA _ _ hp₂A hq₁A
    have n26 := hneA _ _ hp₂A hq₂A
    have n35 := hneA _ _ hp₃A hq₁A
    have n36 := hneA _ _ hp₃A hq₂A
    have n45 := hneA _ _ hp₄A hq₁A
    have n46 := hneA _ _ hp₄A hq₂A
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first
      | exact absurd hij ‹_›
      | exact absurd hij.symm ‹_›
  have injy : Function.Injective ![(0 : Fin 8), 1, 2, 3, 4, 5] := by decide
  obtain ⟨g, hg, hgx⟩ := exists_even_perm_of_emb (le_refl 6) ⟨_, inj⟩ ⟨_, injy⟩
  have g0 : g p₁ = 0 := hgx 0
  have g1 : g (π p₁) = 1 := hgx 1
  have g2 : g p₃ = 2 := hgx 2
  have g3 : g (π p₃) = 3 := hgx 3
  have g4 : g q₁ = 4 := hgx 4
  have g5 : g (π q₁) = 5 := hgx 5
  have hmap : a₀ = A.map g.toEmbedding := by
    refine Finset.eq_of_subset_of_card_le ?_ (by simp [hA, a₀])
    intro w hw
    simp only [a₀, Finset.mem_insert, Finset.mem_singleton] at hw
    rw [Finset.mem_map]
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨p₁, hp₁, g0⟩
    · exact ⟨π p₁, hp₂A, g1⟩
    · exact ⟨p₃, hp₃A, g2⟩
    · exact ⟨π p₃, hp₄A, g3⟩
  have hs0 : g.symm 0 = p₁ := (Equiv.symm_apply_eq g).2 g0.symm
  have hs1 : g.symm 1 = π p₁ := (Equiv.symm_apply_eq g).2 g1.symm
  have hs2 : g.symm 2 = p₃ := (Equiv.symm_apply_eq g).2 g2.symm
  have hs3 : g.symm 3 = π p₃ := (Equiv.symm_apply_eq g).2 g3.symm
  have hs4 : g.symm 4 = q₁ := (Equiv.symm_apply_eq g).2 g4.symm
  have hs5 : g.symm 5 = π q₁ := (Equiv.symm_apply_eq g).2 g5.symm
  set f : Fin 8 → Fin 8 := fun w => g (π (g.symm w)) with hf
  have f0 : f 0 = 1 := by simp only [hf, hs0]; exact g1
  have f1 : f 1 = 0 := by simp only [hf, hs1, hπ]; exact g0
  have f2 : f 2 = 3 := by simp only [hf, hs2]; exact g3
  have f3 : f 3 = 2 := by simp only [hf, hs3, hπ]; exact g2
  have f4 : f 4 = 5 := by simp only [hf, hs4]; exact g5
  have f5 : f 5 = 4 := by simp only [hf, hs5, hπ]; exact g4
  have fff : ∀ w, f (f w) = w := by
    intro w
    simp only [hf, Equiv.symm_apply_apply, hπ, Equiv.apply_symm_apply]
  have ffix : ∀ w, f w ≠ w := by
    intro w h
    simp only [hf] at h
    have h1 : π (g.symm w) = g.symm w := by
      apply g.injective
      rw [h, Equiv.apply_symm_apply]
    exact hfix _ h1
  have hlt : ∀ k : Fin 8, k.val < 6 → (f k).val < 6 := by
    intro k hk
    fin_cases k
    · simp [f0]
    · simp [f1]
    · simp [f2]
    · simp [f3]
    · simp [f4]
    · simp [f5]
    · simp at hk
    · simp at hk
  have f6 : f 6 = 7 := by
    have h1 : 6 ≤ (f 6).val := by
      by_contra hcon
      push Not at hcon
      have := hlt (f 6) hcon
      rw [fff 6] at this
      simp at this
    have h2 : (f 6).val ≠ 6 := fun h => ffix 6 (Fin.ext (by simpa using h))
    have h3 : (f 6).val < 8 := (f 6).isLt
    have h4 : (f 6).val = 7 := by omega
    exact Fin.ext (by simpa using h4)
  have f7 : f 7 = 6 := by
    have h1 : 6 ≤ (f 7).val := by
      by_contra hcon
      push Not at hcon
      have := hlt (f 7) hcon
      rw [fff 7] at this
      simp at this
    have h2 : (f 7).val ≠ 7 := fun h => ffix 7 (Fin.ext (by simpa using h))
    have h3 : (f 7).val < 8 := (f 7).isLt
    have h4 : (f 7).val = 6 := by omega
    exact Fin.ext (by simpa using h4)
  have hfπ : ∀ w, f w = π₀ w := by
    intro w
    fin_cases w
    · exact f0.trans (by decide +kernel)
    · exact f1.trans (by decide +kernel)
    · exact f2.trans (by decide +kernel)
    · exact f3.trans (by decide +kernel)
    · exact f4.trans (by decide +kernel)
    · exact f5.trans (by decide +kernel)
    · exact f6.trans (by decide +kernel)
    · exact f7.trans (by decide +kernel)
  refine ⟨g, hg, fun z => ?_, fun z => ?_⟩
  · rw [hmap, Finset.mem_map_equiv]
    simp
  · have := hfπ (g z)
    simp only [hf, Equiv.symm_apply_apply] at this
    exact this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

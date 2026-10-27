module

public import CFSG.CharacterTheory.Semidihedral.Principal.NormThreeGram

public section

namespace CFSG.CyclicBlocks

open Finset CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.NormThreeGram

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem integral_norm_three_degree_zero_single (o : X) (d : X → ℤ) (hd : ∀ x, 0 < d x)
    (hdo : d o = 1) (v : X → ℤ) (hvo : v o = 1) (hnorm : ∑ x, v x ^ 2 = 3)
    (hdeg : ∑ x, d x * v x = 0) :
    ∃ a : X, a ≠ o ∧ ∃ b : X, b ≠ o ∧ b ≠ a ∧ ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
      v = Pi.single o 1 + δ • Pi.single a 1 - δ • Pi.single b 1 ∧
      d b = d a + δ ∧ 0 < d a + δ ∧ ∀ x, v x ≠ 0 ↔ x = o ∨ x = a ∨ x = b := by
  let w : X → ℤ := fun x => if x = o then 0 else v x
  have hwo : w o = 0 := by simp [w]
  have hwv : ∀ x, x ≠ o → w x = v x := fun x hx => by simp [w, hx]
  have hsq : ∀ x, v x * v x = w x * w x + (Pi.single o (1 : ℤ) : X → ℤ) x := by
    intro x
    by_cases hx : x = o
    · subst hx
      simp [hwo, hvo]
    · simp [hwv x hx, hx]
  have hwnorm : ∑ x, w x * w x = 2 := by
    have h : ∑ x, v x * v x = ∑ x, w x * w x + 1 := by
      rw [Finset.sum_congr rfl fun x _ => hsq x, Finset.sum_add_distrib, Finset.sum_pi_single']
      simp
    have h3 : ∑ x, v x * v x = 3 := by
      rw [← hnorm]
      simp only [sq]
    omega
  have hdsplit : ∀ x, d x * v x = d x * w x + d x * (Pi.single o (1 : ℤ) : X → ℤ) x := by
    intro x
    by_cases hx : x = o
    · subst hx
      simp [hwo, hvo]
    · simp [hwv x hx, hx]
  have hwdeg : ∑ x, d x * w x = -1 := by
    rw [Finset.sum_congr rfl fun x _ => hdsplit x, Finset.sum_add_distrib] at hdeg
    have h' : ∑ x, d x * (Pi.single o (1 : ℤ) : X → ℤ) x = 1 := by
      rw [Fintype.sum_eq_single o fun x hx => by simp [hx], Pi.single_eq_same, mul_one, hdo]
    omega
  have hvals : ∀ x, w x = -1 ∨ w x = 0 ∨ w x = 1 := by
    intro x
    apply int_cases_of_mul_self_le_two
    rw [← hwnorm]
    exact Finset.single_le_sum (f := fun y => w y * w y) (fun y _ => mul_self_nonneg (w y))
      (Finset.mem_univ x)
  have hcard := support_card_of_norm_two w hvals hwnorm
  obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hcard
  have hmem : ∀ x, w x ≠ 0 ↔ x = a ∨ x = b := by
    intro x
    have h := congrArg (fun s : Finset X => x ∈ s) hS
    simpa using h
  have hwa : w a ≠ 0 := (hmem a).mpr (Or.inl rfl)
  have hwb : w b ≠ 0 := (hmem b).mpr (Or.inr rfl)
  have hao : a ≠ o := fun h => hwa (h ▸ hwo)
  have hbo : b ≠ o := fun h => hwb (h ▸ hwo)
  have hdeg2 := hwdeg
  rw [sum_mul_of_support_pair d w hab fun x hx => (hmem x).mp hx] at hdeg2
  have hda := hd a
  have hdb := hd b
  obtain ⟨δ, hδ⟩ : ∃ δ, w a = δ := ⟨_, rfl⟩
  have hδsign : δ = 1 ∨ δ = -1 := by
    rcases hvals a with h | h | h
    · exact Or.inr (hδ ▸ h)
    · exact absurd h hwa
    · exact Or.inl (hδ ▸ h)
  rw [hδ] at hdeg2
  have hwbδ : w b = -δ ∧ d b = d a + δ := by
    rcases hvals b with h | h | h
    · rw [h] at hdeg2 ⊢
      rcases hδsign with h' | h' <;> rw [h'] at hdeg2 ⊢ <;> omega
    · exact absurd h hwb
    · rw [h] at hdeg2 ⊢
      rcases hδsign with h' | h' <;> rw [h'] at hdeg2 ⊢ <;> omega
  have hvx : ∀ x, v x = (Pi.single o (1 : ℤ) : X → ℤ) x + δ * (Pi.single a (1 : ℤ) : X → ℤ) x -
      δ * (Pi.single b (1 : ℤ) : X → ℤ) x := by
    intro x
    by_cases hxo : x = o
    · subst hxo
      simp [hvo, hao.symm, hbo.symm]
    · rw [← hwv x hxo]
      by_cases hxa : x = a
      · subst hxa
        simp [hδ, hxo, hab]
      · by_cases hxb : x = b
        · subst hxb
          simp [hwbδ.1, hxo, hxa]
        · have hwx : w x = 0 := by
            by_contra h
            rcases (hmem x).mp h with h' | h'
            · exact hxa h'
            · exact hxb h'
          simp [hwx, hxo, hxa, hxb]
  refine ⟨a, hao, b, hbo, hab.symm, δ, hδsign, funext fun x => by simpa using hvx x, hwbδ.2,
    hwbδ.2 ▸ hd b, fun x => ?_⟩
  rw [hvx x]
  by_cases hxo : x = o
  · subst hxo
    simp [hao.symm, hbo.symm]
  · by_cases hxa : x = a
    · subst hxa
      rcases hδsign with h | h <;> simp [h, hxo, hab]
    · by_cases hxb : x = b
      · subst hxb
        rcases hδsign with h | h <;> simp [h, hxo, hxa]
      · simp [hxo, hxa, hxb]

theorem integral_norm_three_degree_zero_gram_family_of_pos {I : Type*} [Fintype I]
    (hI : 1 ≤ Fintype.card I) (o : X) (d : X → ℤ) (hd : ∀ x, 0 < d x) (hdo : d o = 1)
    (v : I → X → ℤ) (hvo : ∀ i, v i o = 1) (hnorm : ∀ i, ∑ x, v i x ^ 2 = 3)
    (hdeg : ∀ i, ∑ x, d x * v i x = 0)
    (hgram : ∀ i j, i ≠ j → ∑ x, v i x * v j x = 2) :
    ∃ a : X, a ≠ o ∧ ∃ b : I → X, Function.Injective b ∧ (∀ i, b i ≠ o ∧ b i ≠ a) ∧
      ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ ∀ i,
        v i = Pi.single o 1 + δ • Pi.single a 1 - δ • Pi.single (b i) 1 ∧
        d (b i) = d a + δ ∧ 0 < d a + δ ∧
        ∀ x, v i x ≠ 0 ↔ x = o ∨ x = a ∨ x = b i := by
  rcases Nat.lt_or_ge 1 (Fintype.card I) with h2 | h1
  · exact integral_norm_three_degree_zero_gram_family_common_coordinate h2 o d hd hdo v hvo hnorm
      hdeg hgram
  · obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp (le_antisymm h1 hI)
    obtain ⟨a, hao, b, hbo, hba, δ, hδ, hv, hdb, hpos, hsupp⟩ :=
      integral_norm_three_degree_zero_single o d hd hdo (v i₀) (hvo i₀) (hnorm i₀) (hdeg i₀)
    refine ⟨a, hao, fun _ => b, fun i j _ => (hi₀ i).trans (hi₀ j).symm, fun _ => ⟨hbo, hba⟩, δ,
      hδ, fun i => ?_⟩
    rw [hi₀ i]
    exact ⟨hv, hdb, hpos, hsupp⟩

end CFSG.CyclicBlocks

module

public import Mathlib.Algebra.Polynomial.Roots

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

variable {K : Type} [Field K] {E : Type} [Group E]

private theorem map_one_of_mul {χ : E → K} (hmul : ∀ X Y, χ (X * Y) = χ X * χ Y)
    (h3 : ∀ X, χ X ^ 3 = 1) : χ 1 = 1 := by
  have h0 : χ 1 ≠ 0 := fun h0 => by
    have := h3 1
    rw [h0] at this
    norm_num at this
  have e := hmul 1 1
  rw [one_mul] at e
  have e' : χ 1 * (χ 1 - 1) = 0 := by rw [mul_sub, ← e, mul_one, sub_self]
  rcases mul_eq_zero.1 e' with h | h
  · exact absurd h h0
  · exact sub_eq_zero.1 h

private theorem map_mul_inv_of_eq {χ : E → K} (hmul : ∀ X Y, χ (X * Y) = χ X * χ Y)
    (h3 : ∀ X, χ X ^ 3 = 1) {X Y : E} (h : χ X = χ Y) : χ (X * Y⁻¹) = 1 := by
  rw [hmul, h, ← hmul, mul_inv_cancel, map_one_of_mul hmul h3]

theorem exists_common_trivial [Finite E] {φ ψ : E → K} (hφ : ∀ X Y, φ (X * Y) = φ X * φ Y)
    (hψ : ∀ X Y, ψ (X * Y) = ψ X * ψ Y) (hφ3 : ∀ X, φ X ^ 3 = 1) (hψ3 : ∀ X, ψ X ^ 3 = 1)
    (hcard : 10 ≤ Nat.card E) : ∃ X : E, X ≠ 1 ∧ φ X = 1 ∧ ψ X = 1 := by
  classical
  by_contra hne
  push Not at hne
  set S : Finset K := (Polynomial.nthRoots 3 (1 : K)).toFinset with hSdef
  have hS : S.card ≤ 3 := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)
  have hmem : ∀ {u : K}, u ^ 3 = 1 → u ∈ S := fun hu => by
    rw [hSdef, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
    exact hu
  let F : E → ↥S × ↥S := fun X => (⟨φ X, hmem (hφ3 X)⟩, ⟨ψ X, hmem (hψ3 X)⟩)
  have hF : Function.Injective F := by
    intro X Y hXY
    have h1 : φ X = φ Y := congrArg (fun z : ↥S × ↥S => ((z.1 : ↥S) : K)) hXY
    have h2 : ψ X = ψ Y := congrArg (fun z : ↥S × ↥S => ((z.2 : ↥S) : K)) hXY
    by_contra hXY'
    exact hne (X * Y⁻¹) (fun h => hXY' (mul_inv_eq_one.1 h)) (map_mul_inv_of_eq hφ hφ3 h1)
      (map_mul_inv_of_eq hψ hψ3 h2)
  have hle : Nat.card E ≤ 9 := calc
    Nat.card E ≤ Nat.card (↥S × ↥S) := Nat.card_le_card_of_injective F hF
    _ = S.card * S.card := by simp [Nat.card_prod]
    _ ≤ 3 * 3 := Nat.mul_le_mul hS hS
    _ = 9 := by norm_num
  omega

variable {n : ℕ}

omit [Group E] in
private theorem card_eq_four {χ : Fin n → E → K} {Z : E} {w x y z : Fin n}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hw : χ w Z = 1) (hx : χ x Z = 1) (hy : χ y Z = 1) (hz : χ z Z = 1)
    (hrest : ∀ l, χ l Z = 1 → l = w ∨ l = x ∨ l = y ∨ l = z) :
    Nat.card {l // χ l Z = 1} = 4 := by
  classical
  have hiff : ∀ l, χ l Z = 1 ↔ l ∈ ({w, x, y, z} : Finset (Fin n)) := fun l => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    refine ⟨hrest l, ?_⟩
    rintro (rfl | rfl | rfl | rfl)
    exacts [hw, hx, hy, hz]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card,
    Fintype.card_coe, Finset.card_insert_of_notMem (by simp [hwx, hwy, hwz]),
    Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]

theorem exists_four_trivial [Finite E] (hn : n = 5 ∨ n = 6) (χ : Fin n → E → K)
    (hmul : ∀ l X Y, χ l (X * Y) = χ l X * χ l Y) (h3 : ∀ l X, χ l X ^ 3 = 1)
    (hcard : 27 ≤ Nat.card E) (hfaith : ∀ X, (∀ l, χ l X = 1) → X = 1) {i j : Fin n}
    (hij : i ≠ j) (hi : ∀ X, χ i X = 1) (hj : ∀ X, χ j X = 1) :
    ∃ X : E, X ≠ 1 ∧ Nat.card {l // χ l X = 1} = 4 := by
  classical
  have hcom : ∀ a b, ∃ X : E, X ≠ 1 ∧ χ a X = 1 ∧ χ b X = 1 := fun a b =>
    exists_common_trivial (hmul a) (hmul b) (h3 a) (h3 b) (by omega)
  have hne1 : ∀ {X : E} {l : Fin n}, χ l X ≠ 1 → X ≠ 1 := fun hl hX =>
    hl (by rw [hX]; exact map_one_of_mul (hmul _) (h3 _))
  set C : Finset (Fin n) := (Finset.univ.erase i).erase j with hC
  have hCij : ∀ l ∈ C, l ≠ i ∧ l ≠ j := fun l hl => by
    obtain ⟨hlj, hl'⟩ := Finset.mem_erase.1 hl
    exact ⟨(Finset.mem_erase.1 hl').1, hlj⟩
  have hcov : ∀ l, l = i ∨ l = j ∨ l ∈ C := fun l => by
    by_cases hli : l = i
    · exact Or.inl hli
    by_cases hlj : l = j
    · exact Or.inr (Or.inl hlj)
    exact Or.inr (Or.inr (Finset.mem_erase.2 ⟨hlj, Finset.mem_erase.2 ⟨hli, Finset.mem_univ l⟩⟩))
  have hCcard : C.card + 2 = n := by
    rw [hC, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  rcases hn with rfl | rfl
  ·
    obtain ⟨a, b, c, hab, hac, hbc, hCe⟩ := Finset.card_eq_three.1 (by omega : C.card = 3)
    have ha := hCij a (by simp [hCe])
    have hb := hCij b (by simp [hCe])
    have hcov5 : ∀ l, l = i ∨ l = j ∨ l = a ∨ l = b ∨ l = c := fun l => by
      rcases hcov l with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · rw [hCe] at h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        tauto
    obtain ⟨X, hX1, haX, hbX⟩ := hcom a b
    have hcX : χ c X ≠ 1 := fun hcX => hX1 (hfaith X fun l => by
      rcases hcov5 l with rfl | rfl | rfl | rfl | rfl
      exacts [hi X, hj X, haX, hbX, hcX])
    refine ⟨X, hX1, card_eq_four hij ha.1.symm hb.1.symm ha.2.symm hb.2.symm hab (hi X) (hj X)
      haX hbX fun l hl => ?_⟩
    rcases hcov5 l with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · subst h
      exact absurd hl hcX
  ·
    obtain ⟨a, haC⟩ := Finset.card_pos.1 (by omega : 0 < C.card)
    obtain ⟨b, c, d, hbc, hbd, hcd, hCe⟩ := Finset.card_eq_three.1
      (by rw [Finset.card_erase_of_mem haC]; omega : (C.erase a).card = 3)
    obtain ⟨hba, hbC⟩ := Finset.mem_erase.1 (show b ∈ C.erase a by simp [hCe])
    obtain ⟨hca, hcC⟩ := Finset.mem_erase.1 (show c ∈ C.erase a by simp [hCe])
    obtain ⟨hda, hdC⟩ := Finset.mem_erase.1 (show d ∈ C.erase a by simp [hCe])
    have ha := hCij a haC
    have hb := hCij b hbC
    have hc := hCij c hcC
    have hd := hCij d hdC
    have hcov6 : ∀ l, l = i ∨ l = j ∨ l = a ∨ l = b ∨ l = c ∨ l = d := fun l => by
      rcases hcov l with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · by_cases hla : l = a
        · exact Or.inr (Or.inr (Or.inl hla))
        · have h' : l ∈ C.erase a := Finset.mem_erase.2 ⟨hla, h⟩
          rw [hCe] at h'
          simp only [Finset.mem_insert, Finset.mem_singleton] at h'
          tauto
    obtain ⟨X, hX1, haX, hbX⟩ := hcom a b
    obtain ⟨Y, hY1, hcY, hdY⟩ := hcom c d
    have hXcd : ¬ (χ c X = 1 ∧ χ d X = 1) := fun ⟨hcX, hdX⟩ => hX1 (hfaith X fun l => by
      rcases hcov6 l with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [hi X, hj X, haX, hbX, hcX, hdX])
    have hYab : ¬ (χ a Y = 1 ∧ χ b Y = 1) := fun ⟨haY, hbY⟩ => hY1 (hfaith Y fun l => by
      rcases hcov6 l with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [hi Y, hj Y, haY, hbY, hcY, hdY])
    by_cases hX2 : χ c X ≠ 1 ∧ χ d X ≠ 1
    · refine ⟨X, hX1, card_eq_four hij ha.1.symm hb.1.symm ha.2.symm hb.2.symm hba.symm (hi X)
        (hj X) haX hbX fun l hl => ?_⟩
      rcases hcov6 l with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · subst h
        exact absurd hl hX2.1
      · subst h
        exact absurd hl hX2.2
    by_cases hY2 : χ a Y ≠ 1 ∧ χ b Y ≠ 1
    · refine ⟨Y, hY1, card_eq_four hij hc.1.symm hd.1.symm hc.2.symm hd.2.symm hcd (hi Y)
        (hj Y) hcY hdY fun l hl => ?_⟩
      rcases hcov6 l with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · subst h
        exact absurd hl hY2.1
      · subst h
        exact absurd hl hY2.2
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    obtain ⟨p, q, hpq, hpX, hqX⟩ : ∃ p q, ((p = c ∧ q = d) ∨ (p = d ∧ q = c)) ∧ χ p X = 1 ∧
        χ q X ≠ 1 := by
      by_cases hcX : χ c X = 1
      · exact ⟨c, d, Or.inl ⟨rfl, rfl⟩, hcX, fun h => hXcd ⟨hcX, h⟩⟩
      · have hdX : χ d X = 1 := by
          by_contra h
          exact hX2 ⟨hcX, h⟩
        exact ⟨d, c, Or.inr ⟨rfl, rfl⟩, hdX, hcX⟩
    obtain ⟨p', q', hpq', hp'Y, hq'Y⟩ : ∃ p q, ((p = a ∧ q = b) ∨ (p = b ∧ q = a)) ∧ χ p Y = 1 ∧
        χ q Y ≠ 1 := by
      by_cases haY : χ a Y = 1
      · exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, haY, fun h => hYab ⟨haY, h⟩⟩
      · have hbY : χ b Y = 1 := by
          by_contra h
          exact hY2 ⟨haY, h⟩
        exact ⟨b, a, Or.inr ⟨rfl, rfl⟩, hbY, haY⟩
    have hpY : χ p Y = 1 := by rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hqY : χ q Y = 1 := by rcases hpq with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have hp'X : χ p' X = 1 := by rcases hpq' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hq'X : χ q' X = 1 := by rcases hpq' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have hp := (show p ≠ i ∧ p ≠ j by rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [hc, hd])
    have hp' := (show p' ≠ i ∧ p' ≠ j by rcases hpq' with ⟨rfl, -⟩ | ⟨rfl, -⟩; exacts [ha, hb])
    have hp'p : p' ≠ p := by
      rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases hpq' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        first | exact hca.symm | exact hda.symm | exact hbc | exact hbd
    have hcovPQ : ∀ l, l = i ∨ l = j ∨ l = p' ∨ l = q' ∨ l = p ∨ l = q := by
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        intro l <;> rcases hcov6 l with h | h | h | h | h | h <;> simp [h]
    have hqXY : χ q (X * Y) ≠ 1 := by rwa [hmul, hqY, mul_one]
    have hq'XY : χ q' (X * Y) ≠ 1 := by rwa [hmul, hq'X, one_mul]
    refine ⟨X * Y, hne1 hqXY, card_eq_four hij hp'.1.symm hp.1.symm hp'.2.symm hp.2.symm hp'p
      (by rw [hmul, hi, hi, one_mul]) (by rw [hmul, hj, hj, one_mul])
      (by rw [hmul, hp'X, hp'Y, one_mul]) (by rw [hmul, hpX, hpY, one_mul]) fun l hl => ?_⟩
    rcases hcovPQ l with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · subst h
      exact absurd hl hq'XY
    · exact Or.inr (Or.inr (Or.inr h))
    · subst h
      exact absurd hl hqXY

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end

module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11_card_le_of_cover [Finite G] {V W : Subgroup G} {k : ℕ} (r : Fin k → G)
    (hr : ∀ i, r i ∈ V) (h : ∀ g ∈ V, ∃ i, (r i)⁻¹ * g ∈ W) :
    Nat.card V ≤ k * Nat.card ↥(V ⊓ W) := by
  classical
  let φ : V → Fin k × ↥(V ⊓ W) := fun g =>
    (Classical.choose (h g.1 g.2),
     ⟨(r (Classical.choose (h g.1 g.2)))⁻¹ * g.1, by
       exact ⟨V.mul_mem (V.inv_mem (hr (Classical.choose (h g.1 g.2)))) g.2,
         Classical.choose_spec (h g.1 g.2)⟩⟩)
  have hφ : Function.Injective φ := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ heq
    simp only [φ, Prod.mk.injEq] at heq
    obtain ⟨hi, hw⟩ := heq
    have hcoe : (r (Classical.choose (h g hg)))⁻¹ * g
        = (r (Classical.choose (h g' hg')))⁻¹ * g' := Subtype.ext_iff.mp hw
    rw [hi] at hcoe
    exact Subtype.ext (mul_left_cancel hcoe)
  calc Nat.card V ≤ Nat.card (Fin k × ↥(V ⊓ W)) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (Fin k) * Nat.card ↥(V ⊓ W) := Nat.card_prod _ _
    _ = k * Nat.card ↥(V ⊓ W) := by rw [Nat.card_fin]

private def Swap (W : Subgroup G) (a x g : G) : Prop :=
  ∃ w ∈ W, g = a * w ∨ g = a * x * w

private def Base (W : Subgroup G) (x g : G) : Prop :=
  ∃ w ∈ W, g = x * w

private theorem x_mul_x_mul {x u v : G} (hx2 : x * x = 1) (hxi : x⁻¹ = x) :
    x * (x * u * x⁻¹ * v) = u * x * v := by
  rw [show x * (x * u * x⁻¹ * v) = (x * x) * (u * x⁻¹ * v) by group, hx2, one_mul, hxi]

private theorem card_le_two_of_cover [Finite G] {V W : Subgroup G} {g1 : G} (hg1 : g1 ∈ V)
    (h : ∀ g ∈ V, g ∈ W ∨ g1⁻¹ * g ∈ W) :
    Nat.card V ≤ 2 * Nat.card ↥(V ⊓ W) := by
  refine sec11_card_le_of_cover (k := 2) (r := fun i : Fin 2 => if i = 0 then 1 else g1) ?_ ?_
  · intro i
    split_ifs
    · exact V.one_mem
    · exact hg1
  · intro g hg
    rcases h g hg with hgW | hgW
    · refine ⟨0, ?_⟩
      rw [if_pos rfl]
      simpa using hgW
    · refine ⟨1, ?_⟩
      rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)]
      simpa using hgW

theorem sec11_type_cases [Finite G] {V W : Subgroup G} {a x : G} (hx2 : x * x = 1)
    (hWx : ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hcov : ∀ g ∈ V, g ∈ W ∨ ∃ w ∈ W, g = a * w ∨ g = x * w ∨ g = a * x * w) :
    V ≤ W ∨
      (∃ g ∈ V, (∃ w ∈ W, g = a * w ∨ g = a * x * w) ∧
        Nat.card V ≤ 2 * Nat.card ↥(V ⊓ W)) ∨
      (∃ g ∈ V, (∃ w ∈ W, g = x * w) ∧ Nat.card V ≤ 2 * Nat.card ↥(V ⊓ W)) ∨
      (∃ g1 ∈ V, ∃ g2 ∈ V, (∃ w ∈ W, g1 = a * w ∨ g1 = a * x * w) ∧ (∃ w ∈ W, g2 = x * w) ∧
        Nat.card V ≤ 4 * Nat.card ↥(V ⊓ W)) := by
  classical
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  by_cases hS : ∃ g ∈ V, Swap W a x g
  · by_cases hB : ∃ g ∈ V, Base W x g
    ·
      obtain ⟨g1, hg1V, hg1swap⟩ := hS
      obtain ⟨g2, hg2V, hg2base⟩ := hB
      let ga : G := if h : ∃ g ∈ V, ∃ w ∈ W, g = a * w then h.choose else 1
      let gx : G := if h : ∃ g ∈ V, ∃ w ∈ W, g = x * w then h.choose else 1
      let gax : G := if h : ∃ g ∈ V, ∃ w ∈ W, g = a * x * w then h.choose else 1
      have hgaV : ga ∈ V := by
        dsimp only [ga]
        split_ifs with h
        · exact h.choose_spec.1
        · exact V.one_mem
      have hgxV : gx ∈ V := by
        dsimp only [gx]
        split_ifs with h
        · exact h.choose_spec.1
        · exact V.one_mem
      have hgaxV : gax ∈ V := by
        dsimp only [gax]
        split_ifs with h
        · exact h.choose_spec.1
        · exact V.one_mem
      let r4 : Fin 4 → G := fun i =>
        if i = 0 then 1 else if i = 1 then ga else if i = 2 then gx else gax
      have hcover : ∀ g ∈ V, ∃ i : Fin 4, (r4 i)⁻¹ * g ∈ W := by
        intro g hg
        rcases hcov g hg with hgW | ⟨w, hw, hgw⟩
        · refine ⟨0, ?_⟩
          dsimp only [r4]
          rw [if_pos rfl]
          simpa using hgW
        · rcases hgw with h | h | h
          · have hP : ∃ g ∈ V, ∃ w ∈ W, g = a * w := ⟨g, hg, w, hw, h⟩
            obtain ⟨-, w0, hw0, hw0eq⟩ := hP.choose_spec
            have hga : ga = a * w0 := by
              dsimp only [ga]; rw [dif_pos hP]; exact hw0eq
            refine ⟨1, ?_⟩
            dsimp only [r4]
            rw [if_neg (show (1 : Fin 4) ≠ 0 by decide), if_pos rfl]
            have he : (a * w0)⁻¹ * (a * w) = w0⁻¹ * w := by group
            rw [hga, h, he]
            exact W.mul_mem (W.inv_mem hw0) hw
          · have hP : ∃ g ∈ V, ∃ w ∈ W, g = x * w := ⟨g, hg, w, hw, h⟩
            obtain ⟨-, w0, hw0, hw0eq⟩ := hP.choose_spec
            have hgx : gx = x * w0 := by
              dsimp only [gx]; rw [dif_pos hP]; exact hw0eq
            refine ⟨2, ?_⟩
            dsimp only [r4]
            rw [if_neg (show (2 : Fin 4) ≠ 0 by decide),
              if_neg (show (2 : Fin 4) ≠ 1 by decide), if_pos rfl]
            have he : (x * w0)⁻¹ * (x * w) = w0⁻¹ * w := by group
            rw [hgx, h, he]
            exact W.mul_mem (W.inv_mem hw0) hw
          · have hP : ∃ g ∈ V, ∃ w ∈ W, g = a * x * w := ⟨g, hg, w, hw, h⟩
            obtain ⟨-, w0, hw0, hw0eq⟩ := hP.choose_spec
            have hgax : gax = a * x * w0 := by
              dsimp only [gax]; rw [dif_pos hP]; exact hw0eq
            refine ⟨3, ?_⟩
            dsimp only [r4]
            rw [if_neg (show (3 : Fin 4) ≠ 0 by decide),
              if_neg (show (3 : Fin 4) ≠ 1 by decide),
              if_neg (show (3 : Fin 4) ≠ 2 by decide)]
            have he : (a * x * w0)⁻¹ * (a * x * w) = w0⁻¹ * w := by group
            rw [hgax, h, he]
            exact W.mul_mem (W.inv_mem hw0) hw
      have hbound : Nat.card V ≤ 4 * Nat.card ↥(V ⊓ W) :=
        sec11_card_le_of_cover (k := 4) (r := r4)
          (by
            intro i
            dsimp only [r4]
            split_ifs
            · exact V.one_mem
            · exact hgaV
            · exact hgxV
            · exact hgaxV)
          hcover
      exact Or.inr (Or.inr (Or.inr ⟨g1, hg1V, g2, hg2V, hg1swap, hg2base, hbound⟩))
    ·
      obtain ⟨g1, hg1V, hg1swap⟩ := hS
      obtain ⟨w1, hw1, hg1form⟩ := hg1swap
      have hcover : ∀ g ∈ V, g ∈ W ∨ g1⁻¹ * g ∈ W := by
        intro g hg
        rcases hcov g hg with hgW | ⟨w, hw, hgw⟩
        · exact Or.inl hgW
        · rcases hgw with h | h | h
          · rcases hg1form with hg1 | hg1
            · refine Or.inr ?_
              have he : g1⁻¹ * g = w1⁻¹ * w := by rw [hg1, h]; group
              rw [he]; exact W.mul_mem (W.inv_mem hw1) hw
            · refine Or.inr ?_
              have he : g1⁻¹ * g = w1⁻¹ * x⁻¹ * w := by rw [hg1, h]; group
              have hbase : Base W x (g1⁻¹ * g) :=
                ⟨x * w1⁻¹ * x⁻¹ * w, W.mul_mem (hWx w1⁻¹ (W.inv_mem hw1)) hw, by
                  rw [he, show w1⁻¹ * x⁻¹ * w = w1⁻¹ * x * w by rw [hxi]]
                  exact (x_mul_x_mul hx2 hxi).symm⟩
              exact absurd ⟨g1⁻¹ * g, V.mul_mem (V.inv_mem hg1V) hg, hbase⟩ hB
          · refine Or.inr ?_
            exact absurd ⟨g, hg, show Base W x g from ⟨w, hw, h⟩⟩ hB
          · rcases hg1form with hg1 | hg1
            · refine Or.inr ?_
              have he : g1⁻¹ * g = w1⁻¹ * x * w := by rw [hg1, h]; group
              have hbase : Base W x (g1⁻¹ * g) :=
                ⟨x * w1⁻¹ * x⁻¹ * w, W.mul_mem (hWx w1⁻¹ (W.inv_mem hw1)) hw, by
                  rw [he]; exact (x_mul_x_mul hx2 hxi).symm⟩
              exact absurd ⟨g1⁻¹ * g, V.mul_mem (V.inv_mem hg1V) hg, hbase⟩ hB
            · refine Or.inr ?_
              have he : g1⁻¹ * g = w1⁻¹ * w := by rw [hg1, h]; group
              rw [he]; exact W.mul_mem (W.inv_mem hw1) hw
      exact Or.inr (Or.inl ⟨g1, hg1V, ⟨w1, hw1, hg1form⟩, card_le_two_of_cover hg1V hcover⟩)
  · by_cases hB : ∃ g ∈ V, Base W x g
    ·
      obtain ⟨g2, hg2V, hg2base⟩ := hB
      obtain ⟨w2, hw2, hg2eq⟩ := hg2base
      have hcover : ∀ g ∈ V, g ∈ W ∨ g2⁻¹ * g ∈ W := by
        intro g hg
        rcases hcov g hg with hgW | ⟨w, hw, hgw⟩
        · exact Or.inl hgW
        · rcases hgw with h | h | h
          · refine Or.inr ?_
            exact absurd ⟨g, hg, show Swap W a x g from ⟨w, hw, Or.inl h⟩⟩ hS
          · refine Or.inr ?_
            have he : g2⁻¹ * g = w2⁻¹ * w := by rw [hg2eq, h]; group
            rw [he]; exact W.mul_mem (W.inv_mem hw2) hw
          · refine Or.inr ?_
            exact absurd ⟨g, hg, show Swap W a x g from ⟨w, hw, Or.inr h⟩⟩ hS
      exact Or.inr (Or.inr (Or.inl ⟨g2, hg2V, ⟨w2, hw2, hg2eq⟩,
        card_le_two_of_cover hg2V hcover⟩))
    ·
      refine Or.inl fun g hg => ?_
      rcases hcov g hg with hgW | ⟨w, hw, hgw⟩
      · exact hgW
      · rcases hgw with h | h | h
        · exact absurd ⟨g, hg, show Swap W a x g from ⟨w, hw, Or.inl h⟩⟩ hS
        · exact absurd ⟨g, hg, show Base W x g from ⟨w, hw, h⟩⟩ hB
        · exact absurd ⟨g, hg, show Swap W a x g from ⟨w, hw, Or.inr h⟩⟩ hS

end CFSG.OddStandard.SmallF3.Omega

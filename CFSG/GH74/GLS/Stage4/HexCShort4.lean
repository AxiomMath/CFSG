module

public import CFSG.GH74.GLS.Stage4.HexCShort3

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem short_coords (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4)
    (E₁ : SL2Pos H R.N root 1) (hC : Hex6Comm root)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) {q : ℕ}
    (hq : RootOrdersG2 root q) (hqodd : Odd q) :
    ∃ x₁ x₅ : E.F → G, (∀ c d, x₁ (c + d) = x₁ c * x₁ d) ∧ Function.Injective x₁ ∧
      (∀ d, x₁ d ∈ root 1) ∧ (∀ b ∈ root 1, ∃ d, x₁ d = b) ∧
      (∀ c d, x₅ (c + d) = x₅ c * x₅ d) ∧ Function.Injective x₅ ∧
      (∀ d, x₅ d ∈ root 5) ∧ (∀ b ∈ root 5, ∃ d, x₅ d = b) ∧
      (∀ c d, (x₅ (c * d))⁻¹ * ⁅phi6 r₁ r₂ E.φ (sl2U c), x₁ d⁆ ∈ Vsub root 2 4) ∧
      (∀ (t : E.Fˣ) d, phi6 r₁ r₂ E.φ (sl2D t) * x₁ d * (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ =
        x₁ ((t : E.F)⁻¹ * d)) ∧
      (∀ (t : E.Fˣ) d, phi6 r₁ r₂ E.φ (sl2D t) * x₅ d * (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ =
        x₅ ((t : E.F) * d)) := by
  classical
  have hcardE : Nat.card E.F = q := by
    rw [← E.toRankOneAt.card_root]; exact hq 4 (by norm_num) (by norm_num)
  have hcardE₁ : Nat.card E₁.F = q := by
    rw [← E₁.toRankOneAt.card_root]; exact hq 1 (by norm_num) (by norm_num)
  have hF2 : (2 : E₁.F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hcardE₁]; exact hqodd)
  have hscal : ∀ t : E.Fˣ, ∃ a : E₁.F, ∀ y : E₁.F,
      phi6 r₁ r₂ E.φ (sl2D t) * E₁.φ (sl2U y) * (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ =
        E₁.φ (sl2U (a * y)) := by
    intro t
    have hU' : ∀ c : E₁.F, ∃ d : E₁.F, phi6 r₁ r₂ E.φ (sl2D t) * E₁.φ (sl2U c) *
        (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ = E₁.φ (sl2U d) := fun c => by
      have := R.invariant 1 (isRoot_of_pos_le (by norm_num) (by norm_num)) _ (phi6_D_mem R E t) _
        (sl2Pos_U_mem E₁ c)
      obtain ⟨d, hd⟩ := (E₁.hU _).1 this
      exact ⟨d, hd.symm⟩
    have hL' : ∀ c : E₁.F, ∃ d : E₁.F, phi6 r₁ r₂ E.φ (sl2D t) * E₁.φ (sl2L c) *
        (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ = E₁.φ (sl2L d) := fun c => by
      have := R.invariant (-1) ⟨by norm_num, by norm_num⟩ _ (phi6_D_mem R E t) _
        (sl2Pos_L_mem E₁ c)
      obtain ⟨d, hd⟩ := (E₁.hL _).1 this
      exact ⟨d, hd.symm⟩
    obtain ⟨a, -, ha, -⟩ := exists_scalar_of_normalizes hF2 E₁.φ E₁.inj R.comm_H E₁.hD
      (phi6_D_mem R E t) hU' hL'
    exact ⟨a, ha⟩
  choose a ha using hscal
  have hBN : ∀ x ∈ root 1, x ∈ Vsub root 2 4 → x = 1 := fun x hx hxN =>
    (rgd2_unique_15 R hx (root 5).one_mem (by simpa using hxN)).1
  have hAN : ∀ x ∈ root 5, x ∈ Vsub root 2 4 → x = 1 := fun x hx hxN =>
    (rgd2_unique_15 R (root 1).one_mem hx (by simpa using hxN)).2
  have hDA : ∀ t : E.Fˣ, ∀ x ∈ root 5, phi6 r₁ r₂ E.φ (sl2D t) * x *
      (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ ∈ root 5 := fun t x hx =>
    R.invariant 5 (isRoot_of_pos_le (by norm_num) (by norm_num)) _ (phi6_D_mem R E t) _ hx
  have hcardA : Nat.card (root 5) = Nat.card E.F := by
    rw [hcardE]; exact hq 5 (by norm_num) (by norm_num)
  obtain ⟨x₁, x₅, h1add, h1inj, h1mem, h1surj, h5add, h5inj, h5mem, h5surj, hrel, hw1, hw5⟩ :=
    (natQuot_short R E hC hO).exists_coords (xB := fun y => E₁.φ (sl2U y))
      (fun y y' => by rw [sl2U_add, map_mul]) (fun y y' h => sl2U_injective (E₁.inj h))
      (fun y => sl2Pos_U_mem E₁ y) (fun b hb => (E₁.hU b).1 hb) a ha
      (by rw [hcardE, hcardE₁]) hcardA hBN hAN hDA
  exact ⟨x₁, x₅, h1add, h1inj, h1mem, h1surj, h5add, h5inj, h5mem, h5surj, hrel, hw1, hw5⟩

end CFSG.GH74.GLS.Stage4.Hex

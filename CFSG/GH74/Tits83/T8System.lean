module

public import CFSG.GH74.Tits83.RelationsC2
public import CFSG.GH74.Tits83.Field
public import CFSG.GH74.Tits83.DesignC
public import CFSG.GH74.Tits83.Glue
public import CFSG.GH74.Tits83.T79
public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

universe u

private theorem leaves_transport {X X' : Type u} [Group X] [Group X'] (D : RankTwoSystem X 8)
    (D' : RankTwoSystem X' 8)
    (φ : win (ofRankTwo D).U 1 8 ≃* win (ofRankTwo D').U 1 8)
    (hφ : ∀ j : ℤ, 1 ≤ j → j ≤ 8 → ∀ x : win (ofRankTwo D).U 1 8,
      ((x : X) ∈ (ofRankTwo D).U j ↔
        ((φ x : win (ofRankTwo D').U 1 8) : X') ∈ (ofRankTwo D').U j)) :
    ∃ ψ : D.U ≃* D'.U, ∀ (i : ℤ), 1 ≤ i → i ≤ 8 → ∀ x : D.U,
      ((x : X) ∈ D.root i ↔ ((ψ x : D'.U) : X') ∈ D'.root i) := by
  refine ⟨(MulEquiv.subgroupCongr (U_eq_win D)).trans
    (φ.trans (MulEquiv.subgroupCongr (U_eq_win D').symm)), fun i h1 h2 x => ?_⟩
  have := hφ i h1 h2 (MulEquiv.subgroupCongr (U_eq_win D) x)
  rw [ofRankTwo_U D h1 h2, ofRankTwo_U D' h1 h2] at this
  exact this

private theorem leaves_case_mixed {X X' : Type u} [Group X] [Group X'] [Finite X] [Finite X']
    (T : TitsSystem X 8) (T' : TitsSystem X' 8) (hN : T.Normalized)
    (hN' : (T'.refl 9).Normalized)
    (h1 : Nat.card (T.U 1) = Nat.card (T'.U 1)) (h8 : Nat.card (T.U 8) = Nat.card (T'.U 8)) :
    False := by
  obtain ⟨c⟩ := exists_octField T hN
  obtain ⟨c'⟩ := exists_octField (T'.refl 9) hN'
  have r1 : T'.U 1 = (T'.refl 9).U 8 := by rw [refl_U]; norm_num
  have r8 : T'.U 8 = (T'.refl 9).U 1 := by rw [refl_U]; norm_num
  rw [r1, c.card_odd odd_one, c'.card_even (even_iff_two_dvd.2 (by norm_num))] at h1
  rw [r8, c.card_even (even_iff_two_dvd.2 (by norm_num)), c'.card_odd odd_one] at h8
  exact c.parity_absurd c' h1 h8

private theorem leaves_case_same {X X' : Type u} [Group X] [Group X'] [Finite X] [Finite X']
    (T : TitsSystem X 8) (T' : TitsSystem X' 8) (hN : T.Normalized) (hN' : T'.Normalized)
    (h1 : Nat.card (T.U 1) = Nat.card (T'.U 1)) :
    ∃ φ : win T.U 1 8 ≃* win T'.U 1 8, ∀ j : ℤ, 1 ≤ j → j ≤ 8 → ∀ x : win T.U 1 8,
      ((x : X) ∈ T.U j ↔ ((φ x : win T'.U 1 8) : X') ∈ T'.U j) := by
  obtain ⟨c⟩ := exists_octCoord T hN
  obtain ⟨c'⟩ := exists_octCoord T' hN'
  haveI := c.finite; haveI := c'.finite
  haveI := c.charP; haveI := c'.charP
  have hK : Nat.card c.K = Nat.card c'.K := by
    rw [← c.card_odd odd_one, ← c'.card_odd odd_one]
    exact h1
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comm c.σ c'.σ c.σ_sq c'.σ_sq hK
  exact core_of_coord T T' c c' θ hθ

private theorem leaves_congr_equiv {X X' : Type u} [Group X] [Group X'] {A B : Subgroup X}
    {A' B' : Subgroup X'} (hA : A = B) (hA' : A' = B') (φ : A ≃* A') (V : ℤ → Subgroup X)
    (V' : ℤ → Subgroup X')
    (h : ∀ j : ℤ, 1 ≤ j → j ≤ 8 → ∀ x : A, ((x : X) ∈ V j ↔ ((φ x : A') : X') ∈ V' j)) :
    ∃ ψ : B ≃* B', ∀ j : ℤ, 1 ≤ j → j ≤ 8 → ∀ x : B,
      ((x : X) ∈ V j ↔ ((ψ x : B') : X') ∈ V' j) := by
  subst hA hA'
  exact ⟨φ, h⟩

private theorem leaves_case_refl {X X' : Type u} [Group X] [Group X'] [Finite X] [Finite X']
    (T : TitsSystem X 8) (T' : TitsSystem X' 8) (hN : (T.refl 9).Normalized)
    (hN' : (T'.refl 9).Normalized) (h8 : Nat.card (T.U 8) = Nat.card (T'.U 8)) :
    ∃ φ : win T.U 1 8 ≃* win T'.U 1 8, ∀ j : ℤ, 1 ≤ j → j ≤ 8 → ∀ x : win T.U 1 8,
      ((x : X) ∈ T.U j ↔ ((φ x : win T'.U 1 8) : X') ∈ T'.U j) := by
  have h1 : Nat.card ((T.refl 9).U 1) = Nat.card ((T'.refl 9).U 1) := by
    rw [refl_U, refl_U]; norm_num; exact h8
  obtain ⟨φ, hφ⟩ := leaves_case_same (T.refl 9) (T'.refl 9) hN hN' h1
  have hw : win (T.refl 9).U 1 8 = win T.U 1 8 := by rw [win_refl]; norm_num
  have hw' : win (T'.refl 9).U 1 8 = win T'.U 1 8 := by rw [win_refl]; norm_num
  refine leaves_congr_equiv hw hw' φ T.U T'.U fun j h1 h2 x => ?_
  have := hφ (9 - j) (by omega) (by omega) x
  rwa [refl_U, refl_U, sub_sub_cancel] at this

theorem tits83T8System : CFSG.Quasithin.Stroth.Tits83T8System := by
  intro X X' _ _ _ _ D D' hcard
  have hc : ∀ j : ℤ, 1 ≤ j → j ≤ 8 →
      Nat.card ((ofRankTwo D).U j) = Nat.card ((ofRankTwo D').U j) := by
    intro j h1 h2
    rw [ofRankTwo_U D h1 h2, ofRankTwo_U D' h1 h2]
    exact hcard j h1 h2
  rcases TitsSystem.normalized_or (ofRankTwo D) (center_win_ne_bot D) with hN | hN <;>
    rcases TitsSystem.normalized_or (ofRankTwo D') (center_win_ne_bot D') with hN' | hN'
  · obtain ⟨φ, hφ⟩ := leaves_case_same _ _ hN hN' (hc 1 le_rfl (by norm_num))
    exact leaves_transport D D' φ hφ
  · exact (leaves_case_mixed _ _ hN hN' (hc 1 le_rfl (by norm_num))
      (hc 8 (by norm_num) le_rfl)).elim
  · exact (leaves_case_mixed _ _ hN' hN (hc 1 le_rfl (by norm_num)).symm
      (hc 8 (by norm_num) le_rfl).symm).elim
  · obtain ⟨φ, hφ⟩ := leaves_case_refl _ _ hN hN' (hc 8 (by norm_num) le_rfl)
    exact leaves_transport D D' φ hφ

end CFSG.GH74.Tits83

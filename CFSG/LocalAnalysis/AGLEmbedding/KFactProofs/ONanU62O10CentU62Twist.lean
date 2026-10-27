module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentU62Type

public section

namespace CFSG.AGLEmbedding.U62O10Cent

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62 CFSG.AGLEmbedding.U62ThreeCent

theorem Ncnt_le (κ : Fin 6 → ZMod 3) (t : ZMod 3) : Ncnt κ t ≤ 6 := by
  have := Fintype.card_subtype_le (fun i : Fin 6 => κ i = t)
  simpa using this

theorem card_ne_Ncnt (κ : Fin 6 → ZMod 3) (u : ZMod 3) :
    Fintype.card {i // κ i ≠ u} = 6 - Ncnt κ u := by
  rw [Fintype.card_subtype_compl]
  simp

theorem rootUnit_sub_ne_zero_iff (u v : ZMod 3) :
    ((rootUnit u : F4ˣ) : F4) - ((rootUnit v : F4ˣ) : F4) ≠ 0 ↔ u ≠ v := by
  rw [sub_ne_zero, Ne, Units.val_inj, rootUnit_injective.eq_iff]

open Classical in
theorem Ncnt_shift (κ : Fin 6 → ZMod 3) (s : ZMod 3) {A : GL (Fin 6) F4}
    (h : (A : Matrix (Fin 6) (Fin 6) F4) * ((dK κ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        ((GeneralLinearGroup.scalar (Fin 6) (rootUnit s) : GL (Fin 6) F4) :
          Matrix (Fin 6) (Fin 6) F4) * ((dK κ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))
    (t : ZMod 3) : Ncnt κ (t - s) = Ncnt κ t := by
  have h' : (A : Matrix (Fin 6) (Fin 6) F4) * Matrix.diagonal (fun i => ((rootUnit (κ i) : F4ˣ) :
      F4)) * ((A⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        Matrix.diagonal fun i => ((rootUnit s : F4ˣ) : F4) * ((rootUnit (κ i) : F4ˣ) : F4) := by
    rw [coe_diagGL6] at h
    rw [h, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
  have key := card_ne_shift h' ((rootUnit t : F4ˣ) : F4)
  have e1 : ∀ i : Fin 6, (((rootUnit s : F4ˣ) : F4) * ((rootUnit (κ i) : F4ˣ) : F4) -
      ((rootUnit t : F4ˣ) : F4) ≠ 0) ↔ κ i ≠ t - s := fun i => by
    rw [← Units.val_mul, ← rootUnit_add, rootUnit_sub_ne_zero_iff, ne_eq, ne_eq,
      eq_sub_iff_add_eq, add_comm]
  have e2 : ∀ i : Fin 6, (((rootUnit (κ i) : F4ˣ) : F4) - ((rootUnit t : F4ˣ) : F4) ≠ 0) ↔
      κ i ≠ t := fun i => rootUnit_sub_ne_zero_iff _ _
  have c1 := Fintype.card_congr (Equiv.subtypeEquivRight e1)
  have c2 := Fintype.card_congr (Equiv.subtypeEquivRight e2)
  rw [c1, c2, card_ne_Ncnt, card_ne_Ncnt] at key
  have := Ncnt_le κ (t - s)
  have := Ncnt_le κ t
  omega

theorem eq_of_shift_invariant (N : ZMod 3 → ℕ) (s : ZMod 3) (hs : s ≠ 0)
    (h : ∀ t, N (t - s) = N t) : N 0 = N 1 ∧ N 1 = N 2 := by
  have hs'' : ∀ u : ZMod 3, u ≠ 0 → u = 1 ∨ u = 2 := by decide
  rcases hs'' s hs with rfl | rfl
  · have e0 := h 0
    have e1 := h 1
    rw [show (0 : ZMod 3) - 1 = 2 from by decide] at e0
    rw [show (1 : ZMod 3) - 1 = 0 from by decide] at e1
    omega
  · have e0 := h 0
    have e1 := h 1
    rw [show (0 : ZMod 3) - 2 = 1 from by decide] at e0
    rw [show (1 : ZMod 3) - 2 = 2 from by decide] at e1
    omega

theorem commute_of_not_constant (κ : Fin 6 → ZMod 3) {y : GU6}
    (hy : (y : GL (Fin 6) F4) = dK κ) (hpat : ¬(Ncnt κ 0 = Ncnt κ 1 ∧ Ncnt κ 1 = Ncnt κ 2))
    (g : GU6) (hg : conj6 g * conj6 y = conj6 y * conj6 g) : g * y = y * g := by
  have h1 : conj6 (g * y * g⁻¹ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg]
    group
  have h2 : g * y * g⁻¹ * y⁻¹ ∈ scalarGU6.range := by
    rw [← ker_conj6]
    exact h1
  obtain ⟨c, hc⟩ := h2
  obtain ⟨s, rfl⟩ := exists_rootUnit c
  have h3 : (g : GL (Fin 6) F4) * (y : GL (Fin 6) F4) * (g : GL (Fin 6) F4)⁻¹ =
      GeneralLinearGroup.scalar (Fin 6) (rootUnit s) * (y : GL (Fin 6) F4) := by
    have := congrArg (fun m : GU6 => (m : GL (Fin 6) F4)) hc
    simp only [coe_scalarGU6, Subgroup.coe_mul, Subgroup.coe_inv] at this
    calc (g : GL (Fin 6) F4) * (y : GL (Fin 6) F4) * (g : GL (Fin 6) F4)⁻¹
        = ((g : GL (Fin 6) F4) * (y : GL (Fin 6) F4) * (g : GL (Fin 6) F4)⁻¹ *
            (y : GL (Fin 6) F4)⁻¹) * (y : GL (Fin 6) F4) := by group
      _ = _ := by rw [← this]
  have h4 := congrArg (fun m : GL (Fin 6) F4 => (m : Matrix (Fin 6) (Fin 6) F4)) h3
  simp only [Units.val_mul, hy] at h4
  have hshift := Ncnt_shift κ s h4
  have hs : s = 0 := by
    by_contra hs0
    apply hpat
    exact eq_of_shift_invariant (Ncnt κ) s hs0 hshift
  subst hs
  rw [rootUnit_zero, map_one, one_mul] at h3
  have h5 : (g : GL (Fin 6) F4) * y = y * g := by
    calc (g : GL (Fin 6) F4) * y = (g * y * (g : GL (Fin 6) F4)⁻¹) * g := by group
      _ = y * g := by rw [h3]
  exact Subtype.ext h5

end CFSG.AGLEmbedding.U62O10Cent

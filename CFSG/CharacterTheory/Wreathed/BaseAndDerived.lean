module

public import CFSG.CharacterTheory.Wreathed.Involutions

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical commutatorElement

@[expose] def baseSubgroup (m : ℕ) : Subgroup (Wreath m) :=
  (RegularWreathProduct.rightHom : Wreath m →* Multiplicative (ZMod 2)).ker

@[simp] theorem element_mem_base (m : ℕ) (a b : ZMod m) (e : ZMod 2) :
    element m a b e ∈ baseSubgroup m ↔ e = 0 := by
  change Multiplicative.ofAdd e = 1 ↔ e = 0
  rfl

@[expose] def baseCoordinateEquiv (m : ℕ) : baseSubgroup m ≃ ZMod m × ZMod m where
  toFun g := ((coordinateEquiv m g.val).1, (coordinateEquiv m g.val).2.1)
  invFun c := ⟨element m c.1 c.2 0, by simp⟩
  left_inv g := by
    apply Subtype.ext
    change element m (coordinateEquiv m g.val).1 (coordinateEquiv m g.val).2.1 0 = g.val
    obtain ⟨⟨a, b, e⟩, hg⟩ := (coordinateEquiv m).symm.surjective g.val
    change element m a b e = g.val at hg
    have he : e = 0 := (element_mem_base m a b e).mp (hg ▸ g.property)
    rw [← hg]
    change element m a b 0 = element m a b e
    rw [he]
  right_inv c := by simp [coordinateEquiv, element]

theorem card_base (m : ℕ) : Nat.card (baseSubgroup m) = m ^ 2 := by
  rw [Nat.card_congr (baseCoordinateEquiv m), Nat.card_prod, Nat.card_zmod]
  ring

theorem base_is_abelian (m : ℕ) : IsMulCommutative (baseSubgroup m) := by
  rw [isMulCommutative_iff]
  intro x y
  apply Subtype.ext
  obtain ⟨⟨a, b⟩, hx⟩ := (baseCoordinateEquiv m).symm.surjective x
  obtain ⟨⟨c, d⟩, hy⟩ := (baseCoordinateEquiv m).symm.surjective y
  rw [← hx, ← hy]
  change element m a b 0 * element m c d 0 = element m c d 0 * element m a b 0
  simp only [element_base_mul, add_comm]

theorem base_index_two (m : ℕ) (hm : 0 < m) : (baseSubgroup m).index = 2 := by
  have hmul := (baseSubgroup m).card_mul_index
  rw [card_base, card_wreath] at hmul
  have hpos : 0 < m ^ 2 := pow_pos hm 2
  nlinarith

@[expose] def antiDiagonalHom (m : ℕ) : Multiplicative (ZMod m) →* Wreath m where
  toFun a := element m (Multiplicative.toAdd a) (-Multiplicative.toAdd a) 0
  map_one' := by simp
  map_mul' a b := by
    change element m (Multiplicative.toAdd a + Multiplicative.toAdd b)
      (-(Multiplicative.toAdd a + Multiplicative.toAdd b)) 0 = _
    rw [element_base_mul, neg_add]

theorem antiDiagonalHom_injective (m : ℕ) : Function.Injective (antiDiagonalHom m) := by
  intro a b h
  have hc := congrArg (fun g : Wreath m => g.left (Multiplicative.ofAdd 0)) h
  simpa [antiDiagonalHom, element] using hc

theorem antiDiagonal_range_eq_zpowers (m : ℕ) :
    (antiDiagonalHom m).range = Subgroup.zpowers (element m 1 (-1) 0) := by
  have hgen : Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod m)) = ⊤ := by
    ext a
    simp only [Subgroup.mem_top, iff_true, Subgroup.mem_zpowers_iff]
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd a)
    refine ⟨k, ?_⟩
    apply Multiplicative.toAdd.injective
    change k • (1 : ZMod m) = Multiplicative.toAdd a
    simpa only [zsmul_eq_mul, mul_one] using hk
  change (antiDiagonalHom m).range =
    Subgroup.zpowers ((antiDiagonalHom m) (Multiplicative.ofAdd (1 : ZMod m)))
  rw [← MonoidHom.map_zpowers, hgen, Subgroup.map_top]

@[expose] def abelianizationProjection (m : ℕ) :
    Wreath m →* Multiplicative (ZMod m) × Multiplicative (ZMod 2) where
  toFun g :=
    let c := coordinateEquiv m g
    (Multiplicative.ofAdd (c.1 + c.2.1), Multiplicative.ofAdd c.2.2)
  map_one' := by
    change (Multiplicative.ofAdd (0 + 0), Multiplicative.ofAdd (0 : ZMod 2)) = 1
    simp
  map_mul' g h := by
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
    obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv m).symm.surjective h
    change (let x := coordinateEquiv m (element m a b e * element m c d f)
      ; (Multiplicative.ofAdd (x.1 + x.2.1), Multiplicative.ofAdd x.2.2)) =
      (Multiplicative.ofAdd (a + b), Multiplicative.ofAdd e) *
        (Multiplicative.ofAdd (c + d), Multiplicative.ofAdd f)
    rcases swap_exponent_cases e with rfl | rfl
    · rw [element_base_mul]
      apply Prod.ext
      · change Multiplicative.ofAdd (a + c + (b + d)) = Multiplicative.ofAdd (a + b + (c + d))
        congr 1
        abel
      · change Multiplicative.ofAdd f = Multiplicative.ofAdd (0 + f)
        rw [zero_add]
    · rw [element_swap_mul]
      apply Prod.ext
      · change Multiplicative.ofAdd (a + d + (b + c)) = Multiplicative.ofAdd (a + b + (c + d))
        congr 1
        abel
      · rfl

theorem abelianizationProjection_ker (m : ℕ) :
    (abelianizationProjection m).ker = (antiDiagonalHom m).range := by
  ext g
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
  change element m a b e ∈ (abelianizationProjection m).ker ↔
    element m a b e ∈ (antiDiagonalHom m).range
  constructor
  · intro h
    change (Multiplicative.ofAdd (a + b), Multiplicative.ofAdd e) = 1 at h
    have hs : a + b = 0 := congrArg
      (fun x : Multiplicative (ZMod m) × Multiplicative (ZMod 2) => Multiplicative.toAdd x.1) h
    have he : e = 0 := congrArg
      (fun x : Multiplicative (ZMod m) × Multiplicative (ZMod 2) => Multiplicative.toAdd x.2) h
    have hb : b = -a := by linear_combination hs
    rw [hb, he]
    exact ⟨Multiplicative.ofAdd a, rfl⟩
  · rintro ⟨c, hc⟩
    change element m (Multiplicative.toAdd c) (-Multiplicative.toAdd c) 0 =
      element m a b e at hc
    rw [← hc]
    change (Multiplicative.ofAdd (Multiplicative.toAdd c + -Multiplicative.toAdd c),
      Multiplicative.ofAdd (0 : ZMod 2)) = 1
    simp

theorem commutator_s_swap (m : ℕ) :
    ⁅element m 1 0 0, element m 0 0 1⁆ = element m 1 (-1) 0 := by
  rw [commutatorElement_def, conjugate_swap_by_base, element_swap_inv, element_swap_mul]
  simp [show (1 + 1 : ZMod 2) = 0 by decide]

theorem derived_eq_zpowers (m : ℕ) :
    commutator (Wreath m) = Subgroup.zpowers (element m 1 (-1) 0) := by
  apply le_antisymm
  · rw [← antiDiagonal_range_eq_zpowers, ← abelianizationProjection_ker,
      commutator_def, Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
    apply Prod.ext
    · simp
    · change Multiplicative.ofAdd _ = (1 : Multiplicative (ZMod 2))
      apply Multiplicative.toAdd.injective
      change (coordinateEquiv m g).2.2 + (coordinateEquiv m h).2.2 +
        -(coordinateEquiv m g).2.2 + -(coordinateEquiv m h).2.2 = 0
      abel
  · rw [Subgroup.zpowers_le, ← commutator_s_swap]
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end CFSG.Wreathed

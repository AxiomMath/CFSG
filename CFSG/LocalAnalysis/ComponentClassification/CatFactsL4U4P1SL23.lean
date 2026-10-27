module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Cent

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup Matrix

abbrev SL23 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

@[expose] def sl23a : SL23 := ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def sl23b : SL23 := ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def sl23Word (w : List Bool) : SL23 := (w.map fun c => if c then sl23a else sl23b).prod

@[expose] def sl23Words : List (List Bool) :=
  [[], [true], [false], [true, true], [true, false], [false, true], [false, false],
    [true, true, false], [true, false, true], [true, false, false], [false, true, true],
    [false, true, false], [false, false, true], [true, true, false, true],
    [true, true, false, false], [true, false, true, true], [true, false, true, false],
    [true, false, false, true], [false, true, true, false], [false, true, false, false],
    [false, false, true, true], [false, false, true, false], [true, true, false, true, false],
    [true, false, true, false, false]]

theorem mem_words : ∀ g : SL23, g ∈ sl23Words.map sl23Word := by
  decide

theorem closure_ab : Subgroup.closure ({sl23a, sl23b} : Set SL23) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp (mem_words g)
  refine list_prod_mem fun y hy => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hy
  cases c
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact subset_closure (Set.mem_insert _ _)

theorem sl23a_pow_three : sl23a ^ 3 = 1 := by decide

theorem sl23b_pow_three : sl23b ^ 3 = 1 := by decide

theorem sl23a_mul_ne : sl23a * sl23b ≠ sl23b * sl23a := by decide

theorem card_sl23 : Nat.card SL23 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem odd_orderOf_of_pow_three {M : Type*} [Monoid M] {g : M} (h : g ^ 3 = 1) :
    Odd (orderOf g) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h) with h1 | h1 <;>
    rw [h1] <;> decide

@[expose] noncomputable def slTwoCongr {R R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) R' where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    ext i j
    simp
  right_inv A := by
    ext i j
    simp
  map_mul' := map_mul _

variable {Y : Type} [Group Y]

theorem nonempty_equiv_sl23 (hY : IsSLTwoOver 3 Y) : Nonempty (Y ≃* SL23) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
  have hc : Fintype.card F = Fintype.card (ZMod 3) := by rw [hF, ZMod.card]
  exact ⟨e.trans (slTwoCongr (FiniteField.ringEquivOfCardEq hc))⟩

theorem closure_odd_eq_top (hY : IsSLTwoOver 3 Y) : closure {y : Y | Odd (orderOf y)} = ⊤ := by
  obtain ⟨e⟩ := nonempty_equiv_sl23 hY
  have h1 : Subgroup.closure ({e.symm sl23a, e.symm sl23b} : Set Y) = ⊤ := by
    rw [← Set.image_pair, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_closure, closure_ab,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact e.symm.surjective
  rw [eq_top_iff, ← h1]
  refine closure_mono ?_
  rintro y (rfl | rfl) <;> rw [Set.mem_ofPred_eq, MulEquiv.orderOf_eq]
  · exact odd_orderOf_of_pow_three sl23a_pow_three
  · exact odd_orderOf_of_pow_three sl23b_pow_three

theorem exists_mul_ne (hY : IsSLTwoOver 3 Y) : ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨e⟩ := nonempty_equiv_sl23 hY
  refine ⟨e.symm sl23a, e.symm sl23b, fun h => sl23a_mul_ne ?_⟩
  have h1 := congrArg e h
  simpa only [map_mul, MulEquiv.apply_symm_apply] using h1

theorem card_eq (hY : IsSLTwoOver 3 Y) : Nat.card Y = 24 := by
  obtain ⟨e⟩ := nonempty_equiv_sl23 hY
  rw [Nat.card_congr e.toEquiv, card_sl23]

theorem le_oddPart {G : Type} [Group G] {X H : Subgroup G} (hX : IsSLTwoOver 3 ↥X)
    (hXH : X ≤ H) : X ≤ Q81.oddPart H := by
  have hmap : (closure {y : ↥X | Odd (orderOf y)}).map X.subtype ≤ Q81.oddPart H := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, hy, rfl⟩
    refine Q81.mem_oddPart (hXH y.2) ?_
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    exact hy
  intro x hx
  refine hmap ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [closure_odd_eq_top hX]
  exact mem_top _

end CFSG.ComponentClassification.HarrisLit.P1

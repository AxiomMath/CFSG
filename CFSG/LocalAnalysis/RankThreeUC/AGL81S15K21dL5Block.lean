module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dL5Tits

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dL5Proof

@[expose] def nb (b : Bool) : ℕ := if b then 0 else 1

@[expose] def bf (c : Bool × Bool × Bool × Bool) : Fin (4 + 1) → ℕ :=
  ![0, nb c.1, nb c.1 + nb c.2.1, nb c.1 + nb c.2.1 + nb c.2.2.1,
    nb c.1 + nb c.2.1 + nb c.2.2.1 + nb c.2.2.2]

theorem bf_lt : ∀ (c : Bool × Bool × Bool × Bool) (i j : Fin (4 + 1)), bf c j < bf c i → j < i := by
  decide

@[expose] def Block (c : Bool × Bool × Bool × Bool) : Subgroup SL5 where
  carrier := {g | (g : Mat5).BlockTriangular (bf c)}
  mul_mem' := by
    intro g h hg hh
    exact Matrix.BlockTriangular.mul hg hh
  one_mem' := Matrix.blockTriangular_one
  inv_mem' := by
    intro g hg
    have h1 : ((g⁻¹ : SL5) : Mat5) * (g : Mat5) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : (g : Mat5) * ((g⁻¹ : SL5) : Mat5) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    letI : Invertible (g : Mat5) := ⟨((g⁻¹ : SL5) : Mat5), h1, h2⟩
    have hinv := Matrix.blockTriangular_inv_of_blockTriangular hg
    rw [Matrix.inv_eq_left_inv h1] at hinv
    exact hinv

theorem mem_Block_iff {c : Bool × Bool × Bool × Bool} {g : SL5} :
    g ∈ Block c ↔ ∀ i j : Fin (4 + 1), bf c j < bf c i → (g : Mat5) i j = 0 :=
  Iff.rfl

theorem upperSub5_le_Block (c : Bool × Bool × Bool × Bool) : upperSub5 ≤ Block c := by
  intro g hg i j hij
  exact hg i j (bf_lt c i j hij)

@[expose] def CLe (c c' : Bool × Bool × Bool × Bool) : Prop :=
  (c.1 = true → c'.1 = true) ∧ (c.2.1 = true → c'.2.1 = true) ∧
    (c.2.2.1 = true → c'.2.2.1 = true) ∧ (c.2.2.2 = true → c'.2.2.2 = true)

instance (c c' : Bool × Bool × Bool × Bool) : Decidable (CLe c c') := by
  unfold CLe
  infer_instance

theorem Block_mono {c c' : Bool × Bool × Bool × Bool} (h : CLe c c') : Block c ≤ Block c' := by
  have key : ∀ c c' : Bool × Bool × Bool × Bool, CLe c c' →
      ∀ i j : Fin (4 + 1), bf c' j < bf c' i → bf c j < bf c i := by
    decide
  intro g hg i j hij
  exact hg (key c c' h i j hij)

@[expose] def tv (a b : Fin (4 + 1)) (h : a ≠ b) : SL5 :=
  Matrix.SpecialLinearGroup.transvection h (1 : ZMod 2)

theorem tv_coe (a b : Fin (4 + 1)) (h : a ≠ b) :
    ((tv a b h : SL5) : Mat5) = 1 + Matrix.single a b 1 := rfl

theorem tv_mem_Block_iff {c : Bool × Bool × Bool × Bool} {a b : Fin (4 + 1)} (h : a ≠ b) :
    tv a b h ∈ Block c ↔ ¬ bf c b < bf c a := by
  rw [mem_Block_iff]
  constructor
  · intro hall hlt
    have := hall a b hlt
    rw [tv_coe, Matrix.add_apply, Matrix.one_apply_ne h] at this
    simp at this
  · intro hn i j hij
    have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    have hne' : ¬ (a = i ∧ b = j) := by
      rintro ⟨rfl, rfl⟩
      exact hn hij
    rw [tv_coe, Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.single_apply_of_ne a b 1 i j hne',
      zero_add]

theorem tv10_mem_iff (c : Bool × Bool × Bool × Bool) :
    tv 1 0 (by decide) ∈ Block c ↔ c.1 = true := by
  rw [tv_mem_Block_iff]
  revert c
  decide

theorem tv21_mem_iff (c : Bool × Bool × Bool × Bool) :
    tv 2 1 (by decide) ∈ Block c ↔ c.2.1 = true := by
  rw [tv_mem_Block_iff]
  revert c
  decide

theorem tv32_mem_iff (c : Bool × Bool × Bool × Bool) :
    tv 3 2 (by decide) ∈ Block c ↔ c.2.2.1 = true := by
  rw [tv_mem_Block_iff]
  revert c
  decide

theorem tv43_mem_iff (c : Bool × Bool × Bool × Bool) :
    tv 4 3 (by decide) ∈ Block c ↔ c.2.2.2 = true := by
  rw [tv_mem_Block_iff]
  revert c
  decide

theorem Block_injective : Function.Injective Block := by
  rintro ⟨c0, c1, c2, c3⟩ ⟨d0, d1, d2, d3⟩ h
  have e0 : tv 1 0 (by decide) ∈ Block (c0, c1, c2, c3) ↔ tv 1 0 (by decide) ∈ Block (d0, d1, d2, d3) := by
    rw [h]
  have e1 : tv 2 1 (by decide) ∈ Block (c0, c1, c2, c3) ↔ tv 2 1 (by decide) ∈ Block (d0, d1, d2, d3) := by
    rw [h]
  have e2 : tv 3 2 (by decide) ∈ Block (c0, c1, c2, c3) ↔ tv 3 2 (by decide) ∈ Block (d0, d1, d2, d3) := by
    rw [h]
  have e3 : tv 4 3 (by decide) ∈ Block (c0, c1, c2, c3) ↔ tv 4 3 (by decide) ∈ Block (d0, d1, d2, d3) := by
    rw [h]
  rw [tv10_mem_iff, tv10_mem_iff] at e0
  rw [tv21_mem_iff, tv21_mem_iff] at e1
  rw [tv32_mem_iff, tv32_mem_iff] at e2
  rw [tv43_mem_iff, tv43_mem_iff] at e3
  have f0 : c0 = d0 := Bool.eq_iff_iff.2 e0
  have f1 : c1 = d1 := Bool.eq_iff_iff.2 e1
  have f2 : c2 = d2 := Bool.eq_iff_iff.2 e2
  have f3 : c3 = d3 := Bool.eq_iff_iff.2 e3
  rw [f0, f1, f2, f3]

theorem range_Block_eq : Set.range Block = {P : Subgroup SL5 | sl5B ≤ P} := by
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro _ ⟨c, rfl⟩
    exact sl5B_le_upperSub5.trans (upperSub5_le_Block c)
  · have h16 : (Set.range Block).ncard = 16 := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ Block_injective, Set.ncard_univ]
      simp [Nat.card_eq_fintype_card]
    rw [h16]
    exact sl5B_overgroups_ncard_le

theorem eq_Block_of_overgroup {D : Subgroup SL5} (h : upperSub5 ≤ D) : ∃ c, D = Block c := by
  have hD : D ∈ Set.range Block := by
    rw [range_Block_eq]
    exact sl5B_le_upperSub5.trans h
  obtain ⟨c, hc⟩ := hD
  exact ⟨c, hc.symm⟩

@[expose] def TS (p q r : Fin (4 + 1)) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : Set SL5 :=
  {tv p q hpq, tv q p hpq.symm, tv p r hpr, tv r p hpr.symm, tv q r hqr, tv r q hqr.symm}

theorem tv_mem_commutator {a e b : Fin (4 + 1)} (hae : a ≠ e) (heb : e ≠ b) (hab : a ≠ b)
    {H : Subgroup SL5} (h1 : tv a e hae ∈ H) (h2 : tv e b heb ∈ H) : tv a b hab ∈ ⁅H, H⁆ := by
  have := Subgroup.commutator_mem_commutator h1 h2
  unfold tv at this ⊢
  rwa [Matrix.SpecialLinearGroup.commutatorElement_transvection hae heb hab, mul_one] at this

theorem commutator_closure_TS (p q r : Fin (4 + 1)) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ⁅Subgroup.closure (TS p q r hpq hpr hqr), Subgroup.closure (TS p q r hpq hpr hqr)⁆ =
      Subgroup.closure (TS p q r hpq hpr hqr) := by
  set H := Subgroup.closure (TS p q r hpq hpr hqr) with hH
  refine le_antisymm (Subgroup.commutator_le.2 fun g1 hg1 g2 hg2 => ?_) ?_
  · rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hg1 hg2) (H.inv_mem hg1)) (H.inv_mem hg2)
  · have m1 : tv p q hpq ∈ H := Subgroup.subset_closure (by simp [TS])
    have m2 : tv q p hpq.symm ∈ H := Subgroup.subset_closure (by simp [TS])
    have m3 : tv p r hpr ∈ H := Subgroup.subset_closure (by simp [TS])
    have m4 : tv r p hpr.symm ∈ H := Subgroup.subset_closure (by simp [TS])
    have m5 : tv q r hqr ∈ H := Subgroup.subset_closure (by simp [TS])
    have m6 : tv r q hqr.symm ∈ H := Subgroup.subset_closure (by simp [TS])
    rw [hH, Subgroup.closure_le]
    intro x hx
    simp only [TS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact tv_mem_commutator hpr hqr.symm hpq m3 m6
    · exact tv_mem_commutator hqr hpr.symm hpq.symm m5 m4
    · exact tv_mem_commutator hpq hqr hpr m1 m5
    · exact tv_mem_commutator hqr.symm hpq.symm hpr.symm m6 m2
    · exact tv_mem_commutator hpq.symm hpr hqr m2 m3
    · exact tv_mem_commutator hpr.symm hpq hqr.symm m4 m1

theorem tv_ne_one {a b : Fin (4 + 1)} (h : a ≠ b) : tv a b h ≠ 1 := by
  intro e
  have h1 := congrArg (fun x : SL5 => (x : Mat5) a b) e
  simp only [tv_coe, Matrix.SpecialLinearGroup.coe_one, Matrix.add_apply, Matrix.one_apply_ne h,
    Matrix.single_apply_same, zero_add] at h1
  exact absurd h1 (by decide)

theorem not_solvable_of_TS {p q r : Fin (4 + 1)} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {D : Subgroup SL5} (hD : ∀ x ∈ TS p q r hpq hpr hqr, x ∈ D) : ¬ Group.IsSolvable ↥D := by
  intro hs
  have hle : Subgroup.closure (TS p q r hpq hpr hqr) ≤ D := (Subgroup.closure_le D).2 hD
  haveI : Group.IsPerfect ↥(Subgroup.closure (TS p q r hpq hpr hqr)) :=
    Subgroup.isPerfect_iff.2 (commutator_closure_TS p q r hpq hpr hqr)
  have hmem : tv p q hpq ∈ Subgroup.closure (TS p q r hpq hpr hqr) :=
    Subgroup.subset_closure (by simp [TS])
  haveI : Nontrivial ↥(Subgroup.closure (TS p q r hpq hpr hqr)) :=
    ⟨⟨⟨tv p q hpq, hmem⟩, 1, fun e => tv_ne_one hpq (congrArg Subtype.val e)⟩⟩
  haveI : Group.IsSolvable ↥(Subgroup.closure (TS p q r hpq hpr hqr)) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable _ ‹_›

theorem TS_le_Block {c : Bool × Bool × Bool × Bool} {p q r : Fin (4 + 1)} (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (h1 : bf c p = bf c q) (h2 : bf c q = bf c r) :
    ∀ x ∈ TS p q r hpq hpr hqr, x ∈ Block c := by
  have h3 : bf c p = bf c r := h1.trans h2
  intro x hx
  simp only [TS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [tv_mem_Block_iff] <;> omega

@[expose] def Adj (c : Bool × Bool × Bool × Bool) : Prop :=
  (c.1 = true ∧ c.2.1 = true) ∨ (c.2.1 = true ∧ c.2.2.1 = true) ∨ (c.2.2.1 = true ∧ c.2.2.2 = true)

instance (c : Bool × Bool × Bool × Bool) : Decidable (Adj c) := by
  unfold Adj
  infer_instance

theorem bf_eq_of_adj : ∀ c : Bool × Bool × Bool × Bool,
    (c.1 = true ∧ c.2.1 = true → bf c 0 = bf c 1 ∧ bf c 1 = bf c 2) ∧
    (c.2.1 = true ∧ c.2.2.1 = true → bf c 1 = bf c 2 ∧ bf c 2 = bf c 3) ∧
    (c.2.2.1 = true ∧ c.2.2.2 = true → bf c 2 = bf c 3 ∧ bf c 3 = bf c 4) := by
  decide

theorem not_solvable_Block {c : Bool × Bool × Bool × Bool} (h : Adj c) :
    ¬ Group.IsSolvable ↥(Block c) := by
  obtain ⟨e1, e2, e3⟩ := bf_eq_of_adj c
  rcases h with h | h | h
  · obtain ⟨a, b⟩ := e1 h
    exact not_solvable_of_TS (p := 0) (q := 1) (r := 2) (by decide) (by decide) (by decide)
      (TS_le_Block _ _ _ a b)
  · obtain ⟨a, b⟩ := e2 h
    exact not_solvable_of_TS (p := 1) (q := 2) (r := 3) (by decide) (by decide) (by decide)
      (TS_le_Block _ _ _ a b)
  · obtain ⟨a, b⟩ := e3 h
    exact not_solvable_of_TS (p := 2) (q := 3) (r := 4) (by decide) (by decide) (by decide)
      (TS_le_Block _ _ _ a b)

@[expose] def good1 : Bool × Bool × Bool × Bool := (true, false, true, false)

@[expose] def good2 : Bool × Bool × Bool × Bool := (true, false, false, true)

@[expose] def good3 : Bool × Bool × Bool × Bool := (false, true, false, true)

theorem adj_or_le : ∀ c : Bool × Bool × Bool × Bool,
    Adj c ∨ CLe c good1 ∨ CLe c good2 ∨ CLe c good3 := by
  decide

theorem exists_good_of_solvable {D : Subgroup SL5} (hU : upperSub5 ≤ D) (hs : Group.IsSolvable ↥D) :
    D ≤ Block good1 ∨ D ≤ Block good2 ∨ D ≤ Block good3 := by
  obtain ⟨c, rfl⟩ := eq_Block_of_overgroup hU
  rcases adj_or_le c with h | h | h | h
  · exact absurd hs (not_solvable_Block h)
  · exact Or.inl (Block_mono h)
  · exact Or.inr (Or.inl (Block_mono h))
  · exact Or.inr (Or.inr (Block_mono h))

end K21dL5Proof

end CFSG.LocalAnalysis.RankThreeUC.S15

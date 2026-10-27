module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.Semidihedral.Local

variable {W A : Type*} [Group W] [CommGroup A] (E : Subgroup W)

@[expose] def rightCosetMul (w : W) :
    Quotient (QuotientGroup.rightRel E) → Quotient (QuotientGroup.rightRel E) :=
  Quotient.map' (· * w) fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using h

theorem rightCosetMul_mk (w a : W) :
    rightCosetMul E w (Quotient.mk _ a) = Quotient.mk _ (a * w) := rfl

theorem rightCosetMul_iterate_mk (w a : W) (k : ℕ) :
    (rightCosetMul E w)^[k] (Quotient.mk _ a) = Quotient.mk _ (a * w ^ k) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, rightCosetMul_mk, ih, mul_assoc, ← pow_succ']

theorem rightCoset_mk_eq_iff (a b : W) :
    (Quotient.mk (QuotientGroup.rightRel E) a = Quotient.mk _ b) ↔ b * a⁻¹ ∈ E := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply]

theorem rightCosetMul_injective (w : W) : Function.Injective (rightCosetMul E w) := by
  refine Function.LeftInverse.injective (g := rightCosetMul E w⁻¹) fun C => ?_
  induction C using Quotient.inductionOn with
  | h a => rw [rightCosetMul_mk, rightCosetMul_mk, mul_inv_cancel_right]

theorem rep_mul_rep_inv_mem (x : Quotient (QuotientGroup.rightRel E) → W)
    (hx : ∀ C, Quotient.mk _ (x C) = C) (w : W) (C : Quotient (QuotientGroup.rightRel E)) :
    x C * w * (x (rightCosetMul E w C))⁻¹ ∈ E := by
  have h : Quotient.mk (QuotientGroup.rightRel E) (x C * w) =
      Quotient.mk _ (x (rightCosetMul E w C)) := by
    rw [hx, ← rightCosetMul_mk, hx]
  have h' := E.inv_mem ((rightCoset_mk_eq_iff E _ _).mp h)
  rwa [mul_inv_rev, inv_inv] at h'

theorem rep_pow_rep_inv_mem (w y : W) (C : Quotient (QuotientGroup.rightRel E))
    (hy : Quotient.mk _ y = C) (k : ℕ) (hk : (rightCosetMul E w)^[k] C = C) :
    y * w ^ k * y⁻¹ ∈ E := by
  have h : Quotient.mk (QuotientGroup.rightRel E) (y * w ^ k) = Quotient.mk _ y := by
    rw [← rightCosetMul_iterate_mk, hy, hk]
  have h' := E.inv_mem ((rightCoset_mk_eq_iff E _ _).mp h)
  rwa [mul_inv_rev, inv_inv] at h'

variable [E.FiniteIndex] (φ : E →* A)

theorem transfer_eq_prod_rightCoset [Fintype (Quotient (QuotientGroup.rightRel E))]
    (x : Quotient (QuotientGroup.rightRel E) → W) (hx : ∀ C, Quotient.mk _ (x C) = C) (w : W) :
    φ.transfer w =
      ∏ C, φ ⟨x C * w * (x (rightCosetMul E w C))⁻¹, rep_mul_rep_inv_mem E x hx w C⟩ := by
  classical
  set e := QuotientGroup.quotientRightRelEquivQuotientLeftRel E with he
  let g : W ⧸ E → W := fun q => (x (e.symm q))⁻¹
  have hg : ∀ q, (g q : W ⧸ E) = q := by
    intro q
    have h1 : e (e.symm q) = q := e.apply_symm_apply q
    rw [← hx (e.symm q)] at h1
    exact h1
  have he_smul : ∀ q : W ⧸ E, e.symm (w⁻¹ • q) = rightCosetMul E w (e.symm q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      change Quotient.mk _ (w⁻¹ * a)⁻¹ = Quotient.mk _ (a⁻¹ * w)
      rw [mul_inv_rev, inv_inv]
  let T₀ : E.LeftTransversal := ⟨Set.range g, Subgroup.isComplement_range_left hg⟩
  rw [MonoidHom.transfer_def φ T₀ w]
  let := E.fintypeQuotientOfFiniteIndex
  dsimp only [Subgroup.leftTransversals.diff]
  refine Fintype.prod_equiv e.symm _ _ fun q => ?_
  apply congrArg φ
  apply Subtype.ext
  change (((T₀.2.leftQuotientEquiv q : Set.range g) : W))⁻¹ *
      (((w • T₀).2.leftQuotientEquiv q : (w • T₀ : E.LeftTransversal).1) : W) =
    x (e.symm q) * w * (x (rightCosetMul E w (e.symm q)))⁻¹
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, Subgroup.IsComplement.leftQuotientEquiv_apply hg,
    Subgroup.IsComplement.leftQuotientEquiv_apply hg, smul_eq_mul]
  change (x (e.symm q))⁻¹⁻¹ * (w * (x (e.symm (w⁻¹ • q)))⁻¹) =
    x (e.symm q) * w * (x (rightCosetMul E w (e.symm q)))⁻¹
  rw [he_smul, inv_inv, mul_assoc]

section Orbits

variable {E} [Fintype (Quotient (QuotientGroup.rightRel E))]

omit [E.FiniteIndex] in
theorem exists_orbit_data (w : W) (R : Finset (Quotient (QuotientGroup.rightRel E)))
    (hR : ∀ C, ∃! C₀, C₀ ∈ R ∧ ∃ k : ℕ, (rightCosetMul E w)^[k] C₀ = C) :
    ∃ (ρ : Quotient (QuotientGroup.rightRel E) → Quotient (QuotientGroup.rightRel E))
      (κ : Quotient (QuotientGroup.rightRel E) → ℕ),
      (∀ C, ρ C ∈ R) ∧ (∀ C, κ C < Function.minimalPeriod (rightCosetMul E w) (ρ C)) ∧
      (∀ C, (rightCosetMul E w)^[κ C] (ρ C) = C) ∧
      (∀ C C₀ (j : ℕ), C₀ ∈ R → (rightCosetMul E w)^[j] C₀ = C → ρ C = C₀) ∧
      (∀ C (j : ℕ), j < Function.minimalPeriod (rightCosetMul E w) (ρ C) →
        (rightCosetMul E w)^[j] (ρ C) = C → κ C = j) := by
  set f := rightCosetMul E w with hf
  have hpos : ∀ C, 0 < Function.minimalPeriod f C := fun C =>
    Function.minimalPeriod_pos_of_mem_periodicPts
      ((rightCosetMul_injective E w).mem_periodicPts C)
  choose ρ hρ using fun C => (hR C).exists
  choose k₀ hk₀ using fun C => (hρ C).2
  refine ⟨ρ, fun C => k₀ C % Function.minimalPeriod f (ρ C), fun C => (hρ C).1,
    fun C => Nat.mod_lt _ (hpos _), fun C => by rw [Function.iterate_mod_minimalPeriod_eq, hk₀],
    fun C C₀ j hC₀ hj => (hR C).unique (hρ C) ⟨hC₀, j, hj⟩, fun C j hj hjC => ?_⟩
  rw [← (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (Nat.mod_lt _ (hpos _)) hj),
    Function.iterate_mod_minimalPeriod_eq, hk₀, hjC]

variable (E)

omit [E.FiniteIndex] in
theorem sum_minimalPeriod_eq_index (w : W) (R : Finset (Quotient (QuotientGroup.rightRel E)))
    (hR : ∀ C, ∃! C₀, C₀ ∈ R ∧ ∃ k : ℕ, (rightCosetMul E w)^[k] C₀ = C) :
    ∑ C ∈ R, Function.minimalPeriod (rightCosetMul E w) C = E.index := by
  classical
  obtain ⟨ρ, κ, hρR, hκlt, hκ, hρu, hκu⟩ := exists_orbit_data w R hR
  set f := rightCosetMul E w with hf
  have hcard : E.index = (Finset.univ : Finset (Quotient (QuotientGroup.rightRel E))).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel E)]
    rfl
  rw [hcard, Finset.card_eq_sum_card_fiberwise (f := ρ) (t := R) fun C _ => hρR C]
  refine Finset.sum_congr rfl fun C₀ hC₀ => ?_
  rw [← Finset.card_range (Function.minimalPeriod f C₀)]
  refine Finset.card_nbij' (fun j => f^[j] C₀) κ ?_ ?_ ?_ ?_
  · intro j _
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hρu _ C₀ j hC₀ rfl⟩
  · intro C hC
    rw [Finset.mem_coe, Finset.mem_filter] at hC
    rw [Finset.mem_coe, Finset.mem_range, ← hC.2]
    exact hκlt C
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_range] at hj
    have hρj : ρ (f^[j] C₀) = C₀ := hρu _ C₀ j hC₀ rfl
    have h1 : j < Function.minimalPeriod f (ρ (f^[j] C₀)) := by rw [hρj]; exact hj
    exact hκu (f^[j] C₀) j h1 (by rw [hρj])
  · intro C hC
    rw [Finset.mem_coe, Finset.mem_filter] at hC
    change f^[κ C] C₀ = C
    rw [← hC.2]
    exact hκ C

theorem transfer_eq_prod_orbit (w : W) (R : Finset (Quotient (QuotientGroup.rightRel E)))
    (hR : ∀ C, ∃! C₀, C₀ ∈ R ∧ ∃ k : ℕ, (rightCosetMul E w)^[k] C₀ = C)
    (y : Quotient (QuotientGroup.rightRel E) → W) (hy : ∀ C ∈ R, Quotient.mk _ (y C) = C) :
    φ.transfer w = ∏ C : R,
      φ ⟨y C * w ^ Function.minimalPeriod (rightCosetMul E w) C * (y C)⁻¹,
        rep_pow_rep_inv_mem E w (y C) C (hy C C.2) _ Function.iterate_minimalPeriod⟩ := by
  classical
  obtain ⟨ρ, κ, hρR, hκlt, hκ, hρu, hκu⟩ := exists_orbit_data w R hR
  set f := rightCosetMul E w with hf
  have hpos : ∀ C, 0 < Function.minimalPeriod f C := fun C =>
    Function.minimalPeriod_pos_of_mem_periodicPts
      ((rightCosetMul_injective E w).mem_periodicPts C)
  let x : Quotient (QuotientGroup.rightRel E) → W := fun C => y (ρ C) * w ^ κ C
  have hx : ∀ C, Quotient.mk _ (x C) = C := by
    intro C
    change Quotient.mk _ (y (ρ C) * w ^ κ C) = C
    rw [← rightCosetMul_iterate_mk, hy _ (hρR C), hκ C]
  rw [transfer_eq_prod_rightCoset E φ x hx w]
  have hstep : ∀ C, ρ (f C) = ρ C := fun C =>
    hρu (f C) (ρ C) (κ C + 1) (hρR C) (by rw [Function.iterate_succ_apply', hκ C])
  have hnext : ∀ C, κ C + 1 < Function.minimalPeriod f (ρ C) → κ (f C) = κ C + 1 := by
    intro C hlt
    refine hκu (f C) (κ C + 1) (by rwa [hstep]) ?_
    rw [hstep, Function.iterate_succ_apply', hκ C]
  have hlast : ∀ C, κ C + 1 = Function.minimalPeriod f (ρ C) → f C = ρ C ∧ κ (f C) = 0 := by
    intro C heq
    have hfC : f C = ρ C :=
      calc f C = f (f^[κ C] (ρ C)) := by rw [hκ C]
        _ = f^[κ C + 1] (ρ C) := (Function.iterate_succ_apply' f _ _).symm
        _ = ρ C := by rw [heq, Function.iterate_minimalPeriod]
    refine ⟨hfC, hκu (f C) 0 (by rw [hstep]; exact hpos _) ?_⟩
    rw [hstep, Function.iterate_zero_apply, hfC]
  rw [← Finset.prod_filter_of_ne (p := fun C => κ C + 1 = Function.minimalPeriod f (ρ C))]
  swap
  · intro C _ hne
    by_contra hlt'
    have hlt : κ C + 1 < Function.minimalPeriod f (ρ C) := lt_of_le_of_ne (hκlt C) hlt'
    apply hne
    rw [← map_one φ]
    apply congrArg φ
    apply Subtype.ext
    change y (ρ C) * w ^ κ C * w * (y (ρ (f C)) * w ^ κ (f C))⁻¹ = 1
    rw [hstep, hnext C hlt, pow_succ]
    group
  refine Finset.prod_nbij' (fun C => ⟨ρ C, hρR C⟩)
    (fun C₀ => f^[Function.minimalPeriod f C₀ - 1] C₀) ?_ ?_ ?_ ?_ ?_
  · intro C _
    exact Finset.mem_univ _
  · intro C₀ _
    rw [Finset.mem_filter]
    have hρ0 : ρ (f^[Function.minimalPeriod f C₀ - 1] C₀) = C₀ :=
      hρu _ C₀ _ C₀.2 rfl
    have hlt0 : Function.minimalPeriod f C₀ - 1 <
        Function.minimalPeriod f (ρ (f^[Function.minimalPeriod f C₀ - 1] C₀)) := by
      rw [hρ0]
      exact Nat.sub_lt (hpos _) one_pos
    have hκ0 := hκu _ (Function.minimalPeriod f C₀ - 1) hlt0 (by rw [hρ0])
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hκ0, hρ0]
    exact Nat.sub_add_cancel (hpos _)
  · intro C hC
    rw [Finset.mem_filter] at hC
    change f^[Function.minimalPeriod f (ρ C) - 1] (ρ C) = C
    rw [← hC.2, Nat.add_sub_cancel, hκ C]
  · intro C₀ _
    apply Subtype.ext
    exact hρu _ C₀ _ C₀.2 rfl
  · intro C hC
    rw [Finset.mem_filter] at hC
    apply congrArg φ
    apply Subtype.ext
    obtain ⟨hfC, hκf⟩ := hlast C hC.2
    change y (ρ C) * w ^ κ C * w * (y (ρ (f C)) * w ^ κ (f C))⁻¹ =
      y (ρ C) * w ^ Function.minimalPeriod f (ρ C) * (y (ρ C))⁻¹
    rw [hstep, hκf, pow_zero, mul_one, ← hC.2, pow_succ]
    group

end Orbits

theorem transfer_coset_orbit_formula [Fintype (Quotient (QuotientGroup.rightRel E))] :
    (∀ (x : Quotient (QuotientGroup.rightRel E) → W) (hx : ∀ C, Quotient.mk _ (x C) = C)
        (w : W),
      φ.transfer w =
        ∏ C, φ ⟨x C * w * (x (rightCosetMul E w C))⁻¹, rep_mul_rep_inv_mem E x hx w C⟩) ∧
    ∀ (w : W) (R : Finset (Quotient (QuotientGroup.rightRel E))),
      (∀ C, ∃! C₀, C₀ ∈ R ∧ ∃ k : ℕ, (rightCosetMul E w)^[k] C₀ = C) →
      ∀ (y : Quotient (QuotientGroup.rightRel E) → W) (hy : ∀ C ∈ R, Quotient.mk _ (y C) = C),
        φ.transfer w = ∏ C : R,
          φ ⟨y C * w ^ Function.minimalPeriod (rightCosetMul E w) C * (y C)⁻¹,
            rep_pow_rep_inv_mem E w (y C) C (hy C C.2) _ Function.iterate_minimalPeriod⟩ ∧
        ∑ C ∈ R, Function.minimalPeriod (rightCosetMul E w) C = E.index :=
  ⟨fun x hx w => transfer_eq_prod_rightCoset E φ x hx w, fun w R hR y hy =>
    ⟨transfer_eq_prod_orbit E φ w R hR y hy, sum_minimalPeriod_eq_index E w R hR⟩⟩

end CFSG.Semidihedral.Local

module

public import CFSG.CharacterTheory.Blocks.IrreducibleCharacterBasis
public import CFSG.CharacterTheory.Blocks.RepresentationDecomposition
public import CFSG.CharacterTheory.Blocks.VirtualCharacterRing

public section

open scoped BigOperators Classical

namespace CFSG.SmallDefect

open CFSG.BlockSectionOrthogonality.Helpers

theorem card_conjClass_mul_card_centralizer {G : Type} [Group G] [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier * Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card G := by
  rw [← ConjAct.orbit_eq_carrier_conjClasses, Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

variable {G : Type} [Group G] [Fintype G]

theorem isClassFunction_isConj (y : G) :
    BlocksIsClassFunction (fun g : G => if IsConj g y then (1 : ℂ) else 0) := by
  intro g h
  have hiff : IsConj (h * g * h⁻¹) y ↔ IsConj g y := by
    have hc : IsConj g (h * g * h⁻¹) := isConj_iff.mpr ⟨h, rfl⟩
    exact ⟨fun hy => hc.trans hy, fun hy => hc.symm.trans hy⟩
  simp only [hiff]

theorem card_filter_isConj (y : G) :
    ((Finset.univ.filter fun g : G => IsConj g y).card : ℂ) =
      (Nat.card (ConjClasses.mk y).carrier : ℂ) := by
  congr 1
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
    ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]

theorem sum_isConj_mul {f : G → ℂ} (hf : BlocksIsClassFunction f) (y : G) :
    ∑ g : G, (if IsConj g y then (1 : ℂ) else 0) * f g =
      (Nat.card (ConjClasses.mk y).carrier : ℂ) * f y := by
  rw [← card_filter_isConj, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun g : G => IsConj g y)]
  have h1 : ∀ g ∈ Finset.univ.filter (fun g : G => IsConj g y),
      (if IsConj g y then (1 : ℂ) else 0) * f g = f y := by
    intro g hg
    have hgy := (Finset.mem_filter.mp hg).2
    obtain ⟨c, hc⟩ := isConj_iff.mp hgy.symm
    simp only [hgy, ↓reduceIte, one_mul]
    rw [← hc, hf]
  have h2 : ∀ g ∈ Finset.univ.filter (fun g : G => ¬ IsConj g y),
      (if IsConj g y then (1 : ℂ) else 0) * f g = 0 := by
    intro g hg
    simp only [(Finset.mem_filter.mp hg).2, ↓reduceIte, zero_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const_zero,
    add_zero, nsmul_eq_mul]

theorem sum_irr_mul_conj (x y : G) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, χ x * starRingEnd ℂ (χ y) =
      if IsConj x y then (Nat.card (Subgroup.centralizer ({y} : Set G)) : ℂ) else 0 := by
  set f : G → ℂ := fun g => if IsConj g y then (1 : ℂ) else 0 with hf
  have hexp := congrFun ((irreducible_character_basis G).2.2.2 f (isClassFunction_isConj y)) x
  have hcoef : ∀ χ ∈ (irreducibles_finite G).toFinset, BlocksInnerProduct f χ =
      (Nat.card (ConjClasses.mk y).carrier : ℂ) / Nat.card G * starRingEnd ℂ (χ y) := by
    intro χ hχ
    rw [Set.Finite.mem_toFinset] at hχ
    have hcf : BlocksIsClassFunction (fun g => starRingEnd ℂ (χ g)) := by
      intro g h
      dsimp only
      rw [blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)]
    unfold BlocksInnerProduct
    rw [sum_isConj_mul hcf y, Nat.card_eq_fintype_card]
    ring
  rw [Finset.sum_apply] at hexp
  simp only [Pi.smul_apply, smul_eq_mul] at hexp
  rw [Finset.sum_congr rfl fun χ hχ => by rw [hcoef χ hχ]] at hexp
  have hcardC : (Nat.card (ConjClasses.mk y).carrier : ℂ) ≠ 0 := by
    have := card_conjClass_mul_card_centralizer y
    have hpos : 0 < Nat.card (ConjClasses.mk y).carrier := by
      rcases Nat.eq_zero_or_pos (Nat.card (ConjClasses.mk y).carrier) with h | h
      · rw [h, zero_mul] at this
        exact absurd this.symm Nat.card_pos.ne'
      · exact h
    exact_mod_cast hpos.ne'
  have hrel : (Nat.card (Subgroup.centralizer ({y} : Set G)) : ℂ) *
      ((Nat.card (ConjClasses.mk y).carrier : ℂ) / Nat.card G) = 1 := by
    have h := card_conjClass_mul_card_centralizer y
    have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    rw [← h]
    push_cast
    field_simp
  calc ∑ χ ∈ (irreducibles_finite G).toFinset, χ x * starRingEnd ℂ (χ y)
      = (Nat.card (Subgroup.centralizer ({y} : Set G)) : ℂ) *
          ∑ χ ∈ (irreducibles_finite G).toFinset,
            (Nat.card (ConjClasses.mk y).carrier : ℂ) / Nat.card G * starRingEnd ℂ (χ y) *
              χ x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [← mul_assoc, ← mul_assoc, hrel, one_mul, mul_comm]
    _ = (Nat.card (Subgroup.centralizer ({y} : Set G)) : ℂ) * f x := by rw [← hexp]
    _ = _ := by
        simp only [hf]
        split_ifs <;> simp

omit [Fintype G] in
theorem exists_natCast_restrict {H : Type} [Group H] [Fintype H] (φ : H →* G)
    {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {ψ : H → ℂ} (hψ : ψ ∈ BlocksIrr H) :
    ∃ n : ℕ, BlocksInnerProduct (χ ∘ φ) ψ = n := by
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hχ
  obtain ⟨-, ⟨m, hm, -⟩, hcoef⟩ := complex_representation_character_decomposition (ρ.comp φ)
  refine ⟨m ⟨ψ, hψ⟩, ?_⟩
  have h := hcoef m hm ⟨ψ, hψ⟩
  rw [h]
  rfl

theorem blocksInnerProduct_comm_of_real {f g : G → ℂ} (hf : ∀ x, starRingEnd ℂ (f x) = f x)
    (hg : ∀ x, starRingEnd ℂ (g x) = g x) : BlocksInnerProduct f g = BlocksInnerProduct g f := by
  unfold BlocksInnerProduct
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hf, hg, mul_comm]

theorem blocksInnerProduct_add_left (f g h : G → ℂ) :
    BlocksInnerProduct (f + g) h = BlocksInnerProduct f h + BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  rw [← mul_add, ← Finset.sum_add_distrib]
  simp only [Pi.add_apply, add_mul]

theorem blocksInnerProduct_sub_left (f g h : G → ℂ) :
    BlocksInnerProduct (f - g) h = BlocksInnerProduct f h - BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp only [Pi.sub_apply, sub_mul]

theorem blocksInnerProduct_smul_left (c : ℂ) (f h : G → ℂ) :
    BlocksInnerProduct (c • f) h = c * BlocksInnerProduct f h := by
  unfold BlocksInnerProduct
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem blocksInnerProduct_add_right (f g h : G → ℂ) :
    BlocksInnerProduct f (g + h) = BlocksInnerProduct f g + BlocksInnerProduct f h := by
  unfold BlocksInnerProduct
  rw [← mul_add, ← Finset.sum_add_distrib]
  simp only [Pi.add_apply, map_add, mul_add]

theorem blocksInnerProduct_sub_right (f g h : G → ℂ) :
    BlocksInnerProduct f (g - h) = BlocksInnerProduct f g - BlocksInnerProduct f h := by
  unfold BlocksInnerProduct
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp only [Pi.sub_apply, map_sub, mul_sub]

theorem blocksInnerProduct_smul_right (c : ℂ) (f h : G → ℂ) :
    BlocksInnerProduct f (c • h) = starRingEnd ℂ c * BlocksInnerProduct f h := by
  unfold BlocksInnerProduct
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem blocksInnerProduct_conj_symm (f g : G → ℂ) :
    BlocksInnerProduct g f = starRingEnd ℂ (BlocksInnerProduct f g) := by
  unfold BlocksInnerProduct
  rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem blocksInnerProduct_zero_left (h : G → ℂ) : BlocksInnerProduct (0 : G → ℂ) h = 0 := by
  unfold BlocksInnerProduct
  simp

theorem blocksInnerProduct_zero_right (f : G → ℂ) : BlocksInnerProduct f (0 : G → ℂ) = 0 := by
  unfold BlocksInnerProduct
  simp

theorem blocksInnerProduct_irr {χ ψ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (hψ : ψ ∈ BlocksIrr G) :
    BlocksInnerProduct χ ψ = if χ = ψ then 1 else 0 := by
  have h := blocksInnerProduct_irreducible ⟨χ, hχ⟩ ⟨ψ, hψ⟩
  simpa only [Subtype.mk.injEq] using h

end CFSG.SmallDefect

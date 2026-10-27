module

public import CFSG.CharacterTheory.Blocks.NormOne
public import CFSG.CharacterTheory.Blocks.NormTwo
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Wreathed.AbelianInertiaInduction
public import CFSG.CharacterTheory.Wreathed.CentralSL2.CharacterTools
public import CFSG.CharacterTheory.Wreathed.CentralSL2.InducedStabilizer

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open TwoRankLowerBound.Helpers

section ClassFormula

variable {K : Type} [Group K] [Fintype K]

theorem card_conjugators (g h : K) :
    Nat.card {x : K // x⁻¹ * g * x = h} =
      if IsConj g h then Nat.card (Subgroup.centralizer {g} : Subgroup K) else 0 := by
  by_cases hgh : IsConj g h
  · rw [ite_eq_left hgh]
    obtain ⟨k, hk⟩ := isConj_iff.mp hgh
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1 * k, ?_⟩
        invFun := fun c => ⟨c.1 * k⁻¹, ?_⟩
        left_inv := fun x => Subtype.ext (mul_inv_cancel_right _ _)
        right_inv := fun c => Subtype.ext (inv_mul_cancel_right _ _) }
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hx : x.1⁻¹ * g * x.1 = k * g * k⁻¹ := x.2.trans hk.symm
      calc x.1 * k * g = x.1 * (k * g * k⁻¹) * k := by group
        _ = x.1 * (x.1⁻¹ * g * x.1) * k := by rw [hx]
        _ = g * (x.1 * k) := by group
    · have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
      rw [← hk]
      calc (c.1 * k⁻¹)⁻¹ * g * (c.1 * k⁻¹) = k * (c.1⁻¹ * (g * c.1)) * k⁻¹ := by group
        _ = k * g * k⁻¹ := by rw [← hc]; group
  · rw [ite_eq_right hgh, Nat.card_eq_zero]
    left
    exact ⟨fun x => hgh (isConj_iff.mpr ⟨x.1⁻¹, by rw [inv_inv]; exact x.2⟩)⟩

theorem extendByZero_eq_sum (H : Subgroup K) (ρ : H → ℂ) (y : K) :
    extendByZero H ρ y = ∑ h : H, if (h : K) = y then ρ h else 0 := by
  by_cases hy : y ∈ H
  · rw [extendByZero_of_mem H ρ hy, Finset.sum_eq_single ⟨y, hy⟩]
    · rw [ite_eq_left rfl]
    · intro h _ hne
      rw [ite_eq_right]
      intro h'
      exact hne (Subtype.ext h')
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [extendByZero_of_not_mem H ρ hy]
    symm
    refine Finset.sum_eq_zero fun h _ => ?_
    rw [ite_eq_right]
    rintro rfl
    exact hy h.2

theorem inducedFunction_eq_sum_isConj (H : Subgroup K) (ρ : H → ℂ) (g : K) :
    inducedFunction H ρ g = (Nat.card (Subgroup.centralizer {g} : Subgroup K) : ℂ) /
      Nat.card H * ∑ h : H, if IsConj g (h : K) then ρ h else 0 := by
  rw [inducedFunction_eq_extendByZero]
  simp_rw [extendByZero_eq_sum]
  rw [Finset.sum_comm]
  have hfib : ∀ h : H, (∑ x : K, if (h : K) = x⁻¹ * g * x then ρ h else 0) =
      (if IsConj g (h : K) then (Nat.card (Subgroup.centralizer {g} : Subgroup K) : ℂ) else 0) *
        ρ h := by
    intro h
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter fun x : K => (h : K) = x⁻¹ * g * x).card =
        Nat.card {x : K // x⁻¹ * g * x = h} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext x
      simp [eq_comm]
    rw [hcard, card_conjugators]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun h _ => hfib h, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs <;> ring

end ClassFormula

section AdditiveCharacters

variable {F : Type} [Field F] [Fintype F]

theorem sum_addChar_ne_zero {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∑ t : F, (if t = 0 then 0 else ψ t) = -1 := by
  have h := AddChar.sum_eq_zero_of_ne_one hψ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), AddChar.map_zero_eq_one] at h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), ite_eq_left rfl, zero_add]
  rw [Finset.sum_congr rfl fun t ht => ite_eq_right (Finset.ne_of_mem_erase ht)]
  linear_combination h

theorem exists_addChar_ne_one : ∃ ψ : AddChar F ℂ, ψ ≠ 1 := by
  have hcard : 1 < Fintype.card (AddChar F ℂ) := by
    rw [AddChar.card_eq]
    exact Fintype.one_lt_card
  obtain ⟨ψ, hψ⟩ := Fintype.exists_ne_of_one_lt_card hcard 1
  exact ⟨ψ, hψ⟩

omit [Fintype F] in
theorem addChar_ne_zero (ψ : AddChar F ℂ) (t : F) : ψ t ≠ 0 := by
  intro h
  have h1 := AddChar.map_add_eq_mul ψ t (-t)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

end AdditiveCharacters

section VirtualCharacters

variable {K : Type} [Group K] [Fintype K]

theorem character_mem_blocksVChar {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ K W) : σ.character ∈ BlocksVChar K := by
  obtain ⟨m, μ, hμ⟩ := CFSG.Wreathed.exists_blocksIrr_sum σ
  rw [hμ]
  exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.subset_closure (μ j).2

theorem inducedFunction_mem_blocksVChar (H : Subgroup K) (χ : H →* ℂ) :
    inducedFunction H (fun h => χ h) ∈ BlocksVChar K := by
  obtain ⟨W, _, _, _, τ, hτ⟩ :=
    CFSG.Wreathed.exists_representation_inducedFunction H (monoidHom_mem_blocksIrr χ)
  rw [← hτ]
  exact character_mem_blocksVChar τ

theorem mem_blocksIrr_of_virtual_norm_one {f : K → ℂ} (hf : f ∈ BlocksVChar K)
    (hnorm : BlocksInnerProduct f f = 1) (hdeg : 0 < (f 1).re) : f ∈ BlocksIrr K := by
  obtain ⟨χ, hpos | hneg⟩ := blocksVChar_norm_one_signed_irreducible hf hnorm
  · rw [hpos]
    exact χ.2
  · exfalso
    have h1 := blocksIrr_identity_re_pos χ
    rw [hneg, Pi.neg_apply, Complex.neg_re] at hdeg
    linarith

end VirtualCharacters

end CFSG.Wreathed.CentralSL2

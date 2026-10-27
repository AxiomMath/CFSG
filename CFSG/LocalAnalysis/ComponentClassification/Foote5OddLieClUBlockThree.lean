module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUTools

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.U

theorem ClU.top_le_closure_odd_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (hG : (⊤ : Subgroup G) ≤ Subgroup.closure {g | Odd (orderOf g)}) :
    (⊤ : Subgroup G') ≤ Subgroup.closure {g | Odd (orderOf g)} := by
  intro g' _
  have hle : (Subgroup.closure {g : G | Odd (orderOf g)}).map e.toMonoidHom ≤
      Subgroup.closure {g : G' | Odd (orderOf g)} := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨g, hg, rfl⟩
    refine subset_closure ?_
    change Odd (orderOf (e g))
    rw [MulEquiv.orderOf_eq]
    exact hg
  exact hle ⟨e.symm g', hG (mem_top _), e.apply_symm_apply g'⟩

theorem ClU.sl2_top_le_closure_odd {F : Type*} [Field F] (h3 : (3 : F) = 0) :
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≤
      Subgroup.closure {g | Odd (orderOf g)} := by
  rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  refine Subgroup.subset_closure (show Odd (orderOf _) from ?_)
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  refine Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one ?_)
  rw [pow_three,
    ← Matrix.SpecialLinearGroup.transvection_add, ← Matrix.SpecialLinearGroup.transvection_add,
    show c + (c + c) = 3 * c by ring, h3, zero_mul,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

theorem ClU.uBlockThreeGen : ClU.UBlockThreeGen := by
  intro p f K _ h h3 n x z hxz
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hK := h.card_eq_sq
  have hp : p = 3 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1
    (h3 ▸ dvd_pow_self p (by have := h.one_le; omega))
  have h3K : (3 : K) = 0 := by
    rw [show (3 : K) = ((3 : ℕ) : K) by norm_num, ← hp, CharP.cast_eq_zero]
  have hSU : ∀ k : ℕ, k = 2 →
      (⊤ : Subgroup (StatedSU k (p ^ f) K)) ≤ Subgroup.closure {g | Odd (orderOf g)} := by
    rintro k rfl
    obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
    refine ClU.top_le_closure_odd_of_mulEquiv ((CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
      (CFSG.LieType.Universal.Unitary.equivStatedSU hK 2)) (ClU.sl2_top_le_closure_odd ?_)
    apply (CFSG.LieType.Steinberg.fixedSubfield K p f).subtype.injective
    rw [map_ofNat, map_zero]
    exact h3K
  have hB := ClU.top_le_closure_odd_of_mulEquiv (uBlockEquiv h {x, z})
    (hSU _ (Finset.card_pair hxz))
  intro g hg
  have hle : (Subgroup.closure {b : uBlock p f K {x, z} | Odd (orderOf b)}).map
      (uBlock p f K {x, z}).subtype ≤
      Subgroup.closure {g | g ∈ uBlock p f K {x, z} ∧ Odd (orderOf g)} := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨b, hb, rfl⟩
    exact subset_closure ⟨b.2, by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe]⟩
  exact hle ⟨⟨g, hg⟩, hB (mem_top _), rfl⟩

end CFSG.ComponentClassification.Foote5.OddLieCore

module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDeduce
public import CFSG.RankThree.PartOne.S11c.Sec66PSL2
import CFSG.RankThree.PartOne.S11c.Sec66Glue

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.RankThree.PartOne (centerQuotientConj)
open CFSG.RankThree.PartOne.Sec66T (innerAut fixSub mem_fixSub psl_two_exists_fixSub_equiv)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)

section Coordinate

variable {F : Type} [Field F]

theorem translation_mul_translation (a b : F) :
    translation F a * translation F b = translation F (a + b) := by
  ext x
  cases x with
  | none => rfl
  | some x => simp [Equiv.Perm.mul_apply, add_assoc, add_comm a b]

theorem translation_zero_eq_one : translation F 0 = 1 := by
  ext x
  cases x <;> simp

theorem inversion_mul_inversion : inversion F * inversion F = 1 := by
  ext x
  cases x with
  | none => simp [Equiv.Perm.mul_apply]
  | some x =>
    by_cases hx : x = 0
    · subst hx
      simp [Equiv.Perm.mul_apply]
    · have hx' : -x⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hx)
      simp [Equiv.Perm.mul_apply, inversion_nonzero F x hx, inversion_nonzero F _ hx']

theorem sThree_apply_none : (translation F 1 * inversion F) none = some 1 := by
  simp [Equiv.Perm.mul_apply]

theorem sThree_apply_zero : (translation F 1 * inversion F) (some 0) = none := by
  simp [Equiv.Perm.mul_apply]

theorem sThree_apply_one : (translation F 1 * inversion F) (some 1) = some 0 := by
  simp [Equiv.Perm.mul_apply, inversion_nonzero F 1 one_ne_zero]

theorem sThree_apply_some {x : F} (hx : x ≠ 0) :
    (translation F 1 * inversion F) (some x) = some (-x⁻¹ + 1) := by
  simp [Equiv.Perm.mul_apply, inversion_nonzero F x hx]

theorem sThree_cube : (translation F 1 * inversion F) ^ 3 = 1 := by
  set c := translation F 1 * inversion F with hc
  have h3 : c ^ 3 = c * (c * c) := pow_three c
  ext y
  rw [h3]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  cases y with
  | none => rw [hc, sThree_apply_none, sThree_apply_one, sThree_apply_zero]
  | some x =>
    by_cases hx0 : x = 0
    · subst hx0
      rw [hc, sThree_apply_zero, sThree_apply_none, sThree_apply_one]
    · by_cases hx1 : x = 1
      · subst hx1
        rw [hc, sThree_apply_one, sThree_apply_zero, sThree_apply_none]
      · have hy : -x⁻¹ + 1 ≠ 0 := by
          intro h
          apply hx1
          have : x⁻¹ = 1 := by linear_combination -h
          simpa using this
        have hz : -(-x⁻¹ + 1)⁻¹ + 1 ≠ 0 := by
          intro h
          have h1 : (-x⁻¹ + 1)⁻¹ = 1 := by linear_combination -h
          have h2 : -x⁻¹ + 1 = 1 := by simpa using h1
          apply inv_ne_zero hx0
          linear_combination -h2
        have hx1' : x - 1 ≠ 0 := sub_ne_zero.2 hx1
        have hy' : (-x⁻¹ + 1)⁻¹ = x * (x - 1)⁻¹ := by
          have : -x⁻¹ + 1 = (x - 1) * x⁻¹ := by field_simp; ring
          rw [this, mul_inv, inv_inv, mul_comm]
        have hz' : -(x * (x - 1)⁻¹) + 1 = -(x - 1)⁻¹ := by field_simp; ring
        have hxx : -(-(-x⁻¹ + 1)⁻¹ + 1)⁻¹ + 1 = x := by
          rw [hy', hz', inv_neg, inv_inv]
          ring
        rw [hc, sThree_apply_some hx0, sThree_apply_some hy, sThree_apply_some hz, hxx]

theorem sThree_ne_one : translation F 1 * inversion F ≠ 1 := by
  intro h
  have := sThree_apply_none (F := F)
  rw [h] at this
  simp at this

end Coordinate

section Main

theorem exists_sThree_coordinateG {F : Type} [Field F] [CharP F 2] :
    ∃ t c : ↥(coordinateG F), t ^ 2 = 1 ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ t * c * t⁻¹ = c⁻¹ := by
  have ht : translation F 1 ∈ coordinateG F :=
    Subgroup.subset_closure (Or.inl ⟨1, rfl⟩)
  have hs : inversion F ∈ coordinateG F := Subgroup.subset_closure (Or.inr rfl)
  have htt : translation F 1 * translation F 1 = 1 := by
    rw [translation_mul_translation, one_add_one_eq_two, CharTwo.two_eq_zero]
    exact translation_zero_eq_one
  have htinv : (translation F 1)⁻¹ = translation F 1 := inv_eq_of_mul_eq_one_right htt
  have hsinv : (inversion F)⁻¹ = inversion F := inv_eq_of_mul_eq_one_right inversion_mul_inversion
  refine ⟨⟨translation F 1, ht⟩, ⟨translation F 1 * inversion F, mul_mem ht hs⟩, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (by rw [pow_two]; exact htt)
  · exact Subtype.ext sThree_cube
  · intro h
    exact sThree_ne_one (congrArg Subtype.val h)
  · refine Subtype.ext ?_
    show translation F 1 * (translation F 1 * inversion F) * (translation F 1)⁻¹ =
      (translation F 1 * inversion F)⁻¹
    rw [mul_inv_rev, htinv, hsinv, ← mul_assoc, htt, one_mul]

theorem exists_fixed_sThree_psl_two {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hC : StatedClassicalModel T .PSL 2 2 p) {α : MulAut T} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) :
    ∃ t c : T, α t = t ∧ α c = c ∧ t ^ 2 = 1 ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ t * c * t⁻¹ = c⁻¹ := by
  have hp2 : p ≠ 2 := by omega
  have hf : 1 ≤ p := hp.one_lt.le
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := p) (by rw [← Nat.card_eq_fintype_card, hK])
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp (fun h1 => hαinn (h1 ▸ (innerAut T).one_mem))
  let ψ : T ≃* coordinateG K :=
    (e0.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (pslEquivCoordinateG K)
  obtain ⟨-, k, hkcard, ⟨ε⟩⟩ := psl_two_exists_fixSub_equiv hp hp2 hf hK ψ hαord hαinn
  have hk2 : Nat.card k = 2 := by rw [hkcard, Nat.div_self hp.pos, pow_one]
  have : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype k := Fintype.ofFinite k
  have : CharP ↥k 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hk2)
  obtain ⟨t₀, c₀, ht₀, hc₀, hc₀1, htc₀⟩ := exists_sThree_coordinateG (F := ↥k)
  refine ⟨((ε.symm t₀ : ↥(fixSub α)) : T), ((ε.symm c₀ : ↥(fixSub α)) : T),
    mem_fixSub.1 (ε.symm t₀).2, mem_fixSub.1 (ε.symm c₀).2, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, ht₀, map_one]
    rfl
  · rw [← Subgroup.coe_pow, ← map_pow, hc₀, map_one]
    rfl
  · intro h
    apply hc₀1
    apply ε.symm.injective
    exact Subtype.ext (by simpa using h)
  · have := congrArg (fun y : ↥(fixSub α) => (y : T))
      (show ε.symm t₀ * ε.symm c₀ * (ε.symm t₀)⁻¹ = (ε.symm c₀)⁻¹ by
        rw [← map_mul, ← map_inv, ← map_inv, ← map_mul, htc₀])
    simpa using this

theorem lieOutConcl_psl_two_p {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {p : ℕ} {x : Y}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hxp : x ^ p = 1)
    (hαinn : centerQuotientConj L ⟨x, hx⟩ ∉ innerAut (↥L ⧸ Subgroup.center ↥L))
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 p) : LieOutConcl L x := by
  have hαp := CFSG.RankThree.PartOne.Sec66T.centerQuotientConj_pow hx hxp
  obtain ⟨t, c, htf, hcf, ht, hc, hcne, htc⟩ := exists_fixed_sThree_psl_two hp hp5 h hαp hαinn
  exact lieOutConcl_of_sThree hx hp hp5 hxp (borelMaximal_of_model_psl_two h) htf hcf ht hc hcne
    htc

end Main

end CFSG.AGLEmbedding.LieOut

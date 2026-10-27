module

public import CFSG.GH74.Generic.BProg.B3.S3T5AnPerm
public import CFSG.ClassicalInvolution.Balance.Delta

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T5An

open Equiv Equiv.Perm CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance

theorem conj_mem_map_involutionOddCore {X : Type*} [Group X] {M : Subgroup X} [M.Normal]
    {a : ↥M} {g : X} (hg : g * (a : X) = (a : X) * g) {y : X}
    (hy : y ∈ (involutionOddCore a).map M.subtype) :
    g * y * g⁻¹ ∈ (involutionOddCore a).map M.subtype := by
  obtain ⟨k, hk, rfl⟩ := hy
  have hσa : MulAut.conjNormal g a = a := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, hg, mul_inv_cancel_right]
  have h1 := involutionOddCore_map (MulAut.conjNormal g) a
  rw [hσa] at h1
  refine ⟨MulAut.conjNormal g k, ?_, ?_⟩
  · rw [← h1]
    exact ⟨k, hk, rfl⟩
  · simp [MulAut.conjNormal_apply]

theorem normal_of_alternatingGroup_le {α : Type*} [Fintype α] [DecidableEq α]
    {H : Subgroup (Perm α)} (hA : alternatingGroup α ≤ H) : H.Normal := by
  refine ⟨fun h hh g => ?_⟩
  have hc : g * h * g⁻¹ * h⁻¹ ∈ H := hA (by
    rw [mem_alternatingGroup, map_mul, map_mul, map_mul, map_inv, map_inv, Int.units_inv_eq_self,
      Int.units_inv_eq_self, mul_right_comm (sign g), Int.units_mul_self, one_mul,
      Int.units_mul_self])
  simpa using mul_mem hc hh

theorem odd_card_map_involutionOddCore {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (a : ↥M) : Odd (Nat.card ((involutionOddCore a).map M.subtype)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.card_map_of_injective M.subtype_injective, involutionOddCore,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _), oddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem deltaCore_eq_bot_of_alternatingGroup_le {α : Type*} [Fintype α] [DecidableEq α]
    (hα : ¬ (4 : ℤ) ∣ (Fintype.card α : ℤ) - 3) {H : Subgroup (Perm α)}
    (hA : alternatingGroup α ≤ H) {F : Subgroup ↥H} (hF4 : 4 ≤ Nat.card F)
    (hF2 : ∀ f ∈ F, f * f = 1) : deltaCore F = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHn : H.Normal := normal_of_alternatingGroup_le hA
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hx1' : (x : Perm α) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have h3 : ∀ f ∈ F.map H.subtype, f ≠ 1 → (Finset.univ.filter fun p => f p = p).card = 3 := by
    rintro _ ⟨f, hfF, rfl⟩ hf1
    have hf1' : f ≠ 1 := fun h => hf1 (by rw [h, map_one])
    have hxf : x ∈ involutionOddCore f := mem_deltaCore_iff.1 hx f hfF hf1'
    refine card_fix_eq_three (N := (involutionOddCore f).map H.subtype)
      (odd_card_map_involutionOddCore f) (congrArg Subtype.val (hF2 f hfF)) ?_
      (fun g hg y hy => conj_mem_map_involutionOddCore hg hy) ⟨x, hxf, rfl⟩ hx1'
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.1 (involutionOddCore_le_centralizer f hy))
  have hdvd := int_dvd_card_sub_three h3
  rw [Subgroup.card_map_of_injective H.subtype_injective] at hdvd
  have hp : IsPGroup 2 ↥F := fun g => ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hF2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> simp_all
  have h4 : (4 : ℤ) ∣ (Nat.card F : ℤ) := by
    rw [hk]
    exact_mod_cast (Nat.pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
  exact hα (h4.trans hdvd)

end S3T5An

end CFSG.GH74.Generic.BProg.B3

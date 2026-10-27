module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.MulAutSimple
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.MulAutSimple

open Subgroup
open scoped commutatorElement

variable {U : Type*} [Group U]

theorem inn_ne_bot [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a) : inn U ≠ ⊥ := by
  intro h
  obtain ⟨a, b, hab⟩ := hna
  have h1 : ∀ u : U, u = 1 := by
    intro u
    have hmem : (MulAut.conj u : MulAut U) ∈ inn U := conj_mem_inn u
    rw [h, Subgroup.mem_bot] at hmem
    exact conj_injective ⟨a, b, hab⟩ (hmem.trans (map_one MulAut.conj).symm)
  exact hab (by rw [h1 a, h1 b])

theorem mulAut_complete [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a)
    (α : MulAut (MulAut U)) : ∃ a : MulAut U, α = MulAut.conj a := by
  have hle : ∀ β : MulAut (MulAut U), inn U ≤ (inn U).map β.toMonoidHom := by
    intro β
    haveI : ((inn U).map β.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance β.toMonoidHom β.surjective
    refine inn_le_of_normal hna _ ?_
    intro hbot
    exact inn_ne_bot hna ((Subgroup.map_eq_bot_iff_of_injective (inn U) β.injective).1 hbot)
  have hmap : ∀ (β : MulAut (MulAut U)) (u : U), ∃ v : U, β (MulAut.conj u) = MulAut.conj v := by
    intro β u
    obtain ⟨y, hy, hyu⟩ := hle β.symm (conj_mem_inn u)
    obtain ⟨v, rfl⟩ := hy
    refine ⟨v, ?_⟩
    have h : β.symm (MulAut.conj v) = MulAut.conj u := hyu
    rw [← h]
    exact β.apply_symm_apply _
  choose f hf using hmap α
  have hf_mul : ∀ u v, f (u * v) = f u * f v := by
    intro u v
    apply conj_injective hna
    rw [map_mul, ← hf, ← hf, ← hf, map_mul, map_mul]
  have hf_inj : Function.Injective f := by
    intro u v h
    apply conj_injective hna
    apply α.injective
    rw [hf, hf, h]
  have hf_surj : Function.Surjective f := by
    intro v
    obtain ⟨u, hu⟩ := (hmap α.symm v)
    refine ⟨u, conj_injective hna ?_⟩
    rw [← hf, ← hu]
    exact α.apply_symm_apply _
  let a : MulAut U := MulEquiv.ofBijective (MonoidHom.mk' f hf_mul) ⟨hf_inj, hf_surj⟩
  have ha : ∀ u, a u = f u := fun u => rfl
  have hαc : ∀ u : U, α (MulAut.conj u) = a * MulAut.conj u * a⁻¹ := by
    intro u
    rw [hf, ← ha, mul_conj_mul_inv]
  refine ⟨a, MulEquiv.ext fun x => ?_⟩
  rw [MulAut.conj_apply]
  have hzc : ∀ u : U, (x⁻¹ * (a⁻¹ * α x * a)) * MulAut.conj u *
      (x⁻¹ * (a⁻¹ * α x * a))⁻¹ = MulAut.conj u := by
    intro u
    have h1 : α x * (a * MulAut.conj u * a⁻¹) * (α x)⁻¹ =
        a * (x * MulAut.conj u * x⁻¹) * a⁻¹ := by
      have h := congrArg α (mul_conj_mul_inv x u)
      simp only [map_mul, map_inv, hαc] at h
      rw [h, mul_conj_mul_inv x u]
    calc (x⁻¹ * (a⁻¹ * α x * a)) * MulAut.conj u * (x⁻¹ * (a⁻¹ * α x * a))⁻¹
        = x⁻¹ * a⁻¹ * (α x * (a * MulAut.conj u * a⁻¹) * (α x)⁻¹) * a * x := by group
      _ = x⁻¹ * a⁻¹ * (a * (x * MulAut.conj u * x⁻¹) * a⁻¹) * a * x := by rw [h1]
      _ = MulAut.conj u := by group
  have hz : x⁻¹ * (a⁻¹ * α x * a) ∈ Subgroup.centralizer (inn U : Set (MulAut U)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    exact (mul_inv_eq_iff_eq_mul.mp (hzc u)).symm
  rw [centralizer_inn_eq_bot hna, Subgroup.mem_bot] at hz
  have h2 : a⁻¹ * α x * a = x := (inv_mul_eq_one.mp hz).symm
  calc α x = a * (a⁻¹ * α x * a) * a⁻¹ := by group
    _ = a * x * a⁻¹ := by rw [h2]

theorem index_inn_eq_two [Finite U] [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a)
    (hcard : Nat.card (MulAut U) = 2 * Nat.card U) : (inn U).index = 2 := by
  have h := Subgroup.card_mul_index (inn U)
  rw [natCard_inn hna, hcard, mul_comm 2] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

theorem normal_eq_bot_or_inn_or_top [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a)
    (h2 : (inn U).index = 2) (N : Subgroup (MulAut U)) [N.Normal] :
    N = ⊥ ∨ N = inn U ∨ N = ⊤ := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  have hle : inn U ≤ N := inn_le_of_normal hna N hbot
  have hd : N.index ∣ 2 := h2 ▸ Subgroup.index_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact Or.inr (Subgroup.index_eq_one.1 h)
  · left
    refine le_antisymm ?_ hle
    have hr := Subgroup.relIndex_mul_index hle
    rw [h2, h] at hr
    exact Subgroup.relIndex_eq_one.1 (by omega)

theorem normal_eq_bot_or_index_two_or_top [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a)
    (h2 : (inn U).index = 2) (N : Subgroup (MulAut U)) [N.Normal] :
    N = ⊥ ∨ N.index = 2 ∨ N = ⊤ := by
  rcases normal_eq_bot_or_inn_or_top hna h2 N with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (h ▸ h2))
  · exact Or.inr (Or.inr h)

theorem commutator_eq_inn [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a)
    (h2 : (inn U).index = 2) : commutator (MulAut U) = inn U := by
  apply le_antisymm
  · rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two h2,
      Subgroup.mul_mem_iff_of_index_two h2, Subgroup.mul_mem_iff_of_index_two h2,
      Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
    tauto
  · have h1 : inn U = (⊤ : Subgroup U).map (MulAut.conj : U →* MulAut U) :=
      MonoidHom.range_eq_map _
    have h3 : inn U ≤ ⁅(inn U), (inn U)⁆ := by
      rw [h1]
      conv_lhs => rw [← commutator_eq_top hna, commutator_def]
      rw [Subgroup.map_commutator, ← h1]
    exact h3.trans (Subgroup.commutator_mono le_top le_top)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.MulAutSimple

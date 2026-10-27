module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveComm
public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6

section YSide

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commSub_le_commV (Y : Subgroup (MulAut V)) {y : MulAut V} (hy : y ∈ Y) :
    commSub y ≤ commV Y := by
  rintro w ⟨v, rfl⟩
  exact Subgroup.subset_closure ⟨y, hy, v, rfl⟩

theorem card_le_sixteen_fixSub_of_comm (hV : ∀ v : V, v ^ 2 = 1) (Y : Subgroup (MulAut V))
    {y : MulAut V} (hy : y ∈ Y) (hy5 : y ^ 5 = 1)
    (hU : Nat.card ↥(commV Y) ≤ 2 ^ 4 * Nat.card ↥(commV Y ⊓ fixV Y)) :
    Nat.card V ≤ 2 ^ 4 * Nat.card ↥(fixSub y) := by
  have hNC : commSub y ⊓ (commV Y ⊓ fixV Y) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun u hu => ?_
    have h1 : u ∈ commSub y ⊓ fixSub y := ⟨hu.1, hu.2.2 y hy⟩
    rwa [commSub_inf_fixSub_eq_bot (by decide : Odd 5) hy5 hV, Subgroup.mem_bot] at h1
  have hNU : commSub y ≤ commV Y := commSub_le_commV Y hy
  let f : ↥(commSub y) × ↥(commV Y ⊓ fixV Y) → ↥(commV Y) := fun p =>
    ⟨(p.1 : V) * (p.2 : V), Subgroup.mul_mem _ (hNU p.1.2) p.2.2.1⟩
  have hf : Function.Injective f := by
    rintro ⟨n, c⟩ ⟨n', c'⟩ h
    have h' : (n : V) * (c : V) = (n' : V) * (c' : V) := congrArg Subtype.val h
    have hmem : (n' : V)⁻¹ * n ∈ commSub y ⊓ (commV Y ⊓ fixV Y) := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ n'.2) n.2, ?_⟩
      have : (n' : V)⁻¹ * n = c' * (c : V)⁻¹ := by
        calc (n' : V)⁻¹ * n = (n' : V)⁻¹ * (n * c) * (c : V)⁻¹ := by group
          _ = (n' : V)⁻¹ * (n' * c') * (c : V)⁻¹ := by rw [h']
          _ = c' * (c : V)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ c'.2 (Subgroup.inv_mem _ c.2)
    rw [hNC, Subgroup.mem_bot] at hmem
    have hn : (n : V) = n' := (inv_mul_eq_one.mp hmem).symm
    have hc : (c : V) = c' := by
      rw [← hn] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext hn) (Subtype.ext hc)
  have h1 : Nat.card ↥(commSub y) * Nat.card ↥(commV Y ⊓ fixV Y) ≤ Nat.card ↥(commV Y) := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod] at this
  have hCpos : 0 < Nat.card ↥(commV Y ⊓ fixV Y) := Nat.card_pos
  have h2 : Nat.card ↥(commSub y) ≤ 2 ^ 4 := by
    by_contra hlt
    have hlt' : 2 ^ 4 < Nat.card ↥(commSub y) := Nat.lt_of_not_le hlt
    have := Nat.mul_lt_mul_of_pos_right hlt' hCpos
    omega
  calc Nat.card V = Nat.card ↥(commSub y) * Nat.card ↥(fixSub y) :=
        (card_commSub_mul_card_fixSub y).symm
    _ ≤ 2 ^ 4 * Nat.card ↥(fixSub y) := Nat.mul_le_mul_right _ h2

omit [Finite V] in
theorem card_commV_of_isNatSectionBy {S M : Type*} [Group S] [Group M] (act : S → M → M)
    (Y : Subgroup (MulAut V))
    (h : IsNatSectionBy act Y (commV Y) (commV Y ⊓ fixV Y)) :
    Nat.card ↥(commV Y) = Nat.card ↥(commV Y ⊓ fixV Y) * Nat.card M := by
  obtain ⟨-, θ, β, hβ, hker, -⟩ := h
  have h1 := Subgroup.card_ker_mul_card_of_surjective hβ
  rw [hker] at h1
  have h2 : Nat.card ↥((commV Y ⊓ fixV Y).subgroupOf (commV Y)) = Nat.card ↥(commV Y ⊓ fixV Y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  exact h1.symm

omit [Finite V] in
theorem card_commV_le_sixteen_of_isNatSectionBy {S M : Type*} [Group S] [Group M] (act : S → M → M)
    (Y : Subgroup (MulAut V)) (hM : Nat.card M = 16)
    (h : IsNatSectionBy act Y (commV Y) (commV Y ⊓ fixV Y)) :
    Nat.card ↥(commV Y) ≤ 2 ^ 4 * Nat.card ↥(commV Y ⊓ fixV Y) := by
  rw [card_commV_of_isNatSectionBy act Y h, hM, mul_comm]
  norm_num

end YSide

end CFSG.CGT.PushingUpLit.CGT6M

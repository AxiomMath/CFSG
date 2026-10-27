module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinA7

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS FinGen FinGlue
open scoped Nat

namespace FinAlt

variable {n : ℕ}

theorem disjoint_of_isSwap {σ τ : Perm (Fin n)} (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hc : σ * τ = τ * σ) (hne : σ ≠ τ) : Perm.Disjoint σ τ := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, d, hcd, rfl⟩ := hτ
  rw [disjoint_iff_disjoint_support, support_swap hab, support_swap hcd]
  have key : ∀ x y z : Fin n, x ≠ y → x ≠ z → y ≠ z →
      swap x y * swap x z ≠ swap x z * swap x y := by
    intro x y z hxy hxz hyz h
    have h1 := congrArg (fun π : Perm (Fin n) => π y) h
    simp only [Perm.mul_apply] at h1
    rw [swap_apply_of_ne_of_ne (Ne.symm hxy) hyz, swap_apply_right, swap_apply_left] at h1
    exact hxz h1
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
  have hne' : ¬ (a = c ∧ b = d) ∧ ¬ (a = d ∧ b = c) := by
    refine ⟨fun ⟨h1, h2⟩ => hne (by rw [h1, h2]), fun ⟨h1, h2⟩ => hne (by rw [h1, h2, swap_comm])⟩
  rcases hx with rfl | rfl <;> rcases hx' with h | h
  ·
    subst h
    exact key x b d hab hcd (fun h => hne'.1 ⟨rfl, h⟩) hc
  · subst h
    exact key x b c hab (Ne.symm hcd) (fun h => hne'.2 ⟨rfl, h⟩)
      (by rw [swap_comm x c]; exact hc)
  · subst h
    exact key x a d (Ne.symm hab) hcd (fun h => hne'.2 ⟨h, rfl⟩)
      (by rw [swap_comm x a]; exact hc)
  · subst h
    exact key x a c (Ne.symm hab) (Ne.symm hcd) (fun h => hne'.1 ⟨h, rfl⟩)
      (by rw [swap_comm x a, swap_comm x c]; exact hc)

theorem exists_not_swap {U : Subgroup (Perm (Fin n))} (hU : IVK.IsFourSubgroup U) :
    ∃ w ∈ U, w ≠ 1 ∧ w * w = 1 ∧ ¬ w.IsSwap := by
  have := hU.1
  have hsq : ∀ x ∈ U, x * x = 1 := fun x hx => by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥U)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h4 := hU.2
  obtain ⟨u, huU, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra h
    push Not at h
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall U).mpr h
    rw [this, card_bot] at h4
    omega
  obtain ⟨v, hvU, hv1, hvu⟩ : ∃ v ∈ U, v ≠ 1 ∧ v ≠ u := by
    by_contra h
    push Not at h
    have hsub : (U : Set (Perm (Fin n))) ⊆ {1, u} := fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h x hx hx1)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hu1.symm, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at this
    omega
  by_cases hu : u.IsSwap
  · by_cases hv : v.IsSwap
    · refine ⟨u * v, U.mul_mem huU hvU, fun h => hvu ?_, ?_, fun hs => ?_⟩
      · have := hsq u huU
        calc v = u * (u * v) := by rw [← mul_assoc, this, one_mul]
          _ = u := by rw [h, mul_one]
      · exact hsq _ (U.mul_mem huU hvU)
      · have hd := disjoint_of_isSwap hu hv (hcomm u huU v hvU) (Ne.symm hvu)
        have h1 := hd.card_support_mul
        rw [card_support_eq_two.mpr hu, card_support_eq_two.mpr hv,
          card_support_eq_two.mpr hs] at h1
        omega
    · exact ⟨v, hvU, hv1, hsq v hvU, hv⟩
  · exact ⟨u, huU, hu1, hsq u huU, hu⟩

end FinAlt

open FinAlt

theorem noFourPerf_S8 : NoFourPerf (Perm (Fin 8)) := by
  refine noFourPerf_of fun U hU => ?_
  obtain ⟨w, hwU, hw1, hww, hws⟩ := exists_not_swap hU
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
  obtain ⟨k, hk1, hsupp, hk8, hc⟩ := card_centralizer_of_prime Nat.prime_two hw2
  have hk2 : k ≠ 1 := by
    rintro rfl
    exact hws (card_support_eq_two.mp hsupp)
  have hsol : Group.IsSolvable ↥(centralizer ({w} : Set (Perm (Fin 8)))) := by
    have hk4 : k ≤ 4 := by omega
    interval_cases k
    · omega
    · exact isSolvable_of_card_eq_pow_mul_pow (a := 6) (b := 1) Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [hc]; decide)
    · exact isSolvable_of_card_eq_pow_mul_pow (a := 5) (b := 1) Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [hc]; decide)
    · exact isSolvable_of_card_eq_pow_mul_pow (a := 7) (b := 1) Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [hc]; decide)
  have hle : centralizer (U : Set (Perm (Fin 8))) ≤ centralizer ({w} : Set (Perm (Fin 8))) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwU)
  exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).surjective

theorem finCellB_a8 {Y : Type} [Group Y] (h : Nonempty (Y ≃* alternatingGroup (Fin 8))) :
    FinCellB Y := by
  obtain ⟨e⟩ := h
  exact finCellB_of (NoFourPerf.of_equiv (autTransport (by norm_num) (by norm_num) e)
    noFourPerf_S8)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

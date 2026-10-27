module

public import CFSG.Fischer.Classification.Recognition.R3Count
public import CFSG.Assembly.Defs
public import CFSG.Fischer.Classification.Basic.WidthOne

public section

namespace CFSG.LargeExtraspecial.S12InspF3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification CFSG.Fischer.Classification.Recognition.R3

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem two_mul_ncard_D3 (hf : IsF3Form f) (hm : 4 ≤ m) : 2 * (D3 f).ncard = normCount f 1 := by
  classical
  set S : Finset (Fin m → ZMod 3) := Finset.univ.filter fun x => f x x = 1 with hSdef
  have hS : normCount f 1 = S.card := by
    rw [normCount_def, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hD : D3 f = ↑(S.image (reflBar f)) := by
    ext q
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, hSdef, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact mem_D3_iff
  rw [hD, Set.ncard_coe_finset, hS, Finset.card_eq_sum_card_image (reflBar f) S,
    Finset.sum_const_nat (m := 2) fun q hq => ?_, mul_comm]
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
  have hv1 : f v v = 1 := (Finset.mem_filter.mp hv).2
  have hfib : (S.filter fun a => reflBar f a = reflBar f v) = {v, -v} := by
    ext x
    simp only [Finset.mem_filter, hSdef, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxv⟩
      exact (reflBar_eq_reflBar_iff hf hm hv1 hx).1 hxv.symm
    · rintro (rfl | rfl)
      · exact ⟨hv1, rfl⟩
      · exact ⟨by rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg, hv1],
          reflBar_neg v⟩
  rw [hfib, Finset.card_pair (F3.ne_neg_self (F3.ne_zero_of_norm_one hv1))]

theorem T_iterate_three_left : T^[3] (1, 2, 0) = (33, 24, 24) := by
  decide

theorem T_iterate_three_right : T^[3] (1, 0, 2) = (21, 30, 30) := by
  decide

theorem ncard_D3_local_eq_fifteen {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    (hf : IsF3Form f) {v : Fin 5 → ZMod 3} (hv : f v v = 1) (h36 : (D3 f).ncard = 36)
    {f' : LinearMap.BilinForm (ZMod 3) (Fin 4 → ZMod 3)} (hf' : IsF3Form f')
    {e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)} (he : ∀ a b, f' (e a) (e b) = f a b) :
    (D3 f').ncard = 15 := by
  have hrf : restrictForm f e = f' := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [← e.apply_symm_apply x, ← e.apply_symm_apply y, restrictForm_apply, he]
  have h72 : normCount f 1 = 72 := by
    rw [← two_mul_ncard_D3 hf (by norm_num), h36]
  have hsplit := normCount_eq (n := 4) hf hv e 1
  rw [hrf, h72, show (1 : ZMod 3) - 1 = 0 by decide] at hsplit
  have h2 := two_mul_ncard_D3 hf' (by norm_num)
  rcases normTriple_eq 3 f' hf' with h | h
  · rw [T_iterate_three_left] at h
    simp only [Prod.mk.injEq] at h
    omega
  · rw [T_iterate_three_right] at h
    simp only [Prod.mk.injEq] at h
    omega

theorem nonabelian_commutator_R3_of_four_le (hf : IsF3Form f) (hm : 4 ≤ m)
    (hS : IsSimpleGroup (commutator (R3 f))) : ∃ a b : commutator (R3 f), a * b ≠ b * a := by
  by_contra! hab
  obtain ⟨φ, hφ⟩ := Pair.exists_mulEquiv_perm_three (pair_R3 hf hm) (center_R3_eq_bot hf hm) hS
    hab
  obtain ⟨v, hv⟩ := F3.exists_norm_eq hf (by omega) (one_ne_zero (α := ZMod 3))
  obtain ⟨w, hw, hwv⟩ := F3.exists_norm_eq_perp hf (by omega) hv (one_ne_zero (α := ZMod 3))
  have hvw : f v w = 0 := by rw [hf.symm]; exact hwv
  have hne : reflBar f v ≠ reflBar f w := by
    intro h
    rcases (reflBar_eq_reflBar_iff hf hm hv hw).1 h with h' | h'
    · rw [h', hv] at hwv
      exact one_ne_zero hwv
    · rw [h', LinearMap.BilinForm.neg_left, hv] at hwv
      exact one_ne_zero (neg_eq_zero.1 hwv)
  have hc : reflBar f v * reflBar f w = reflBar f w * reflBar f v :=
    (reflBar_commute_iff hf hm hv hw).2 (Or.inl hvw)
  have key : ∀ σ τ : Equiv.Perm (Fin 3), σ.support.card = 2 → τ.support.card = 2 →
      σ * τ = τ * σ → σ = τ := by
    decide
  have hsw : ∀ {u}, f u u = 1 → (φ (reflBar f u)).support.card = 2 := fun hu =>
    Equiv.Perm.card_support_eq_two.2 ((hφ _).1 (reflBar_mem_D3 hu))
  exact hne (φ.injective (key _ _ (hsw hv) (hsw hw) (by rw [← map_mul, ← map_mul, hc])))

end CFSG.LargeExtraspecial.S12InspF3

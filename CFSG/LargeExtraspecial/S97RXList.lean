module

public import CFSG.LargeExtraspecial.S97RXAbs

public section

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.CGT.Timmesfeld75 CFSG.Blueprint.NativeSporadic

theorem coe_smul_sylow_eq_conjSubgroup {Λ : Type*} [Group Λ] {p : ℕ} (P : Sylow p Λ) (y : Λ) :
    ((y • P : Sylow p Λ) : Subgroup Λ) = conjSubgroup y (P : Subgroup Λ) := by
  rw [Sylow.coe_subgroup_smul]
  rfl

theorem srProp_of_sylow {Λ : Type*} [Group Λ] [Finite Λ] {T : Subgroup Λ} (hWC : IsWC T)
    (P : Sylow 2 Λ) (hTZ : ∀ s ∈ (P : Subgroup Λ), ∀ t ∈ T, s * t = t * s)
    (hN : ∃ P' : Sylow 2 Λ, normalizer (T : Set Λ) = normalizer ((P' : Subgroup Λ) : Set Λ)) :
    SRProp T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hN⟩ := hN
  have hT2 : IsPGroup 2 T := fun x => ⟨1, Subtype.ext (by
    rw [pow_one]; simpa using hWC.1.2 x x.2)⟩
  have hPN : (P : Subgroup Λ) ≤ normalizer ((P' : Subgroup Λ) : Set Λ) := by
    rw [← hN]
    intro s hs
    refine mem_normalizer_iff_conjSubgroup_eq.mpr ?_
    refine Subgroup.eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj s).injective).ge
    rintro _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hTZ s hs t ht, mul_inv_cancel_right]
    exact ht
  have hPP' : (P : Subgroup Λ) = P' := by
    have h1 : (P : Subgroup Λ) ⊓ normalizer ((P' : Subgroup Λ) : Set Λ) =
        (P : Subgroup Λ) ⊓ (P' : Subgroup Λ) :=
      IsPGroup.inf_normalizer_sylow P.isPGroup' P'
    rw [inf_eq_left.mpr hPN] at h1
    exact (P.is_maximal' P'.isPGroup' (h1.le.trans inf_le_right)).symm
  intro y hne
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨huT, huN⟩ := mem_inf.mp hu
  by_contra hu1
  have hu1' : u ≠ 1 := fun h0 => hu1 (h0 ▸ one_mem _)
  have huN' : u ∈ normalizer (((y • P : Sylow 2 Λ) : Subgroup Λ) : Set Λ) := by
    rw [coe_smul_sylow_eq_conjSubgroup, mem_normalizer_conj_iff97, hPP', ← hN]
    exact mem_normalizer_conj_iff97.mp huN
  have huP : u ∈ ((y • P : Sylow 2 Λ) : Subgroup Λ) := by
    have h1 : zpowers u ⊓ normalizer (((y • P : Sylow 2 Λ) : Subgroup Λ) : Set Λ) =
        zpowers u ⊓ ((y • P : Sylow 2 Λ) : Subgroup Λ) :=
      IsPGroup.inf_normalizer_sylow (hT2.to_le (zpowers_le.mpr huT)) (y • P)
    have h2 : u ∈ zpowers u ⊓ normalizer (((y • P : Sylow 2 Λ) : Subgroup Λ) : Set Λ) :=
      ⟨mem_zpowers u, huN'⟩
    rw [h1] at h2
    exact h2.2
  rw [coe_smul_sylow_eq_conjSubgroup, mem_conjSubgroup] at huP
  refine hne ((hWC.2 u huT hu1').2 y fun w hw => mem_centralizer_iff.mpr fun x hx => ?_)
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rw [mem_conjSubgroup] at hw
  have hc := hTZ _ huP _ hw
  calc x * w = y * ((y⁻¹ * x * y) * (y⁻¹ * w * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * w * y) * (y⁻¹ * x * y)) * y⁻¹ := by rw [hc]
    _ = w * x := by group

theorem exists_orderOf_five_alternating_six :
    ∃ c : alternatingGroup (Fin 6), orderOf c = 5 := by
  have hnd : ([0, 1, 2, 3, 4] : List (Fin 6)).Nodup := by decide
  have hcyc := List.isCycle_formPerm hnd (by decide)
  have hsupp := List.support_formPerm_of_nodup _ hnd (by decide)
  have hmem : ([0, 1, 2, 3, 4] : List (Fin 6)).formPerm ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, hcyc.sign, hsupp]
    decide
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [Subgroup.orderOf_mk, hcyc.orderOf, hsupp]
  decide

theorem exists_orderOf_five_alternating_seven :
    ∃ c : alternatingGroup (Fin 7), orderOf c = 5 := by
  have hnd : ([0, 1, 2, 3, 4] : List (Fin 7)).Nodup := by decide
  have hcyc := List.isCycle_formPerm hnd (by decide)
  have hsupp := List.support_formPerm_of_nodup _ hnd (by decide)
  have hmem : ([0, 1, 2, 3, 4] : List (Fin 7)).formPerm ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, hcyc.sign, hsupp]
    decide
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [Subgroup.orderOf_mk, hcyc.orderOf, hsupp]
  decide

@[expose] def m23Cycle : List (Fin 23) :=
  [0, 14, 16, 15, 10, 3, 4, 6, 7, 22, 2, 1, 9, 8, 21, 12, 18, 19, 13, 17, 5, 20, 11]

set_option maxRecDepth 100000 in
theorem m23_gens_mul :
    (List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
      List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
      List.formPerm [20, 21]) *
    (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
      List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]) =
      (m23Cycle.formPerm : Equiv.Perm (Fin 23)) := by
  ext i
  fin_cases i <;> decide

theorem exists_orderOf_23_M23 : ∃ x : Carrier .M23, orderOf x = 23 := by
  have hmem : (m23Cycle.formPerm : Equiv.Perm (Fin 23)) ∈ M23 := by
    rw [← m23_gens_mul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  refine ⟨(⟨m23Cycle.formPerm, hmem⟩ : ↥M23), ?_⟩
  have h : orderOf (⟨m23Cycle.formPerm, hmem⟩ : ↥M23) = 23 := by
    rw [Subgroup.orderOf_mk, (List.isCycle_formPerm (by decide) (by decide)).orderOf,
      List.support_formPerm_of_nodup _ (by decide) (by decide)]
    decide
  exact h

@[expose] def m24Cycle : List (Fin 24) :=
  [1, 11, 20, 15, 4, 10, 17, 18, 19, 23, 21, 22, 9, 12, 2, 5, 3, 8, 7, 14, 16, 13, 6]

set_option maxRecDepth 100000 in
theorem m24_gens_mul :
    (List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
      List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] *
      List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] *
      List.formPerm [19, 23] * List.formPerm [21, 22]) *
    (List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
      List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]) =
      (m24Cycle.formPerm : Equiv.Perm (Fin 24)) := by
  ext i
  fin_cases i <;> decide

theorem exists_orderOf_23_M24 : ∃ x : Carrier .M24, orderOf x = 23 := by
  have hmem : (m24Cycle.formPerm : Equiv.Perm (Fin 24)) ∈ M24 := by
    rw [← m24_gens_mul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  refine ⟨(⟨m24Cycle.formPerm, hmem⟩ : ↥M24), ?_⟩
  have h : orderOf (⟨m24Cycle.formPerm, hmem⟩ : ↥M24) = 23 := by
    rw [Subgroup.orderOf_mk, (List.isCycle_formPerm (by decide) (by decide)).orderOf,
      List.support_formPerm_of_nodup _ (by decide) (by decide)]
    decide
  exact h

end CFSG.LargeExtraspecial.S11

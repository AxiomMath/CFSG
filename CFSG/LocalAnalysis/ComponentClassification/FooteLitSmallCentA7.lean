module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFoote47GenA7

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup Equiv

@[expose] def invCentSup {X : Type*} [Group X] (R : Subgroup X) : Subgroup X :=
  ⨆ (r : X) (_ : r ∈ R) (_ : orderOf r = 2), centralizer ({r} : Set X)

theorem centralizer_le_invCentSup {X : Type*} [Group X] {R : Subgroup X} {r : X} (hr : r ∈ R)
    (hr2 : orderOf r = 2) : centralizer ({r} : Set X) ≤ invCentSup R :=
  le_iSup₂_of_le (f := fun r (_ : r ∈ R) => ⨆ (_ : orderOf r = 2), centralizer ({r} : Set X))
    r hr (le_iSup (fun _ : orderOf r = 2 => centralizer ({r} : Set X)) hr2)

theorem map_invCentSup_le {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (R : Subgroup X) :
    (invCentSup R).map φ.toMonoidHom ≤ invCentSup (R.map φ.toMonoidHom) := by
  unfold invCentSup
  simp only [Subgroup.map_iSup]
  refine iSup₂_le fun r hr => iSup_le fun hr2 => ?_
  rintro _ ⟨y, hy, rfl⟩
  have hφr : φ r ∈ R.map φ.toMonoidHom := ⟨r, hr, rfl⟩
  have hφr2 : orderOf (φ r) = 2 := by rw [MulEquiv.orderOf_eq]; exact hr2
  refine centralizer_le_invCentSup hφr hφr2 (mem_centralizer_singleton_iff.mpr ?_)
  change φ y * φ r = φ r * φ y
  rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hy]

theorem invCentSup_eq_top_of_map {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    {R : Subgroup X} (h : invCentSup R = ⊤) : invCentSup (R.map φ.toMonoidHom) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  apply map_invCentSup_le φ R
  rw [h]
  exact ⟨φ.symm y, mem_top _, φ.apply_symm_apply y⟩

@[expose] def d8Set : Finset (Perm (Fin 7)) :=
  {1, swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 3,
    swap 0 3 * swap 3 2 * swap 2 1 * swap 4 5, swap 0 2 * swap 4 5, swap 1 3 * swap 4 5,
    swap 0 1 * swap 2 3, swap 0 3 * swap 1 2}

theorem d8Set_mul : ∀ x ∈ d8Set, ∀ y ∈ d8Set, x * y ∈ d8Set := by
  simp only [d8Set, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) y
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem d8Set_inv : ∀ x ∈ d8Set, x⁻¹ ∈ d8Set := by
  simp only [d8Set, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem d8Set_sign : ∀ x ∈ d8Set, x ∈ alternatingGroup (Fin 7) := by
  simp only [d8Set, Finset.mem_insert, Finset.mem_singleton, Perm.mem_alternatingGroup]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

@[expose] def d8Perm : Subgroup (Perm (Fin 7)) where
  carrier := ↑d8Set
  mul_mem' ha hb := d8Set_mul _ ha _ hb
  one_mem' := by decide
  inv_mem' {x} hx := d8Set_inv x hx

theorem card_d8Perm : Nat.card d8Perm = 8 := by
  change Nat.card (↑d8Set : Set (Perm (Fin 7))) = 8
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rfl

theorem d8Perm_le : d8Perm ≤ alternatingGroup (Fin 7) := fun x hx => d8Set_sign x hx

@[expose] def d8A7 : Subgroup (alternatingGroup (Fin 7)) :=
  d8Perm.subgroupOf (alternatingGroup (Fin 7))

theorem card_d8A7 : Nat.card d8A7 = 8 := by
  rw [d8A7, ← card_d8Perm]
  exact Nat.card_congr (subgroupOfEquivOfLe d8Perm_le).toEquiv

theorem orderOf_mk_alternatingGroup_eq_two {x : Perm (Fin 7)} (hx : x ∈ alternatingGroup (Fin 7))
    (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    orderOf (⟨x, hx⟩ : alternatingGroup (Fin 7)) = 2 := by
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime (by rw [sq]; exact hx2) hx1

theorem invCentSup_d8A7 : invCentSup d8A7 = ⊤ := by
  set H := invCentSup d8A7 with hH
  have hmem : ∀ x : Perm (Fin 7), x ∈ d8Set → (hx : x ∈ alternatingGroup (Fin 7)) →
      (⟨x, hx⟩ : alternatingGroup (Fin 7)) ∈ d8A7 := fun x hx _ => hx
  have key : ∀ (r c : Perm (Fin 7)) (hr : r ∈ alternatingGroup (Fin 7))
      (hc : c ∈ alternatingGroup (Fin 7)), r ∈ d8Set → r * r = 1 → r ≠ 1 → c * r = r * c →
      c ∈ H.map (alternatingGroup (Fin 7)).subtype := by
    intro r c hr hc hrD hr2 hr1 hcr
    refine ⟨⟨c, hc⟩, centralizer_le_invCentSup (hmem r hrD hr)
      (orderOf_mk_alternatingGroup_eq_two hr hr2 hr1)
      (mem_centralizer_singleton_iff.mpr (Subtype.ext hcr)), rfl⟩
  have hA : ∀ x : Perm (Fin 7), Perm.sign x = 1 → x ∈ alternatingGroup (Fin 7) :=
    fun x hx => Perm.mem_alternatingGroup.mpr hx
  have h₁ := key (swap 0 2 * swap 1 3) (swap 4 5 * swap 4 6) (hA _ (by decide))
    (hA _ (by decide)) (by decide) (by decide) (by decide) (by decide)
  have h₂ := key (swap 0 2 * swap 4 5) (swap 1 3 * swap 1 6) (hA _ (by decide))
    (hA _ (by decide)) (by decide) (by decide) (by decide) (by decide)
  have h₃ := key (swap 1 3 * swap 4 5) (swap 0 2 * swap 0 6) (hA _ (by decide))
    (hA _ (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hle := AutL2Facts.alternatingGroup_le_of_three_cycles _ h₁ h₂ h₃
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem invCentSup_a7_eq_top (R : Sylow 2 (alternatingGroup (Fin 7))) :
    invCentSup (R : Subgroup (alternatingGroup (Fin 7))) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := AutL2Facts.card_alternatingGroup_seven
  set R₀ : Sylow 2 (alternatingGroup (Fin 7)) := Sylow.ofCard d8A7 (by
    rw [card_d8A7, hcard]
    rw [show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    simp [Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]) with hR₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) R₀ R
  have hR : (R : Subgroup (alternatingGroup (Fin 7))) =
      (d8A7 : Subgroup (alternatingGroup (Fin 7))).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hR₀, Sylow.coe_ofCard]
    rfl
  rw [hR]
  exact invCentSup_eq_top_of_map (MulAut.conj g) invCentSup_d8A7

end CFSG.ComponentClassification.FooteLit

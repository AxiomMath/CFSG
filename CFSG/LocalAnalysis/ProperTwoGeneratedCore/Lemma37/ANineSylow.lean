module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open Equiv

@[expose] def aNineSylowGenA : alternatingGroup (Fin 9) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def aNineSylowGenB : alternatingGroup (Fin 9) :=
  ⟨swap 0 2 * swap 1 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def aNineSylowGenC : alternatingGroup (Fin 9) :=
  ⟨swap 4 5 * swap 6 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def aNineSylowGenD : alternatingGroup (Fin 9) :=
  ⟨swap 4 6 * swap 5 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def aNineSylowGenE : alternatingGroup (Fin 9) :=
  ⟨swap 0 1 * swap 4 5, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def aNineSylowGenF : alternatingGroup (Fin 9) :=
  ⟨swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def ANineSylow : Subgroup (alternatingGroup (Fin 9)) :=
  Subgroup.closure {aNineSylowGenA, aNineSylowGenB, aNineSylowGenC, aNineSylowGenD,
    aNineSylowGenE, aNineSylowGenF}

@[expose] def aNineSylowWord (v : Fin 64) : alternatingGroup (Fin 9) :=
  aNineSylowGenA ^ (v.val / 32 % 2) * aNineSylowGenB ^ (v.val / 16 % 2) *
    aNineSylowGenC ^ (v.val / 8 % 2) * aNineSylowGenD ^ (v.val / 4 % 2) *
    aNineSylowGenE ^ (v.val / 2 % 2) * aNineSylowGenF ^ (v.val % 2)

@[expose] def aNineSylowWordPerm (v : Fin 64) : Perm (Fin 9) :=
  (aNineSylowGenA : Perm (Fin 9)) ^ (v.val / 32 % 2) *
    (aNineSylowGenB : Perm (Fin 9)) ^ (v.val / 16 % 2) *
    (aNineSylowGenC : Perm (Fin 9)) ^ (v.val / 8 % 2) *
    (aNineSylowGenD : Perm (Fin 9)) ^ (v.val / 4 % 2) *
    (aNineSylowGenE : Perm (Fin 9)) ^ (v.val / 2 % 2) *
    (aNineSylowGenF : Perm (Fin 9)) ^ (v.val % 2)

@[simp] theorem coe_aNineSylowWord (v : Fin 64) :
    (aNineSylowWord v : Perm (Fin 9)) = aNineSylowWordPerm v := by
  simp only [aNineSylowWord, aNineSylowWordPerm, Subgroup.coe_mul, Subgroup.coe_pow]

theorem aNineSylowGenA_mem : aNineSylowGenA ∈ ANineSylow :=
  Subgroup.subset_closure (by simp)

theorem aNineSylowGenB_mem : aNineSylowGenB ∈ ANineSylow :=
  Subgroup.subset_closure (by simp)

theorem aNineSylowGenC_mem : aNineSylowGenC ∈ ANineSylow :=
  Subgroup.subset_closure (by simp)

theorem aNineSylowGenD_mem : aNineSylowGenD ∈ ANineSylow :=
  Subgroup.subset_closure (by simp)

theorem aNineSylowGenE_mem : aNineSylowGenE ∈ ANineSylow :=
  Subgroup.subset_closure (by simp)

theorem aNineSylowGenF_mem : aNineSylowGenF ∈ ANineSylow :=
  Subgroup.subset_closure (by simp)

theorem aNineSylowWord_mem (v : Fin 64) : aNineSylowWord v ∈ ANineSylow :=
  ANineSylow.mul_mem (ANineSylow.mul_mem (ANineSylow.mul_mem (ANineSylow.mul_mem
    (ANineSylow.mul_mem (ANineSylow.pow_mem aNineSylowGenA_mem _)
      (ANineSylow.pow_mem aNineSylowGenB_mem _)) (ANineSylow.pow_mem aNineSylowGenC_mem _))
    (ANineSylow.pow_mem aNineSylowGenD_mem _)) (ANineSylow.pow_mem aNineSylowGenE_mem _))
    (ANineSylow.pow_mem aNineSylowGenF_mem _)

theorem aNineSylowWordPerm_injective : Function.Injective aNineSylowWordPerm := by
  unfold Function.Injective
  decide +kernel

theorem aNineSylowWord_injective : Function.Injective aNineSylowWord := fun v w h =>
  aNineSylowWordPerm_injective (by rw [← coe_aNineSylowWord, h, coe_aNineSylowWord])

private theorem aNineSylowWordPerm_mul_genA : ∀ v : Fin 64, ∃ w : Fin 64,
    aNineSylowWordPerm v * (aNineSylowGenA : Perm (Fin 9)) = aNineSylowWordPerm w := by
  decide +kernel

private theorem aNineSylowWordPerm_mul_genB : ∀ v : Fin 64, ∃ w : Fin 64,
    aNineSylowWordPerm v * (aNineSylowGenB : Perm (Fin 9)) = aNineSylowWordPerm w := by
  decide +kernel

private theorem aNineSylowWordPerm_mul_genC : ∀ v : Fin 64, ∃ w : Fin 64,
    aNineSylowWordPerm v * (aNineSylowGenC : Perm (Fin 9)) = aNineSylowWordPerm w := by
  decide +kernel

private theorem aNineSylowWordPerm_mul_genD : ∀ v : Fin 64, ∃ w : Fin 64,
    aNineSylowWordPerm v * (aNineSylowGenD : Perm (Fin 9)) = aNineSylowWordPerm w := by
  decide +kernel

private theorem aNineSylowWordPerm_mul_genE : ∀ v : Fin 64, ∃ w : Fin 64,
    aNineSylowWordPerm v * (aNineSylowGenE : Perm (Fin 9)) = aNineSylowWordPerm w := by
  decide +kernel

private theorem aNineSylowWordPerm_mul_genF : ∀ v : Fin 64, ∃ w : Fin 64,
    aNineSylowWordPerm v * (aNineSylowGenF : Perm (Fin 9)) = aNineSylowWordPerm w := by
  decide +kernel

private theorem aNineSylowWord_mul_of {g : alternatingGroup (Fin 9)}
    (hg2 : (g : Perm (Fin 9)) * g = 1)
    (hg : ∀ v : Fin 64, ∃ w : Fin 64, aNineSylowWordPerm v * g = aNineSylowWordPerm w)
    (v : Fin 64) : (∃ w, aNineSylowWord w = aNineSylowWord v * g) ∧
      ∃ w, aNineSylowWord w = aNineSylowWord v * g⁻¹ := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_left (Subtype.ext hg2)
  obtain ⟨w, hw⟩ := hg v
  have hw' : aNineSylowWord w = aNineSylowWord v * g := Subtype.ext (by simp [hw])
  exact ⟨⟨w, hw'⟩, ⟨w, by rw [hinv, hw']⟩⟩

theorem exists_aNineSylowWord_eq {x : alternatingGroup (Fin 9)} (hx : x ∈ ANineSylow) :
    ∃ v : Fin 64, aNineSylowWord v = x := by
  have key : ∀ y ∈ ({aNineSylowGenA, aNineSylowGenB, aNineSylowGenC, aNineSylowGenD,
      aNineSylowGenE, aNineSylowGenF} : Set (alternatingGroup (Fin 9))), ∀ v : Fin 64,
      (∃ w, aNineSylowWord w = aNineSylowWord v * y) ∧
        ∃ w, aNineSylowWord w = aNineSylowWord v * y⁻¹ := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact aNineSylowWord_mul_of (by decide) aNineSylowWordPerm_mul_genA
    · exact aNineSylowWord_mul_of (by decide) aNineSylowWordPerm_mul_genB
    · exact aNineSylowWord_mul_of (by decide) aNineSylowWordPerm_mul_genC
    · exact aNineSylowWord_mul_of (by decide) aNineSylowWordPerm_mul_genD
    · exact aNineSylowWord_mul_of (by decide) aNineSylowWordPerm_mul_genE
    · exact aNineSylowWord_mul_of (by decide) aNineSylowWordPerm_mul_genF
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨0, by simp [aNineSylowWord]⟩
  | mul_right x _ y hy ih =>
    obtain ⟨v, rfl⟩ := ih
    exact (key y hy v).1
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨v, rfl⟩ := ih
    exact (key y hy v).2

@[expose] noncomputable def aNineSylowEquiv : Fin 64 ≃ ANineSylow :=
  Equiv.ofBijective (fun v => ⟨aNineSylowWord v, aNineSylowWord_mem v⟩)
    ⟨fun _ _ h => aNineSylowWord_injective (congrArg Subtype.val h),
      fun x => (exists_aNineSylowWord_eq x.2).imp fun _ h => Subtype.ext h⟩

@[simp] theorem coe_aNineSylowEquiv (v : Fin 64) :
    (aNineSylowEquiv v : alternatingGroup (Fin 9)) = aNineSylowWord v :=
  rfl

theorem card_aNineSylow : Nat.card ANineSylow = 64 := by
  rw [← Nat.card_congr aNineSylowEquiv, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_alternatingGroup_fin_nine : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem factorization_card_alternatingGroup_fin_nine :
    (Nat.card (alternatingGroup (Fin 9))).factorization 2 = 6 := by
  rw [card_alternatingGroup_fin_nine, show (181440 : ℕ) = 2 ^ 6 * 2835 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 2835)]

@[expose] noncomputable def aNineSylowSylow : Sylow 2 (alternatingGroup (Fin 9)) :=
  Sylow.ofCard ANineSylow (by
    rw [card_aNineSylow, factorization_card_alternatingGroup_fin_nine]
    norm_num)

@[simp] theorem coe_aNineSylowSylow :
    (aNineSylowSylow : Subgroup (alternatingGroup (Fin 9))) = ANineSylow :=
  rfl

end CFSG.ProperTwoGeneratedCore.Lemma37

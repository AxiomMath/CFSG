module

public import CFSG.LocalAnalysis.OddStandard.AltStdEvenFusDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusP42Perm

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.P42E

open Equiv Subgroup P42

section Elements

@[expose] def bFun8 (k : Fin 16) (x : Fin 8) : Fin 8 :=
  if h : x.val < 4 then
    ⟨x.val ^^^ (k.val % 4), by
      have h1 := Nat.xor_lt_two_pow (n := 2) (x := x.val) (y := k.val % 4) (by simpa using h)
        (by simp; omega)
      simp at h1
      omega⟩
  else
    ⟨x.val ^^^ (k.val / 4), by
      have h1 := Nat.xor_lt_two_pow (n := 3) (x := x.val) (y := k.val / 4) (by simpa using x.2)
        (by simp; omega)
      simp at h1
      omega⟩

theorem bFun8_involutive (k : Fin 16) : Function.Involutive (bFun8 k) := by
  intro x
  revert k x
  decide

@[expose] def bEl8 (k : Fin 16) : Perm (Fin 8) :=
  Function.Involutive.toPerm (bFun8 k) (bFun8_involutive k)

@[expose] def bGen8 : Fin 4 → Perm (Fin 8) :=
  ![swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7]

private def bIdx8 (σ : Perm (Fin 8)) : Fin 16 :=
  ⟨(σ 0).val % 4 + 4 * ((σ 4).val % 4), by omega⟩

theorem bEl8_apply (k : Fin 16) (x : Fin 8) : bEl8 k x = bFun8 k x := rfl

private theorem bFun8_mul :
    ∀ (k l : Fin 16) (x : Fin 8), bFun8 k (bFun8 l x) = bFun8 (bxor k l) x := by
  decide

theorem bEl8_mul (k l : Fin 16) : bEl8 k * bEl8 l = bEl8 (bxor k l) :=
  Equiv.ext fun x => bFun8_mul k l x

theorem bEl8_zero : bEl8 0 = 1 :=
  Equiv.ext fun x => by
    rw [bEl8_apply, Perm.one_apply]
    revert x
    decide

theorem bEl8_inv (k : Fin 16) : (bEl8 k)⁻¹ = bEl8 k := by
  apply inv_eq_of_mul_eq_one_right
  rw [bEl8_mul, show bxor k k = 0 from Fin.ext (Nat.xor_self _), bEl8_zero]

private theorem bIdx8_bEl8 : ∀ k : Fin 16, bIdx8 (bEl8 k) = k := by
  decide

theorem bEl8_injective : Function.Injective bEl8 := fun k l h => by
  rw [← bIdx8_bEl8 k, ← bIdx8_bEl8 l, h]

private theorem bGen8_apply :
    ∀ (j : Fin 4) (x : Fin 8), bGen8 j x = bEl8 (![1, 2, 4, 8] j) x := by
  decide

theorem bGen8_eq (j : Fin 4) : bGen8 j = bEl8 (![1, 2, 4, 8] j) :=
  Equiv.ext (bGen8_apply j)

theorem bEl8_mem_bBar8 (k : Fin 16) : bEl8 k ∈ bBar8 := by
  have hg : ∀ j : Fin 4, bGen8 j ∈ bBar8 := fun j => by
    unfold bBar8
    apply Subgroup.subset_closure
    fin_cases j <;> simp [bGen8]
  refine fin16_induction (P := fun k => bEl8 k ∈ bBar8) ?_ ?_ ?_ ?_ ?_ ?_ k
  · rw [bEl8_zero]
    exact one_mem _
  · intro k l hk hl
    rw [← bEl8_mul]
    exact mul_mem hk hl
  · simpa [bGen8_eq] using hg 0
  · simpa [bGen8_eq] using hg 1
  · simpa [bGen8_eq] using hg 2
  · simpa [bGen8_eq] using hg 3

theorem mem_bBar8_iff {σ : Perm (Fin 8)} : σ ∈ bBar8 ↔ ∃ k, bEl8 k = σ := by
  constructor
  · intro hσ
    unfold bBar8 at hσ
    induction hσ using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨1, (bGen8_eq 0).symm⟩
      · exact ⟨2, (bGen8_eq 1).symm⟩
      · exact ⟨4, (bGen8_eq 2).symm⟩
      · exact ⟨8, (bGen8_eq 3).symm⟩
    | one => exact ⟨0, bEl8_zero⟩
    | mul y y' _ _ hy hy' =>
      obtain ⟨k, rfl⟩ := hy
      obtain ⟨l, rfl⟩ := hy'
      exact ⟨bxor k l, (bEl8_mul k l).symm⟩
    | inv y _ hy =>
      obtain ⟨k, rfl⟩ := hy
      exact ⟨k, (bEl8_inv k).symm⟩
  · rintro ⟨k, rfl⟩
    exact bEl8_mem_bBar8 k

theorem bBar8_le_alternatingGroup : bBar8 ≤ alternatingGroup (Fin 8) := by
  unfold bBar8
  rw [Subgroup.closure_le]
  intro σ hσ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl | rfl | rfl <;>
    exact Perm.mem_alternatingGroup.2 (sign_swap_mul_swap (by decide) (by decide))

theorem bEl8_mem_alternatingGroup (k : Fin 16) : bEl8 k ∈ alternatingGroup (Fin 8) :=
  bBar8_le_alternatingGroup (bEl8_mem_bBar8 k)

theorem isO6_of_card_support8 : ∀ k : Fin 16, (bEl8 k).support.card = 4 → isO6 k = true := by
  decide

theorem tr_one_eq_bEl8 : tr le88 1 = bEl8 5 :=
  Equiv.ext fun x => by
    revert x
    decide

end Elements

section Witnesses

@[expose] def dt8 (a b c d : Fin 8) : Perm (Fin 8) := swap a b * swap c d

theorem dt8_mem {a b c d : Fin 8} (hab : a ≠ b) (hcd : c ≠ d) :
    dt8 a b c d ∈ alternatingGroup (Fin 8) :=
  Perm.mem_alternatingGroup.2 (sign_swap_mul_swap hab hcd)

@[expose] def wit8 : Fin 11 → Perm (Fin 8) :=
  ![dt8 0 3 4 5, dt8 0 2 4 5, dt8 0 4 1 5 * dt8 2 6 3 7, dt8 0 4 1 6 * dt8 2 5 3 7,
    dt8 0 4 1 7 * dt8 2 5 3 6, dt8 0 1 4 7, dt8 0 3 4 7, dt8 0 2 4 7, dt8 0 1 4 6, dt8 0 3 4 6,
    dt8 0 2 4 6]

theorem wit8_mem (j : Fin 11) : wit8 j ∈ alternatingGroup (Fin 8) := by
  fin_cases j
  · exact (dt8_mem (by decide) (by decide) : dt8 0 3 4 5 ∈ _)
  · exact (dt8_mem (by decide) (by decide) : dt8 0 2 4 5 ∈ _)
  · exact (mul_mem (dt8_mem (by decide) (by decide)) (dt8_mem (by decide) (by decide)) :
      dt8 0 4 1 5 * dt8 2 6 3 7 ∈ _)
  · exact (mul_mem (dt8_mem (by decide) (by decide)) (dt8_mem (by decide) (by decide)) :
      dt8 0 4 1 6 * dt8 2 5 3 7 ∈ _)
  · exact (mul_mem (dt8_mem (by decide) (by decide)) (dt8_mem (by decide) (by decide)) :
      dt8 0 4 1 7 * dt8 2 5 3 6 ∈ _)
  · exact (dt8_mem (by decide) (by decide) : dt8 0 1 4 7 ∈ _)
  · exact (dt8_mem (by decide) (by decide) : dt8 0 3 4 7 ∈ _)
  · exact (dt8_mem (by decide) (by decide) : dt8 0 2 4 7 ∈ _)
  · exact (dt8_mem (by decide) (by decide) : dt8 0 1 4 6 ∈ _)
  · exact (dt8_mem (by decide) (by decide) : dt8 0 3 4 6 ∈ _)
  · exact (dt8_mem (by decide) (by decide) : dt8 0 2 4 6 ∈ _)

private theorem wit8_conj_apply : ∀ (j : Fin 11) (k : Fin 16) (x : Fin 8),
    (wit8 j * bEl8 k * (wit8 j)⁻¹) x = bEl8 (piTab j k) x := by
  decide

theorem wit8_conj (j : Fin 11) (k : Fin 16) : wit8 j * bEl8 k * (wit8 j)⁻¹ = bEl8 (piTab j k) :=
  Equiv.ext (wit8_conj_apply j k)

end Witnesses

section NormCent

theorem mem_normalizer_bBar8_iff {σ : Perm (Fin 8)} :
    σ ∈ normalizer (bBar8 : Set (Perm (Fin 8))) ↔ ∀ k, ∃ l, σ * bEl8 k * σ⁻¹ = bEl8 l := by
  constructor
  · intro h k
    obtain ⟨l, hl⟩ := mem_bBar8_iff.1 ((mem_normalizer_iff.1 h (bEl8 k)).1 (bEl8_mem_bBar8 k))
    exact ⟨l, hl.symm⟩
  · intro h
    apply mem_normalizer_of_forall_conj
    intro b hb
    obtain ⟨k, rfl⟩ := mem_bBar8_iff.1 hb
    obtain ⟨l, hl⟩ := h k
    rw [hl]
    exact bEl8_mem_bBar8 l

theorem mem_centralizer_bBar8_iff {σ : Perm (Fin 8)} :
    σ ∈ centralizer (bBar8 : Set (Perm (Fin 8))) ↔ ∀ k, σ * bEl8 k * σ⁻¹ = bEl8 k := by
  rw [mem_centralizer_iff]
  constructor
  · intro h k
    rw [← h (bEl8 k) (bEl8_mem_bBar8 k), mul_inv_cancel_right]
  · intro h b hb
    obtain ⟨k, rfl⟩ := mem_bBar8_iff.1 hb
    have := h k
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm

end NormCent

section Transport

@[expose] def e89 : Fin 8 ≃ {x : Fin 9 // x.val < 8} where
  toFun i := ⟨⟨i.val, by omega⟩, i.2⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def iota : Perm (Fin 8) →* Perm (Fin 9) := Perm.extendDomainHom e89

theorem iota_injective : Function.Injective iota := Perm.extendDomainHom_injective e89

theorem val_iota_apply_of_lt (σ : Perm (Fin 8)) {x : Fin 9} (hx : x.val < 8) :
    (iota σ x).val = (σ ⟨x.val, hx⟩).val := by
  rw [iota, Perm.extendDomainHom_apply, Perm.extendDomain_apply_subtype σ e89 hx]
  rfl

theorem iota_apply_eight (σ : Perm (Fin 8)) : iota σ 8 = 8 :=
  Perm.extendDomain_apply_not_subtype _ _ (by decide)

theorem sign_iota (σ : Perm (Fin 8)) : Perm.sign (iota σ) = Perm.sign σ :=
  Perm.sign_extendDomain σ e89

private theorem bFun8_val :
    ∀ (k : Fin 16) (x : Fin 8), (bFun8 k x).val = (bFun k (Fin.castSucc x)).val := by
  decide

theorem iota_bEl8 (k : Fin 16) : iota (bEl8 k) = bEl k := by
  ext x
  by_cases hx : x.val < 8
  · rw [val_iota_apply_of_lt _ hx, bEl8_apply, bFun8_val, bEl_apply]
    rfl
  · have hx8 : x = 8 := Fin.ext (by have := x.2; simp only [not_lt] at hx; simp; omega)
    subst hx8
    rw [iota_apply_eight, bEl_apply_eight]

theorem mem_range_iota {τ : Perm (Fin 9)} (h : τ 8 = 8) : τ ∈ iota.range := by
  have h8 : ∀ y : Fin 9, y.val < 8 ↔ y ≠ 8 := by
    intro y
    constructor
    · rintro hy rfl
      exact absurd hy (by decide)
    · intro hy
      have h1 : y.val ≠ 8 := fun h' => hy (Fin.ext (by simpa using h'))
      have := y.2
      omega
  have hp : ∀ x : Fin 9, (τ x).val < 8 ↔ x.val < 8 := by
    intro x
    rw [h8, h8, Ne, Ne, not_iff_not]
    constructor
    · intro hx
      rw [← h] at hx
      exact τ.injective hx
    · rintro rfl
      exact h
  refine ⟨e89.symm.permCongr (τ.subtypePerm hp), Equiv.ext fun x => ?_⟩
  by_cases hx : x.val < 8
  · apply Fin.ext
    rw [val_iota_apply_of_lt _ hx]
    rfl
  · have hx8 : x = 8 := Fin.ext (by have := x.2; simp only [not_lt] at hx; simp; omega)
    subst hx8
    rw [iota_apply_eight, h]

theorem comap_iota_centralizer :
    (centralizer (bBar : Set (Perm (Fin 9)))).comap iota =
      centralizer (bBar8 : Set (Perm (Fin 8))) := by
  ext σ
  rw [mem_comap, mem_centralizer_bBar_iff, mem_centralizer_bBar8_iff]
  refine forall_congr' fun k => ?_
  rw [← iota_bEl8, ← map_inv, ← map_mul, ← map_mul, iota_injective.eq_iff]

theorem comap_iota_normalizer :
    (normalizer (bBar : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9)).comap iota =
      normalizer (bBar8 : Set (Perm (Fin 8))) ⊓ alternatingGroup (Fin 8) := by
  ext σ
  rw [mem_comap, mem_inf, mem_inf, mem_normalizer_bBar_iff, mem_normalizer_bBar8_iff,
    Perm.mem_alternatingGroup, Perm.mem_alternatingGroup, sign_iota]
  refine and_congr_left' (forall_congr' fun k => exists_congr fun l => ?_)
  rw [← iota_bEl8, ← iota_bEl8, ← map_inv, ← map_mul, ← map_mul, iota_injective.eq_iff]

theorem normalizer_bBar_le_range :
    normalizer (bBar : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9) ≤ iota.range :=
  fun _ hτ => mem_range_iota (fix_eight_of_mem_normalizer hτ.1)

theorem relIndex_centralizer_bBar8 :
    (centralizer (bBar8 : Set (Perm (Fin 8)))).relIndex
      (normalizer (bBar8 : Set (Perm (Fin 8))) ⊓ alternatingGroup (Fin 8)) = 36 := by
  rw [← comap_iota_centralizer, ← comap_iota_normalizer, relIndex_comap,
    map_comap_eq_self normalizer_bBar_le_range]
  exact relIndex_centralizer_bBar

end Transport

end CFSG.OddStandard.AltStdSmall4.Fus.P42E

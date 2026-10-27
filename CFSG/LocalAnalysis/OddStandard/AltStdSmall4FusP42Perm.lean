module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusP42Count
public import Certificates.Certificate36404

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.P42

open Equiv Subgroup

theorem mem_normalizer_of_forall_conj {G : Type*} [Group G] {H : Subgroup G} [Finite H] {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

section Elements

theorem bEl_apply (k : Fin 16) (x : Fin 9) : bEl k x = bFun k x := rfl

private theorem bFun_mul : ∀ (k l : Fin 16) (x : Fin 9), bFun k (bFun l x) = bFun (bxor k l) x := by
  decide

theorem bEl_mul (k l : Fin 16) : bEl k * bEl l = bEl (bxor k l) :=
  Equiv.ext fun x => bFun_mul k l x

theorem bEl_zero : bEl 0 = 1 :=
  Equiv.ext fun x => by
    rw [bEl_apply, Perm.one_apply]
    revert x
    decide

theorem bEl_inv (k : Fin 16) : (bEl k)⁻¹ = bEl k := by
  apply inv_eq_of_mul_eq_one_right
  rw [bEl_mul, show bxor k k = 0 from Fin.ext (Nat.xor_self _), bEl_zero]

private theorem bIdx_bEl : ∀ k : Fin 16, bIdx (bEl k) = k := by
  decide

theorem bEl_injective : Function.Injective bEl := fun k l h => by
  rw [← bIdx_bEl k, ← bIdx_bEl l, h]

theorem bEl_apply_eight : ∀ k : Fin 16, bEl k 8 = 8 := by
  decide

private theorem eq_eight_of_fix : ∀ x : Fin 9, bEl 1 x = x → bEl 4 x = x → x = 8 := by
  decide

private theorem bGen_apply : ∀ (j : Fin 4) (x : Fin 9), bGen j x = bEl (![1, 2, 4, 8] j) x := by
  decide

theorem bGen_eq (j : Fin 4) : bGen j = bEl (![1, 2, 4, 8] j) :=
  Equiv.ext (bGen_apply j)

theorem fin16_induction {P : Fin 16 → Prop} (h0 : P 0) (hm : ∀ k l, P k → P l → P (bxor k l))
    (h1 : P 1) (h2 : P 2) (h4 : P 4) (h8 : P 8) : ∀ k, P k := by
  have h3 : P 3 := (show bxor 1 2 = 3 by decide) ▸ hm 1 2 h1 h2
  have h12 : P 12 := (show bxor 4 8 = 12 by decide) ▸ hm 4 8 h4 h8
  have key : ∀ k : Fin 16, ∃ a b : Fin 16, (a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) ∧
      (b = 0 ∨ b = 4 ∨ b = 8 ∨ b = 12) ∧ bxor a b = k := by
    decide
  intro k
  obtain ⟨a, b, ha, hb, rfl⟩ := key k
  refine hm a b ?_ ?_
  · rcases ha with rfl | rfl | rfl | rfl <;> assumption
  · rcases hb with rfl | rfl | rfl | rfl <;> assumption

theorem bEl_mem_bBar (k : Fin 16) : bEl k ∈ bBar := by
  have hg : ∀ j : Fin 4, bGen j ∈ bBar := fun j => by
    unfold bBar
    apply Subgroup.subset_closure
    fin_cases j <;> simp [bGen]
  refine fin16_induction (P := fun k => bEl k ∈ bBar) ?_ ?_ ?_ ?_ ?_ ?_ k
  · rw [bEl_zero]
    exact one_mem _
  · intro k l hk hl
    rw [← bEl_mul]
    exact mul_mem hk hl
  · simpa [bGen_eq] using hg 0
  · simpa [bGen_eq] using hg 1
  · simpa [bGen_eq] using hg 2
  · simpa [bGen_eq] using hg 3

theorem mem_bBar_iff {σ : Perm (Fin 9)} : σ ∈ bBar ↔ ∃ k, bEl k = σ := by
  constructor
  · intro hσ
    unfold bBar at hσ
    induction hσ using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨1, (bGen_eq 0).symm⟩
      · exact ⟨2, (bGen_eq 1).symm⟩
      · exact ⟨4, (bGen_eq 2).symm⟩
      · exact ⟨8, (bGen_eq 3).symm⟩
    | one => exact ⟨0, bEl_zero⟩
    | mul y y' _ _ hy hy' =>
      obtain ⟨k, rfl⟩ := hy
      obtain ⟨l, rfl⟩ := hy'
      exact ⟨bxor k l, (bEl_mul k l).symm⟩
    | inv y _ hy =>
      obtain ⟨k, rfl⟩ := hy
      exact ⟨k, (bEl_inv k).symm⟩
  · rintro ⟨k, rfl⟩
    exact bEl_mem_bBar k

theorem bBar_le_alternatingGroup : bBar ≤ alternatingGroup (Fin 9) := by
  unfold bBar
  rw [Subgroup.closure_le]
  intro σ hσ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with rfl | rfl | rfl | rfl <;>
    exact Perm.mem_alternatingGroup.2 (sign_swap_mul_swap (by decide) (by decide))

theorem bEl_mem_alternatingGroup (k : Fin 16) : bEl k ∈ alternatingGroup (Fin 9) :=
  bBar_le_alternatingGroup (bEl_mem_bBar k)

theorem isO6_of_card_support : ∀ k : Fin 16, (bEl k).support.card = 4 → isO6 k = true := by
  decide

theorem tr_one_eq_bEl : tr le89 1 = bEl 5 :=
  Equiv.ext fun x => by
    revert x
    decide

end Elements

section Witnesses

@[expose] def dt (a b c d : Fin 9) : Perm (Fin 9) := swap a b * swap c d

theorem dt_mem {a b c d : Fin 9} (hab : a ≠ b) (hcd : c ≠ d) :
    dt a b c d ∈ alternatingGroup (Fin 9) :=
  Perm.mem_alternatingGroup.2 (sign_swap_mul_swap hab hcd)

@[expose] def wit : Fin 11 → Perm (Fin 9) :=
  ![dt 0 3 4 5, dt 0 2 4 5, dt 0 4 1 5 * dt 2 6 3 7, dt 0 4 1 6 * dt 2 5 3 7,
    dt 0 4 1 7 * dt 2 5 3 6, dt 0 1 4 7, dt 0 3 4 7, dt 0 2 4 7, dt 0 1 4 6, dt 0 3 4 6,
    dt 0 2 4 6]

theorem wit_mem (j : Fin 11) : wit j ∈ alternatingGroup (Fin 9) := by
  fin_cases j
  · exact (dt_mem (by decide) (by decide) : dt 0 3 4 5 ∈ _)
  · exact (dt_mem (by decide) (by decide) : dt 0 2 4 5 ∈ _)
  · exact (mul_mem (dt_mem (by decide) (by decide)) (dt_mem (by decide) (by decide)) :
      dt 0 4 1 5 * dt 2 6 3 7 ∈ _)
  · exact (mul_mem (dt_mem (by decide) (by decide)) (dt_mem (by decide) (by decide)) :
      dt 0 4 1 6 * dt 2 5 3 7 ∈ _)
  · exact (mul_mem (dt_mem (by decide) (by decide)) (dt_mem (by decide) (by decide)) :
      dt 0 4 1 7 * dt 2 5 3 6 ∈ _)
  · exact (dt_mem (by decide) (by decide) : dt 0 1 4 7 ∈ _)
  · exact (dt_mem (by decide) (by decide) : dt 0 3 4 7 ∈ _)
  · exact (dt_mem (by decide) (by decide) : dt 0 2 4 7 ∈ _)
  · exact (dt_mem (by decide) (by decide) : dt 0 1 4 6 ∈ _)
  · exact (dt_mem (by decide) (by decide) : dt 0 3 4 6 ∈ _)
  · exact (dt_mem (by decide) (by decide) : dt 0 2 4 6 ∈ _)

private theorem wit_conj_apply : ∀ (j : Fin 11) (k : Fin 16) (x : Fin 9),
    (wit j * bEl k * (wit j)⁻¹) x = bEl (piTab j k) x := by
  decide

theorem wit_conj (j : Fin 11) (k : Fin 16) : wit j * bEl k * (wit j)⁻¹ = bEl (piTab j k) :=
  Equiv.ext (wit_conj_apply j k)

end Witnesses

section NormCent

theorem mem_normalizer_bBar_iff {σ : Perm (Fin 9)} :
    σ ∈ normalizer (bBar : Set (Perm (Fin 9))) ↔ ∀ k, ∃ l, σ * bEl k * σ⁻¹ = bEl l := by
  constructor
  · intro h k
    obtain ⟨l, hl⟩ := mem_bBar_iff.1 ((mem_normalizer_iff.1 h (bEl k)).1 (bEl_mem_bBar k))
    exact ⟨l, hl.symm⟩
  · intro h
    apply mem_normalizer_of_forall_conj
    intro b hb
    obtain ⟨k, rfl⟩ := mem_bBar_iff.1 hb
    obtain ⟨l, hl⟩ := h k
    rw [hl]
    exact bEl_mem_bBar l

theorem mem_centralizer_bBar_iff {σ : Perm (Fin 9)} :
    σ ∈ centralizer (bBar : Set (Perm (Fin 9))) ↔ ∀ k, σ * bEl k * σ⁻¹ = bEl k := by
  rw [mem_centralizer_iff]
  constructor
  · intro h k
    rw [← h (bEl k) (bEl_mem_bBar k), mul_inv_cancel_right]
  · intro h b hb
    obtain ⟨k, rfl⟩ := mem_bBar_iff.1 hb
    have := h k
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm

theorem fix_eight_of_mem_normalizer {σ : Perm (Fin 9)}
    (h : σ ∈ normalizer (bBar : Set (Perm (Fin 9)))) : σ 8 = 8 := by
  have key : ∀ k, bEl k (σ 8) = σ 8 := by
    intro k
    obtain ⟨l, hl⟩ := mem_bBar_iff.1 ((mem_normalizer_iff.1 (inv_mem h) (bEl k)).1
      (bEl_mem_bBar k))
    have h8 := bEl_apply_eight l
    rw [hl, inv_inv, Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq] at h8
    exact h8
  exact eq_eight_of_fix _ (key 1) (key 4)

private theorem conj_mem_of_gen {σ : Perm (Fin 9)} (h : ∀ j, σ * bGen j * σ⁻¹ ∈ bBar) :
    σ ∈ normalizer (bBar : Set (Perm (Fin 9))) := by
  apply mem_normalizer_of_forall_conj
  have hle : bBar ≤ bBar.comap (MulAut.conj σ).toMonoidHom := by
    show Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact h 0
    · exact h 1
    · exact h 2
    · exact h 3
  exact fun b hb => hle hb

private theorem normB_iff {σ : Perm (Fin 9)} :
    normB σ = true ↔ σ ∈ normalizer (bBar : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9) := by
  simp only [normB, Bool.and_eq_true, decide_eq_true_eq, Subgroup.mem_inf,
    Perm.mem_alternatingGroup]
  constructor
  · rintro ⟨⟨-, hconj⟩, hsign⟩
    refine ⟨conj_mem_of_gen fun j => ?_, hsign⟩
    rw [hconj j]
    exact bEl_mem_bBar _
  · rintro ⟨hN, hsign⟩
    refine ⟨⟨fix_eight_of_mem_normalizer hN, fun j => ?_⟩, hsign⟩
    obtain ⟨l, hl⟩ := mem_bBar_iff.1 ((mem_normalizer_iff.1 hN (bGen j)).1
      (by rw [bGen_eq]; exact bEl_mem_bBar _))
    rw [← hl, bIdx_bEl]

private theorem centB_iff {σ : Perm (Fin 9)} :
    centB σ = true ↔ σ ∈ centralizer (bBar : Set (Perm (Fin 9))) ⊓
      (normalizer (bBar : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9)) := by
  simp only [centB, Bool.and_eq_true, decide_eq_true_eq, Subgroup.mem_inf,
    Perm.mem_alternatingGroup]
  constructor
  · rintro ⟨⟨-, hcomm⟩, hsign⟩
    have hC : σ ∈ centralizer (bBar : Set (Perm (Fin 9))) := by
      rw [mem_centralizer_iff]
      have hle : bBar ≤ centralizer ({σ} : Set (Perm (Fin 9))) := by
        show Subgroup.closure _ ≤ _
        rw [Subgroup.closure_le]
        intro g hg
        rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact (hcomm 0).symm
        · exact (hcomm 1).symm
        · exact (hcomm 2).symm
        · exact (hcomm 3).symm
      intro b hb
      exact mem_centralizer_singleton_iff.1 (hle hb)
    exact ⟨hC, centralizer_le_normalizer _ hC, hsign⟩
  · rintro ⟨hC, hN, hsign⟩
    refine ⟨⟨fix_eight_of_mem_normalizer hN, fun j => ?_⟩, hsign⟩
    exact (mem_centralizer_iff.1 hC (bGen j) (by rw [bGen_eq]; exact bEl_mem_bBar _)).symm

theorem relIndex_centralizer_bBar :
    (centralizer (bBar : Set (Perm (Fin 9)))).relIndex
      (normalizer (bBar : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9)) = 36 := by
  have hc := Certificates.certificate36404
  simp only [p42Check, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hN, hC⟩ := hc
  have h1 : Nat.card (normalizer (bBar : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9) :
      Subgroup (Perm (Fin 9))) = 576 := by
    rw [← hN, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => normB_iff.symm)
  have h2 : Nat.card (centralizer (bBar : Set (Perm (Fin 9))) ⊓
      (normalizer (bBar : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9)) :
        Subgroup (Perm (Fin 9))) = 16 := by
    rw [← hC, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => centB_iff.symm)
  have h3 := Subgroup.relIndex_mul_card (centralizer (bBar : Set (Perm (Fin 9))))
    (normalizer (bBar : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9))
  rw [h1, h2] at h3
  omega

end NormCent

end CFSG.OddStandard.AltStdSmall4.Fus.P42

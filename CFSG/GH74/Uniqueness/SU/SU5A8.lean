module

public import CFSG.GH74.Uniqueness.SU.SU5J2Sub

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup

@[expose] def IsA8Type (P : Type*) [Group P] : Prop :=
  ∃ Q : Sylow 2 (alternatingGroup (Fin 8)), Nonempty (P ≃* Q)

namespace J2Syl

@[expose] def Hp (s : J2Syl) : Prop :=
  (s.left.a = 0 ∨ s.left.a = 1) ∧ (s.left.b = 0 ∨ s.left.b = 1) ∧
    ((s.right = 1 ∧ (s.left.c = 0 ∨ s.left.c = 1)) ∨
      (s.right ≠ 1 ∧ (s.left.c = F4c.w ∨ s.left.c = F4c.w2)))

instance instDecHp (s : J2Syl) : Decidable (Hp s) := by unfold Hp; infer_instance

@[expose] def Hs : Subgroup J2Syl := subOfPred Hp (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem card_Hs : Nat.card Hs = 16 := by
  unfold Hs; rw [card_subOfPred]; decide +kernel

@[expose] def rep (i : Fin 8) : J2Syl :=
  ⟨⟨if i.val % 2 = 0 then 0 else F4c.w, if (i.val / 2) % 2 = 0 then 0 else F4c.w, 0⟩,
    if (i.val / 4) % 2 = 0 then 1 else Multiplicative.ofAdd 1⟩

@[expose] def label (g : J2Syl) : Fin 8 :=
  match (List.finRange 8).find? (fun i => decide (Hp ((rep i)⁻¹ * g))) with
  | some i => i
  | none => 0

theorem rep_label : ∀ g : J2Syl, Hp ((rep (label g))⁻¹ * g) := by decide +kernel

theorem label_mul : ∀ g h : J2Syl, Hp h → label (g * h) = label g := by decide +kernel

theorem label_rep : ∀ i : Fin 8, label (rep i) = i := by decide +kernel

theorem label_eq_of_mem {g g' : J2Syl} (h : g⁻¹ * g' ∈ Hs) : label g = label g' := by
  have h2 : g * (g⁻¹ * g') = g' := by group
  calc label g = label (g * (g⁻¹ * g')) := (label_mul g _ h).symm
    _ = label g' := by rw [h2]

@[expose] def cosetEquiv : J2Syl ⧸ Hs ≃ Fin 8 where
  toFun := Quotient.lift label (fun _ _ hr => label_eq_of_mem (QuotientGroup.leftRel_apply.1 hr))
  invFun i := (rep i : J2Syl ⧸ Hs)
  left_inv := by
    intro q
    refine QuotientGroup.induction_on q (fun g => ?_)
    exact QuotientGroup.eq.2 (rep_label g)
  right_inv := label_rep

@[expose] def permRep : J2Syl →* Equiv.Perm (Fin 8) where
  toFun s := cosetEquiv.permCongr (MulAction.toPermHom J2Syl (J2Syl ⧸ Hs) s)
  map_one' := by
    ext i
    simp [Equiv.permCongr_apply]
  map_mul' s t := by
    rw [map_mul]
    exact Equiv.permCongr_mul _ _ _

theorem permRep_apply (s : J2Syl) (i : Fin 8) : permRep s i = label (s * rep i) := rfl

theorem permRep_eq_one_iff : ∀ s : J2Syl, permRep s = 1 ↔ (s = 1 ∨ s = z0) := by
  have h : ∀ s : J2Syl, (∀ i : Fin 8, label (s * rep i) = i) ↔ (s = 1 ∨ s = z0) := by
    decide +kernel
  intro s
  rw [← h s]
  constructor
  · intro h1 i
    rw [← permRep_apply, h1]
    rfl
  · intro h1
    refine Equiv.ext (fun i => ?_)
    rw [permRep_apply]
    exact h1 i

theorem sign_permRep : ∀ s : J2Syl, Equiv.Perm.sign (permRep s) = 1 := by decide +kernel

theorem mem_zpowers_of_sq_eq_one {M : Type*} [Group M] {a : M} (ha : a ≠ 1) (ha2 : a * a = 1)
    {s : M} : s ∈ zpowers a ↔ s = 1 ∨ s = a := by
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha
  constructor
  · rintro ⟨k, rfl⟩
    show a ^ k = 1 ∨ a ^ k = a
    rw [← zpow_mod_orderOf, hord]
    have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases h2 with h2 | h2
    · left; rw [h2]; simp
    · right; rw [h2]; simp
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem mem_zpowers_z0 {s : J2Syl} : s ∈ zpowers z0 ↔ s = 1 ∨ s = z0 :=
  mem_zpowers_of_sq_eq_one z0_ne_one z0_sq

theorem ker_permRep : permRep.ker = zpowers z0 := by
  ext s
  rw [MonoidHom.mem_ker, permRep_eq_one_iff, mem_zpowers_z0]

theorem card_range_permRep : Nat.card permRep.range = 64 := by
  have h := Subgroup.card_ker_mul_card_range permRep
  have hz : Nat.card (zpowers z0) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact z0_sq) z0_ne_one
  rw [ker_permRep, hz, card_J2Syl] at h
  omega

theorem range_permRep_le : permRep.range ≤ alternatingGroup (Fin 8) := by
  rintro _ ⟨s, rfl⟩
  exact Equiv.Perm.mem_alternatingGroup.2 (sign_permRep s)

theorem card_A8_factorization :
    (Nat.card (alternatingGroup (Fin 8))).factorization 2 = 6 := by
  have h1 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h1, Nat.factorization_def _ Nat.prime_two]
  have h2 : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
  rw [h2, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
  have h3 : padicValNat 2 315 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  omega

@[expose] def imgA8 : Subgroup (alternatingGroup (Fin 8)) :=
  permRep.range.subgroupOf (alternatingGroup (Fin 8))

theorem card_imgA8 :
    Nat.card imgA8 = 2 ^ ((Nat.card (alternatingGroup (Fin 8))).factorization 2) := by
  rw [card_A8_factorization]
  have := Nat.card_congr (Subgroup.subgroupOfEquivOfLe range_permRep_le).toEquiv
  unfold imgA8
  rw [this, card_range_permRep]
  norm_num

@[expose] def sylA8 : Sylow 2 (alternatingGroup (Fin 8)) := Sylow.ofCard imgA8 card_imgA8

instance instNormalZpowersZ0 : (zpowers z0).Normal := by
  rw [← ker_permRep]; infer_instance

theorem isA8Type_quotient : IsA8Type (J2Syl ⧸ zpowers z0) :=
  ⟨sylA8, ⟨(QuotientGroup.quotientMulEquivOfEq ker_permRep.symm).trans
    ((QuotientGroup.quotientKerEquivRange permRep).trans
      (Subgroup.subgroupOfEquivOfLe range_permRep_le).symm)⟩⟩

end J2Syl

end CFSG.GH74.Uniqueness.SU.SU5

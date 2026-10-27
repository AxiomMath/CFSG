module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermBound

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup

theorem exists_card_four_of_commuting_involutions {G : Type*} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b) {P : Subgroup G} (haP : a ∈ P) (hbP : b ∈ P) : 4 ∣ Nat.card P := by
  have f1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have f2 : b * (a * b) = a := by rw [hab, ← mul_assoc, hb, one_mul]
  have f3 : (a * b) * a = b := by rw [hab, mul_assoc, ha, mul_one]
  have f4 : (a * b) * b = a := by rw [mul_assoc, hb, mul_one]
  have f5 : (a * b) * (a * b) = 1 := by rw [mul_assoc, f2, ha]
  have hba : b * a = a * b := hab.symm
  let V : Subgroup G :=
    { carrier := {1, a, b, a * b}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          simp [ha, hb, hba, f1, f2, f3, f4, f5]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl
        · simp
        · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
        · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
        · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right f5))) }
  have hVP : V ≤ P := by
    intro x hx
    simp only [V, Subgroup.mem_mk] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact P.one_mem
    · exact haP
    · exact hbP
    · exact P.mul_mem haP hbP
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact (inv_eq_of_mul_eq_one_right ha).symm)
  have hab2 : a ≠ a * b := fun h => hb1 (by
    have : a * 1 = a * b := by rw [mul_one]; exact h
    exact (mul_left_cancel this).symm)
  have hab3 : b ≠ a * b := fun h => ha1 (by
    have : 1 * b = a * b := by rw [one_mul]; exact h
    exact (mul_right_cancel this).symm)
  have hcard : Nat.card V = 4 := by
    show Nat.card ↥(V : Set G) = 4
    rw [Nat.card_coe_set_eq]
    show ({1, a, b, a * b} : Set G).ncard = 4
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hab3]
    · simp [hne, hab2]
    · simp [ha1.symm, hb1.symm, hab1.symm]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hVP

theorem card_eq_two_of_normalized_involution {Q : Type*} [Fintype Q] [DecidableEq Q]
    (hQ : 0 < Fintype.card Q) (P : Subgroup (Perm Q)) {θ : Perm Q} (hθP : θ ∈ P)
    (hθ2 : θ * θ = 1) (hθ : ∀ x, θ x ≠ x)
    (hnorm : ∀ g ∈ alternatingGroup Q, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (h4 : ¬ 4 ∣ Nat.card P) :
    Fintype.card Q = 2 := by
  classical
  obtain ⟨x⟩ := Fintype.card_pos_iff.1 hQ
  have hθθ : ∀ y, θ (θ y) = y := fun y => by
    simpa [Perm.mul_apply] using congrArg (fun e : Perm Q => e y) hθ2
  by_contra hne
  have hxb : x ≠ θ x := (hθ x).symm
  have hcard2 : 2 ≤ Fintype.card Q := by
    have h2 : ({x, θ x} : Finset Q).card = 2 := Finset.card_pair hxb
    calc 2 = ({x, θ x} : Finset Q).card := h2.symm
      _ ≤ Fintype.card Q := Finset.card_le_univ _
  obtain ⟨c, hcx, hcb⟩ : ∃ c : Q, c ≠ x ∧ c ≠ θ x := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset Q) ⊆ {x, θ x} := fun y _ => by
      by_cases h : y = x
      · simp [h]
      · simp [hcon y h]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Finset.card_pair hxb] at this
    omega
  obtain ⟨b, hb⟩ : ∃ b, b = θ x := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = θ c := ⟨_, rfl⟩
  rw [← hb] at hxb hcb
  have hθx : θ x = b := hb.symm
  have hθb : θ b = x := by rw [hb, hθθ]
  have hθc : θ c = d := hd.symm
  have hθd : θ d = c := by rw [hd, hθθ]
  have hdc : d ≠ c := by rw [hd]; exact hθ c
  have hdx : d ≠ x := fun h => hcb (by
    have : θ d = θ x := by rw [h]
    rw [hθd, hθx] at this
    exact this)
  have hdb : d ≠ b := fun h => hcx (by
    have : θ d = θ b := by rw [h]
    rw [hθd, hθb] at this
    exact this)
  have hbx := hxb.symm
  have hbc := hcb.symm
  have hxc := hcx.symm
  have hcd := hdc.symm
  have hxd := hdx.symm
  have hbd := hdb.symm
  set g : Perm Q := swap x b * swap b c with hg
  have hgA : g ∈ alternatingGroup Q := by
    rw [Perm.mem_alternatingGroup, hg, Perm.sign_mul, Perm.sign_swap hxb, Perm.sign_swap hbc]
    decide
  have gx : g x = b := by
    rw [hg, Perm.mul_apply, swap_apply_of_ne_of_ne hxb hxc, swap_apply_left]
  have gb : g b = c := by
    rw [hg, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hcx hcb]
  have gc : g c = x := by
    rw [hg, Perm.mul_apply, swap_apply_right, swap_apply_right]
  have gd : g d = d := by
    rw [hg, Perm.mul_apply, swap_apply_of_ne_of_ne hdb hdc, swap_apply_of_ne_of_ne hdx hdb]
  have hθ1 : θ ≠ 1 := fun h => hθ x (by rw [h]; rfl)
  by_cases h5 : 5 ≤ Fintype.card Q
  ·
    have hsimple : IsSimpleGroup (alternatingGroup Q) :=
      alternatingGroup.isSimpleGroup (by rwa [Nat.card_eq_fintype_card])
    let Pa : Subgroup ↥(alternatingGroup Q) :=
      (P ⊓ alternatingGroup Q).subgroupOf (alternatingGroup Q)
    have hPa : Pa.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hnorm g g.2 n hn.1, (g * n * g⁻¹ : ↥(alternatingGroup Q)).2⟩⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Pa with hbot | htop
    ·
      have hPA : ∀ p ∈ P, p ∈ alternatingGroup Q → p = 1 := fun p hp hpA => by
        have hmem : (⟨p, hpA⟩ : ↥(alternatingGroup Q)) ∈ Pa := by
          rw [Subgroup.mem_subgroupOf]
          exact ⟨hp, hpA⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      have hθodd : sign θ = -1 := by
        rcases Int.units_eq_one_or (sign θ) with h | h
        · exact absurd (hPA θ hθP (Perm.mem_alternatingGroup.2 h)) hθ1
        · exact h
      have hqP : g * θ * g⁻¹ ∈ P := hnorm g hgA θ hθP
      have hqsign : sign (g * θ * g⁻¹) = -1 := by
        rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_comm (sign g) (sign θ), mul_assoc,
          Int.units_mul_self, mul_one, hθodd]
      have hsq : sign (θ⁻¹ * (g * θ * g⁻¹)) = 1 := by
        rw [Perm.sign_mul, Perm.sign_inv, hθodd, hqsign]
        decide
      have h1 : θ⁻¹ * (g * θ * g⁻¹) = 1 :=
        hPA _ (P.mul_mem (P.inv_mem hθP) hqP) (Perm.mem_alternatingGroup.2 hsq)
      have hq : g * θ * g⁻¹ = θ := (inv_mul_eq_one.1 h1).symm
      have hcomm : g * θ = θ * g := mul_inv_eq_iff_eq_mul.1 hq
      have := congrArg (fun e : Perm Q => e x) hcomm
      simp only [Perm.mul_apply, hθx, gb, gx, hθb] at this
      exact hcx this
    ·
      have hAP : alternatingGroup Q ≤ P := fun g hg => by
        have hmem : (⟨g, hg⟩ : ↥(alternatingGroup Q)) ∈ Pa := by
          rw [htop]
          exact Subgroup.mem_top _
        exact ((Subgroup.mem_subgroupOf).1 hmem).1
      have hdvd : Nat.card (alternatingGroup Q) ∣ Nat.card P := Subgroup.card_dvd_of_le hAP
      have hA2 := card_alternatingGroup_mul_two (β := Q) (by rw [Nat.card_eq_fintype_card]; omega)
      rw [Nat.card_eq_fintype_card (α := Q)] at hA2
      have h8 : 8 ∣ (Fintype.card Q).factorial :=
        dvd_trans (by decide : 8 ∣ Nat.factorial 4) (Nat.factorial_dvd_factorial (by omega))
      have h4A : 4 ∣ Nat.card (alternatingGroup Q) := by omega
      exact h4 (dvd_trans h4A hdvd)
  ·
    have hq4 : ({x, b, c, d} : Finset Q).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hxb, hxc, hxd]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
    have h4le : 4 ≤ Fintype.card Q := by
      have := Finset.card_le_univ ({x, b, c, d} : Finset Q)
      omega
    have hall : (Finset.univ : Finset Q) = {x, b, c, d} := by
      symm
      apply Finset.eq_univ_of_card
      rw [hq4]
      omega
    have huniv : ∀ y : Q, y = x ∨ y = b ∨ y = c ∨ y = d := fun y => by
      have : y ∈ ({x, b, c, d} : Finset Q) := by rw [← hall]; exact Finset.mem_univ y
      simpa using this
    have hθeq : θ = swap x b * swap c d := by
      refine Equiv.ext fun y => ?_
      rcases huniv y with rfl | rfl | rfl | rfl <;>
        simp [Perm.mul_apply, swap_apply_def, hθx, hθb, hθc, hθd, hxc, hxd, hbc, hbd, hcx, hcb,
          hdx, hdb]
    set θ' : Perm Q := swap b c * swap x d with hθ'
    have hθ'g : θ' * g = g * θ := by
      refine Equiv.ext fun y => ?_
      rcases huniv y with rfl | rfl | rfl | rfl <;>
        simp [Perm.mul_apply, swap_apply_def, hθ', gx, gb, gc, gd, hθx, hθb, hθc, hθd, hxb, hxc,
          hbx, hbd, hcx, hcd, hdb, hdc]
    have hθ'eq : θ' = g * θ * g⁻¹ := (eq_mul_inv_iff_mul_eq.2 hθ'g)
    have hθ'P : θ' ∈ P := by rw [hθ'eq]; exact hnorm g hgA θ hθP
    have hθ'2 : θ' * θ' = 1 := by
      rw [hθ'eq]
      calc g * θ * g⁻¹ * (g * θ * g⁻¹) = g * (θ * θ) * g⁻¹ := by group
        _ = 1 := by rw [hθ2]; group
    have hθ'1 : θ' ≠ 1 := fun h => hθ1 (by
      rw [h] at hθ'eq
      have : θ = g⁻¹ * 1 * g := by
        rw [hθ'eq]
        group
      rw [this]
      group)
    have hθθ' : θ ≠ θ' := fun h => hbd (by
      have := congrArg (fun e : Perm Q => e x) h
      simp [hθ', Perm.mul_apply, swap_apply_def, hθx, hbd, hdb, hdc] at this)
    have hcomm : θ * θ' = θ' * θ := by
      refine Equiv.ext fun y => ?_
      rcases huniv y with rfl | rfl | rfl | rfl <;>
        simp [Perm.mul_apply, swap_apply_def, hθ', hθx, hθb, hθc, hθd, hxb, hxc, hbx, hbd, hcx,
          hcd, hdb, hdc]
    exact h4 (exists_card_four_of_commuting_involutions hθ2 hθ'2 hcomm hθ1 hθ'1 hθθ' hθP hθ'P)

end CFSG.OddStandard.Solomon75

module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6.A5Aux

open Equiv Equiv.Perm Subgroup

theorem mul_self_eq_one_of_pow_four (x : alternatingGroup (Fin 5)) (h : x ^ 4 = 1) :
    x * x = 1 := by
  have key : ∀ x : alternatingGroup (Fin 5), x ^ 4 = 1 → x * x = 1 := by decide +kernel
  exact key x h

theorem exists_unique_fixed (a : alternatingGroup (Fin 5)) (ha : a ≠ 1) (ha2 : a * a = 1) :
    ∃ x0 : Fin 5, a.1 x0 = x0 ∧ ∀ y : Fin 5, a.1 y = y → y = x0 := by
  have key : ∀ a : alternatingGroup (Fin 5), a ≠ 1 → a * a = 1 →
      ∃ x0 : Fin 5, a.1 x0 = x0 ∧ ∀ y : Fin 5, a.1 y = y → y = x0 := by decide +kernel
  exact key a ha ha2

theorem card_invFix (x0 : Fin 5) :
    (Finset.univ.filter (fun y : alternatingGroup (Fin 5) => y.1 x0 = x0 ∧ y * y = 1)).card =
      4 := by
  have key : ∀ x0 : Fin 5, (Finset.univ.filter (fun y : alternatingGroup (Fin 5) =>
      y.1 x0 = x0 ∧ y * y = 1)).card = 4 := by decide +kernel
  exact key x0

theorem card_stab (x0 : Fin 5) :
    (Finset.univ.filter (fun y : alternatingGroup (Fin 5) => y.1 x0 = x0)).card = 12 := by
  have key : ∀ x0 : Fin 5, (Finset.univ.filter (fun y : alternatingGroup (Fin 5) =>
      y.1 x0 = x0)).card = 12 := by decide +kernel
  exact key x0

theorem centralizer_invFix (x0 : Fin 5) (x : alternatingGroup (Fin 5))
    (h : ∀ y : alternatingGroup (Fin 5), y.1 x0 = x0 → y * y = 1 → x * y = y * x) :
    x.1 x0 = x0 ∧ x * x = 1 := by
  have key : ∀ x0 : Fin 5, ∀ x : alternatingGroup (Fin 5),
      (∀ y : alternatingGroup (Fin 5), y.1 x0 = x0 → y * y = 1 → x * y = y * x) →
        x.1 x0 = x0 ∧ x * x = 1 := by decide +kernel
  exact key x0 x h

theorem odd_involution_moves (σ : Perm (Fin 5)) (hσ2 : σ * σ = 1) (hσ : sign σ = -1)
    (x0 : Fin 5) :
    ∃ x : alternatingGroup (Fin 5), x.1 * σ = σ * x.1 ∧ x.1 x0 ≠ x0 := by
  have key : ∀ σ : Perm (Fin 5), σ * σ = 1 → sign σ = -1 → ∀ x0 : Fin 5,
      ∃ x : alternatingGroup (Fin 5), x.1 * σ = σ * x.1 ∧ x.1 x0 ≠ x0 := by decide +kernel
  exact key σ hσ2 hσ x0

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem factorization_sixty : (60 : ℕ).factorization 2 = 2 := by
  have h : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem mul_self_eq_one_of_mem {P : Subgroup (alternatingGroup (Fin 5))}
    (hP : Nat.card P = 4) {y : alternatingGroup (Fin 5)} (hy : y ∈ P) : y * y = 1 := by
  apply mul_self_eq_one_of_pow_four
  have h1 : (⟨y, hy⟩ : P) ^ Nat.card P = 1 := pow_card_eq_one'
  rw [hP] at h1
  simpa using congrArg Subtype.val h1

theorem exists_fixed_point_of_card_four {P : Subgroup (alternatingGroup (Fin 5))}
    (hP : Nat.card P = 4) :
    ∃ x0 : Fin 5, ∀ y : alternatingGroup (Fin 5), y ∈ P ↔ (y.1 x0 = x0 ∧ y * y = 1) := by
  have hsq : ∀ y ∈ P, y * y = 1 := fun y hy => mul_self_eq_one_of_mem hP hy
  have hne : P ≠ ⊥ := by
    intro h
    have := Subgroup.card_eq_one.mpr h
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨x0, hx0, huniq⟩ := exists_unique_fixed a.1 (fun h => ha (Subtype.ext h))
    (hsq a.1 a.2)
  have hsub : ∀ y ∈ P, y.1 x0 = x0 ∧ y * y = 1 := by
    intro y hy
    refine ⟨?_, hsq y hy⟩
    have hcomm : y * a.1 = a.1 * y := by
      have h1 := hsq (y * a.1) (P.mul_mem hy a.2)
      have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
      have ha' : a.1⁻¹ = a.1 := inv_eq_of_mul_eq_one_right (hsq a.1 a.2)
      have h2 : (y * a.1)⁻¹ = y * a.1 := inv_eq_of_mul_eq_one_right h1
      rw [mul_inv_rev, hy', ha'] at h2
      exact h2.symm
    apply huniq
    have := congrArg (fun g : alternatingGroup (Fin 5) => g.1 x0) hcomm
    simp only [Subgroup.coe_mul, Perm.mul_apply] at this
    rw [hx0] at this
    exact this.symm
  have hset : (P : Set (alternatingGroup (Fin 5))) =
      {y : alternatingGroup (Fin 5) | y.1 x0 = x0 ∧ y * y = 1} := by
    apply Set.eq_of_subset_of_ncard_le
    · exact fun y hy => hsub y hy
    · have h1 : (P : Set (alternatingGroup (Fin 5))).ncard = 4 := by
        rw [← Nat.card_coe_set_eq]; exact hP
      have h2 : {y : alternatingGroup (Fin 5) | y.1 x0 = x0 ∧ y * y = 1}.ncard = 4 := by
        rw [Set.ncard_eq_toFinset_card']
        simpa using card_invFix x0
      omega
    · exact Set.toFinite _
  exact ⟨x0, fun y => by
    have := Set.ext_iff.mp hset y
    simpa using this⟩

theorem centralizer_le_of_card_four {P : Subgroup (alternatingGroup (Fin 5))}
    (hP : Nat.card P = 4) :
    centralizer (P : Set (alternatingGroup (Fin 5))) ≤ P := by
  obtain ⟨x0, hx0⟩ := exists_fixed_point_of_card_four hP
  intro x hx
  have hcomm : ∀ y : alternatingGroup (Fin 5), y.1 x0 = x0 → y * y = 1 → x * y = y * x := by
    intro y h1 h2
    exact ((mem_centralizer_iff.mp hx) y ((hx0 y).mpr ⟨h1, h2⟩)).symm
  exact (hx0 x).mpr (centralizer_invFix x0 x hcomm)

theorem stabilizer_le_normalizer {P : Subgroup (alternatingGroup (Fin 5))} {x0 : Fin 5}
    (hx0 : ∀ y : alternatingGroup (Fin 5), y ∈ P ↔ (y.1 x0 = x0 ∧ y * y = 1)) :
    MulAction.stabilizer (alternatingGroup (Fin 5)) x0 ≤ normalizer (P : Set _) := by
  intro g hg
  have hg' : g.1 x0 = x0 := MulAction.mem_stabilizer_iff.mp hg
  have hgi : g.1⁻¹ x0 = x0 := by
    rw [Perm.inv_eq_iff_eq]; exact hg'.symm
  rw [mem_normalizer_iff]
  intro h
  rw [hx0, hx0]
  have e1 : (g * h * g⁻¹).1 x0 = g.1 (h.1 (x0)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
    rw [hgi]
  have e2 : (g * h * g⁻¹) * (g * h * g⁻¹) = g * (h * h) * g⁻¹ := by group
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [h1, hg']
    · rw [h2]; group
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : g.1 (h.1 x0) = g.1 x0 := by rw [h1, hg']
      exact g.1.injective this
    · have := congrArg (fun t => g⁻¹ * t * g) h2
      simpa [mul_assoc] using this

theorem eq_top_of_normalizer_le {P : Subgroup (alternatingGroup (Fin 5))} (hP : Nat.card P = 4)
    {σ : Perm (Fin 5)} (hσ2 : σ * σ = 1) (hσ : sign σ = -1)
    {D : Subgroup (alternatingGroup (Fin 5))} (hN : normalizer (P : Set _) ≤ D)
    (hC : ∀ x : alternatingGroup (Fin 5), x.1 * σ = σ * x.1 → x ∈ D) : D = ⊤ := by
  obtain ⟨x0, hx0⟩ := exists_fixed_point_of_card_four hP
  have hSD : MulAction.stabilizer (alternatingGroup (Fin 5)) x0 ≤ D :=
    (stabilizer_le_normalizer hx0).trans hN
  have hcard : Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) x0) = 12 := by
    have e : ↥(MulAction.stabilizer (alternatingGroup (Fin 5)) x0) ≃
        {y : alternatingGroup (Fin 5) // y.1 x0 = x0} :=
      Equiv.subtypeEquivRight (fun y => MulAction.mem_stabilizer_iff)
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_stab x0
  have hdvd1 : 12 ∣ Nat.card D := hcard ▸ Subgroup.card_dvd_of_le hSD
  have hdvd2 : Nat.card D ∣ 60 :=
    card_alternatingGroup_five ▸ Subgroup.card_subgroup_dvd_card D
  have h12 : Nat.card D = 12 ∨ Nat.card D = 60 := by
    obtain ⟨k, hk⟩ := hdvd1
    have hle : Nat.card D ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd2
    have hpos : 0 < Nat.card D := Nat.card_pos
    rw [hk] at hdvd2 hle hpos
    have hk5 : k ≤ 5 := by omega
    interval_cases k <;> omega
  rcases h12 with h | h
  · exfalso
    have hEq : MulAction.stabilizer (alternatingGroup (Fin 5)) x0 = D :=
      Subgroup.eq_of_le_of_card_ge hSD (by rw [h, hcard])
    obtain ⟨x, hxσ, hx0'⟩ := odd_involution_moves σ hσ2 hσ x0
    have hxD : x ∈ D := hC x hxσ
    rw [← hEq] at hxD
    exact hx0' (MulAction.mem_stabilizer_iff.mp hxD)
  · exact (Subgroup.card_eq_iff_eq_top D).mp (by rw [h, card_alternatingGroup_five])

end CFSG.GH74.Uniqueness.SU.K.R6.A5Aux

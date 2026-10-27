module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.KS.SylowLab

open Subgroup

theorem exists_conj_mem_of_card {G : Type*} [Group G] {L S : Subgroup G} [Finite L]
    (hSL : S ≤ L) {p k m : ℕ} (hp : p.Prime) (hS : Nat.card S = p ^ k)
    (hL : Nat.card L = p ^ k * m) (hm : ¬ p ∣ m) {z : G} (hz : z ∈ L) (hzp : z ^ p = 1) :
    ∃ g ∈ L, g⁻¹ * z * g ∈ S := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hfac : (Nat.card L).factorization p = k := by
    rw [hL, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
      add_zero]
  have hS' : Nat.card (S.subgroupOf L) = p ^ (Nat.card L).factorization p := by
    rw [hfac, ← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSL).toEquiv
  let P : Sylow p L := Sylow.ofCard (S.subgroupOf L) hS'
  set y : L := ⟨z, hz⟩
  have hy : y ^ p = 1 := Subtype.ext (by simpa [y] using hzp)
  have hord : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hy
  have hpg : IsPGroup p (zpowers y) := by
    rcases (Nat.dvd_prime hp).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L Q P
  have hyQ : y ∈ (Q : Subgroup L) := hQ (mem_zpowers y)
  have hmem : g * y * g⁻¹ ∈ (P : Subgroup L) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.2 (by
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hyQ)
  refine ⟨((g⁻¹ : L) : G), (g⁻¹ : L).2, ?_⟩
  have h1 : (g * y * g⁻¹ : L) ∈ S.subgroupOf L := hmem
  rw [mem_subgroupOf] at h1
  simpa [y, mul_assoc] using h1

theorem mem_closure_pair {G : Type*} [Group G] {a b x : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (hx : x ∈ closure ({a, b} : Set G)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have ha' : ∀ y : G, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba' : ∀ y : G, b * (a * y) = a * (b * y) := fun y => by
    rw [← mul_assoc, ← hab, mul_assoc]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [mul_assoc, ha, hb, ha', hba', hab.symm]
  | inv x _ hx =>
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb, ← hab]

variable {n : ℕ}

@[expose] def labStab (lab : Fin n → ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ p, lab (g p) = lab p}
  mul_mem' {a b} ha hb p := by
    rw [Equiv.Perm.mul_apply, ha, hb]
  one_mem' p := rfl
  inv_mem' {a} ha p := by
    have := ha (a⁻¹ p)
    simpa using this.symm

theorem mem_labStab {lab : Fin n → ℕ} {g : Equiv.Perm (Fin n)} :
    g ∈ labStab lab ↔ ∀ p, lab (g p) = lab p := Iff.rfl

theorem conj_mem_labStab {lab : Fin n → ℕ} {x : Equiv.Perm (Fin n)}
    (hx : ∀ u v, lab u = lab v → lab (x u) = lab (x v)) {k : Equiv.Perm (Fin n)}
    (hk : k ∈ labStab lab) : x * k * x⁻¹ ∈ labStab lab := by
  intro p
  have := hx (k (x⁻¹ p)) (x⁻¹ p) (hk _)
  simpa [Equiv.Perm.mul_apply] using this

theorem mem_normalizer_labStab {lab : Fin n → ℕ} {x : Equiv.Perm (Fin n)}
    (hx : ∀ u v, lab u = lab v → lab (x u) = lab (x v))
    (hxi : ∀ u v, lab u = lab v → lab (x⁻¹ u) = lab (x⁻¹ v)) :
    x ∈ normalizer (labStab lab : Set (Equiv.Perm (Fin n))) := by
  rw [mem_normalizer_iff]
  intro k
  refine ⟨conj_mem_labStab hx, fun hk => ?_⟩
  have := conj_mem_labStab hxi hk
  simpa [mul_assoc] using this

end CFSG.KS.SylowLab

end

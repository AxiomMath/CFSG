module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.QuaternionCentralizers

public section

namespace CFSG.ComponentClassification.SmallLocal

open DihedralGroup

theorem card_le_of_forall_mem_finset {X : Type*} [Group X] {E : Subgroup X} (F : Finset X)
    (h : ∀ x ∈ E, x ∈ F) : Nat.card E ≤ F.card := by
  have h1 := Nat.card_le_card_of_injective (fun x : E => (⟨x, h x x.2⟩ : F))
    fun a b hab => Subtype.ext (by simpa using hab)
  rwa [Nat.card_eq_finsetCard] at h1

theorem dihedral_card_le_four_of_mul_self_eq_one {m : ℕ} [NeZero m]
    (E : Subgroup (DihedralGroup (2 * m))) (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  classical
  have hr : ∀ j : ZMod (2 * m), r j ∈ E → j = 0 ∨ j = (m : ZMod (2 * m)) := by
    intro j hj
    have h := hE _ hj
    rw [r_mul_r, one_def, r.injEq, ← two_mul] at h
    exact (CFSG.GroupTheory.two_mul_eq_zero_iff_zmod j).mp h
  by_cases hs : ∃ i, sr i ∈ E
  · obtain ⟨i, hi⟩ := hs
    have hsub : ∀ x ∈ E,
        x ∈ ({r 0, r (m : ZMod (2 * m)), sr i, sr (i + (m : ZMod (2 * m)))} : Finset _) := by
      intro x hx
      cases x with
      | r j => rcases hr j hx with rfl | rfl <;> simp
      | sr j =>
        rcases hr (j - i) (by rw [← sr_mul_sr]; exact mul_mem hi hx) with h | h
        · rw [sub_eq_zero.mp h]
          simp
        · rw [sub_eq_iff_eq_add.mp h, add_comm]
          simp
    exact (card_le_of_forall_mem_finset _ hsub).trans Finset.card_le_four
  · push Not at hs
    have hsub : ∀ x ∈ E, x ∈ ({r 0, r (m : ZMod (2 * m))} : Finset _) := by
      intro x hx
      cases x with
      | r j => rcases hr j hx with rfl | rfl <;> simp
      | sr j => exact absurd hx (hs j)
    exact (card_le_of_forall_mem_finset _ hsub).trans (Finset.card_le_two.trans (by norm_num))

theorem not_injective_quaternion_dihedral {n : ℕ} (φ : QuaternionGroup 2 →* DihedralGroup n) :
    ¬ Function.Injective φ := by
  intro hφ
  have hrot : ∀ x : QuaternionGroup 2, orderOf x = 4 → ∃ i, φ x = r i := by
    intro x hx
    have h := orderOf_injective φ hφ x
    rw [hx] at h
    cases hφx : φ x with
    | r i => exact ⟨i, rfl⟩
    | sr i =>
      rw [hφx, orderOf_sr] at h
      omega
  obtain ⟨i, hi⟩ := hrot (QuaternionGroup.a 1) (by rw [QuaternionGroup.orderOf_a_one])
  obtain ⟨j, hj⟩ := hrot (QuaternionGroup.xa 0) (QuaternionGroup.orderOf_xa 0)
  have hcomm : φ (QuaternionGroup.a 1 * QuaternionGroup.xa 0) =
      φ (QuaternionGroup.xa 0 * QuaternionGroup.a 1) := by
    rw [map_mul, map_mul, hi, hj, r_mul_r, r_mul_r, add_comm]
  have h := hφ hcomm
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa.injEq] at h
  exact absurd h (by decide)

theorem exists_injective_hom_of_isPGroup {G : Type*} [Group G] [Finite G] {n : ℕ}
    (P : Sylow 2 G) (e : (P : Subgroup G) ≃* DihedralGroup n) {E : Subgroup G}
    (hE : IsPGroup 2 E) : ∃ f : E →* DihedralGroup n, Function.Injective f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  exact ⟨e.toMonoidHom.comp ((Sylow.equiv Q P).toMonoidHom.comp (Subgroup.inclusion hEQ)),
    e.injective.comp ((Sylow.equiv Q P).injective.comp (Subgroup.inclusion_injective hEQ))⟩

theorem dihedral_sylow_rank_and_quaternion_obstructions {G : Type*} [Group G] [Finite G] {s : ℕ}
    (hs : 2 ≤ s)
    (hP : ∃ P : Sylow 2 G, Nonempty ((P : Subgroup G) ≃* DihedralGroup (2 ^ (s - 1)))) :
    pRank 2 G ≤ 2 ∧ ¬ ∃ R : Subgroup G, Nonempty (R ≃* QuaternionGroup 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, ⟨e⟩⟩ := hP
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ (s - 1) = 2 * m :=
    ⟨2 ^ (s - 2), by rw [← pow_succ']; congr 1; omega⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have : NeZero m := ⟨hm0⟩
  rw [hm] at e
  refine ⟨csSup_le' ?_, ?_⟩
  · rintro r ⟨A, hA, hcard⟩
    obtain ⟨f, hf⟩ := exists_injective_hom_of_isPGroup P e (IsElementaryAbelian.isPGroup 2 A)
    have hsq : ∀ x ∈ f.range, x * x = 1 := by
      rintro _ ⟨a, rfl⟩
      rw [← map_mul, ← pow_two, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a, map_one]
    have h4 := dihedral_card_le_four_of_mul_self_eq_one f.range hsq
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, hcard] at h4
    by_contra hr
    have h8 : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rintro ⟨R, ⟨eR⟩⟩
    have hRp : IsPGroup 2 R := IsPGroup.of_card (n := 3) (by
      rw [Nat.card_congr eR.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      norm_num)
    obtain ⟨f, hf⟩ := exists_injective_hom_of_isPGroup P e hRp
    exact not_injective_quaternion_dihedral (f.comp eR.symm.toMonoidHom)
      (hf.comp eR.symm.injective)

end CFSG.ComponentClassification.SmallLocal

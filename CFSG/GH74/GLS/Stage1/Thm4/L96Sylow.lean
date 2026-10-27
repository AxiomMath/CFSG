module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

theorem exists_elemAbelian_of_odd_kernel {T X : Type*} [Group T] [Finite T] [Group X] (f : T →* X)
    (hker : Odd (Nat.card f.ker)) (E : Subgroup X) (hE : E ≤ f.range)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1) :
    ∃ E' : Subgroup T, (∀ a ∈ E', ∀ b ∈ E', a * b = b * a) ∧ (∀ a ∈ E', a ^ 2 = 1) ∧
      Nat.card E ≤ Nat.card E' := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup T := E.comap f
  have hKP : f.ker ≤ P := MonoidHom.ker_le_comap f E
  have hrfin : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hEfin : Finite E :=
    Finite.of_injective (Subgroup.inclusion hE) (Subgroup.inclusion_injective hE)
  have hEp : IsPGroup 2 E := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg : g ^ 2 = 1 := Subtype.ext (hE2 g g.2)
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg) with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have hPcard : Nat.card P = Nat.card f.ker * Nat.card E := by
    have h1 := Subgroup.card_mul_index (f.domRestrict P).ker
    rw [Subgroup.index_ker, MonoidHom.domRestrict_range, Subgroup.map_comap_eq,
      inf_of_le_right hE, MonoidHom.ker_domRestrict] at h1
    rw [← h1]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv
  obtain ⟨Q⟩ : Nonempty (Sylow 2 P) := Sylow.nonempty
  have hQcard : Nat.card Q = Nat.card E := by
    have hker0 : Nat.card f.ker ≠ 0 := Nat.card_pos.ne'
    have hE0 : Nat.card E ≠ 0 := Nat.card_pos.ne'
    have hodd : ¬ 2 ∣ Nat.card f.ker := fun h =>
      (Nat.not_even_iff_odd.mpr hker) (even_iff_two_dvd.mpr h)
    rw [Sylow.card_eq_multiplicity Q, hPcard, Nat.factorization_mul hker0 hE0,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd, zero_add, hk,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hE'p : IsPGroup 2 (Q.map P.subtype) := Q.2.map P.subtype
  have key : ∀ x ∈ Q.map P.subtype, f x = 1 → x = 1 := by
    intro x hx hfx
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hE'p ⟨x, hx⟩
    have hx1 : orderOf x = 2 ^ j := by rwa [Subgroup.orderOf_mk] at hj
    have hdvd : orderOf x ∣ Nat.card f.ker := by
      have := orderOf_dvd_natCard (⟨x, MonoidHom.mem_ker.mpr hfx⟩ : f.ker)
      rwa [Subgroup.orderOf_mk] at this
    rw [hx1] at hdvd
    have hj0 : j = 0 := by
      by_contra hj0
      exact (Nat.not_even_iff_odd.mpr hker)
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 hj0).trans hdvd))
    rw [hj0, pow_zero] at hx1
    exact orderOf_eq_one_iff.mp hx1
  have hfE : ∀ a ∈ Q.map P.subtype, f a ∈ E := by
    intro a ha
    obtain ⟨q, _, rfl⟩ := Subgroup.mem_map.mp ha
    exact q.2
  refine ⟨Q.map P.subtype, ?_, ?_, ?_⟩
  · intro a ha b hb
    have h1 := key (a * b * (b * a)⁻¹)
      (mul_mem (mul_mem ha hb) (inv_mem (mul_mem hb ha)))
      (by rw [map_mul, map_mul, map_inv, map_mul, hEc _ (hfE a ha) _ (hfE b hb), mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  · intro a ha
    exact key (a ^ 2) (pow_mem ha 2) (by rw [map_pow, hE2 _ (hfE a ha)])
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hQcard]

end CFSG.GH74.GLS.Stage1.Thm4.L96

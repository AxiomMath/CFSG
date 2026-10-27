module

public import CFSG.LargeExtraspecial.S14C12TOrd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

namespace SmithAlt

open Subgroup Equiv CFSG.Open

theorem not_thirteen_dvd_card_M {G : Type} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) : ¬ 13 ∣ Nat.card S.M := by
  obtain ⟨hk, hM⟩ := card_M_of_U6 S hw hU
  rw [hM]
  rcases eq_of_dvd_six hk with hk | hk | hk | hk <;> rw [hk] <;> norm_num

theorem thirteen_dvd_card_centralizer {m : ℕ} (hm : 37 ≤ m) {g : Perm (Fin m)}
    (hg : orderOf g = 2) : 13 ∣ Nat.card (centralizer {g}) := by
  have hp : (orderOf g).Prime := hg ▸ Nat.prime_two
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order hp
  rw [hg] at hk
  have hle := Perm.sum_cycleType_le g
  rw [hk, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hle
  rw [Perm.nat_card_centralizer, hk]
  simp only [Multiset.sum_replicate, Multiset.prod_replicate, Fintype.card_fin, smul_eq_mul,
    Multiset.toFinset_replicate, Nat.add_one_ne_zero, ↓reduceIte, Finset.prod_singleton,
    Multiset.count_replicate_self]
  have h13 : Nat.Prime 13 := by norm_num
  by_cases hk13 : 13 ≤ k + 1
  · exact dvd_mul_of_dvd_right ((h13.dvd_factorial).mpr hk13) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ((h13.dvd_factorial).mpr (by omega)) _) _

theorem sign_eq_one_of_orderOf {m : ℕ} {h : Perm (Fin m)} (hh : orderOf h = 13) :
    Perm.sign h = 1 := by
  have h1 : Perm.sign h ^ 13 = 1 := by rw [← map_pow, ← hh, pow_orderOf_eq_one, map_one]
  rw [show (13 : ℕ) = 2 * 6 + 1 from rfl, pow_succ, pow_mul, Int.units_sq, one_pow,
    one_mul] at h1
  exact h1

theorem false_of_mulEquiv_alternatingGroup {G : Type} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {m : ℕ}
    (e : G ≃* alternatingGroup (Fin m)) : False := by
  have h2 := factorization_card_of_U6 S hw hU
  have h36 : 2 ^ 36 ∣ Nat.card G :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mpr (by omega)
  by_cases hm : m ≤ 36
  · have h1 : Nat.card G ∣ Nat.factorial 36 := by
      rw [Nat.card_congr e.toEquiv]
      refine (Subgroup.card_subgroup_dvd_card _).trans ?_
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact Nat.factorial_dvd_factorial hm
    exact absurd (h36.trans h1) (by decide)
  · push Not at hm
    have hσ : orderOf ((e S.z : alternatingGroup (Fin m)) : Perm (Fin m)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, S.orderOf_z]
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' 13
      (thirteen_dvd_card_centralizer (by omega) hσ)
    have hh' : orderOf (h : Perm (Fin m)) = 13 := by rw [Subgroup.orderOf_coe, hh]
    set h₁ : alternatingGroup (Fin m) :=
      ⟨h, Perm.mem_alternatingGroup.mpr (sign_eq_one_of_orderOf hh')⟩ with hh₁
    have hcomm : h₁ * e S.z = e S.z * h₁ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp h.2)
    have hy : e.symm h₁ ∈ S.M := by
      rw [mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hcomm]
    have hord : orderOf (⟨e.symm h₁, hy⟩ : S.M) = 13 := by
      rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hh₁, Subgroup.orderOf_mk, hh']
    exact not_thirteen_dvd_card_M S hw hU (hord ▸ orderOf_dvd_natCard _)

end SmithAlt

end CFSG.LargeExtraspecial.S14

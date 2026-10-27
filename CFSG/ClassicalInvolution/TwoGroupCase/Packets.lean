module

public import CFSG.ClassicalInvolution.TwoGroupCase.CommutingFamily
public import CFSG.ClassicalInvolution.Reduction

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

theorem exists_mul_self_ne_one_of_mulEquiv_quaternionGroup {P : Type*} [Group P] {k : ℕ}
    (hk : 1 ≤ k) (e : P ≃* QuaternionGroup (2 ^ k)) : ∃ x : P, x * x ≠ 1 := by
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  refine ⟨e.symm (QuaternionGroup.a 1), fun h => ?_⟩
  have h2 : (e.symm (QuaternionGroup.a 1)) ^ 2 = 1 := by rw [pow_two]; exact h
  have hdvd : orderOf (e.symm (QuaternionGroup.a 1)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one] at hdvd
  have hpos : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem quaternion_conjugates_commute {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (S : Sylow 2 R)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) {t : G}
    (ht : t ∈ (S : Subgroup R).map R.subtype) (hto : orderOf t = 2)
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hST : (S : Subgroup R).map R.subtype ≤ T) {h k : G}
    (hhT : conjSubgroup h ((S : Subgroup R).map R.subtype) ≤ T)
    (hkT : conjSubgroup k ((S : Subgroup R).map R.subtype) ≤ T)
    (hne : conjSubgroup h ((S : Subgroup R).map R.subtype) ≠
      conjSubgroup k ((S : Subgroup R).map R.subtype)) :
    conjSubgroup h ((S : Subgroup R).map R.subtype) ⊓
        conjSubgroup k ((S : Subgroup R).map R.subtype) = ⊥ ∧
      ∀ x ∈ conjSubgroup h ((S : Subgroup R).map R.subtype),
        ∀ y ∈ conjSubgroup k ((S : Subgroup R).map R.subtype), x * y = y * x := by
  have hTE := (normalizer_eq_centralizer_and_tightlyEmbedded S hS ht hto hRC hRn).2
  obtain ⟨hSp, hSne⟩ := sylow_map_isPGroup_ne_bot S hS
  have d : TightData R ⊤ ((S : Subgroup R).map R.subtype) T :=
    ⟨hTE, by simpa using isSylow2Of_map_subtype S, hSne, hT, le_top, hST⟩
  have hΦ : ∃ x ∈ (S : Subgroup R).map R.subtype, x * x ≠ 1 := by
    obtain ⟨r, hr, ⟨e⟩⟩ := hS
    obtain ⟨y, hy⟩ := exists_mul_self_ne_one_of_mulEquiv_quaternionGroup (k := r - 2)
      (by omega) e
    refine ⟨((y : R) : G), ⟨(y : R), y.2, rfl⟩, fun h1 => hy ?_⟩
    apply Subtype.ext
    apply R.subtype_injective
    simpa using h1
  exact d.commute_conj hΦ (Subgroup.mem_top h) (Subgroup.mem_top k) hhT hkT hne

end CFSG.ClassicalInvolution

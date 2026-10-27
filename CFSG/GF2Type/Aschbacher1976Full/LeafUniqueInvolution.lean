module

public import CFSG.GF2Type.Aschbacher1976Full.Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicZStar

public section

namespace CFSG.GF2Type.Aschbacher1976Full.LeafUniqueInvolution

theorem eq_of_orderOf_eq_two_of_isCyclic {P : Type} [Group P] [Finite P] [IsCyclic P] {a b : P}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  haveI : Fintype P := Fintype.ofFinite P
  have hdvd : 2 ∣ Fintype.card P := by
    rw [← ha]
    exact orderOf_dvd_card
  have hcard := IsCyclic.card_orderOf_eq_totient hdvd
  rw [Nat.totient_two] at hcard
  exact Finset.card_le_one.1 hcard.le a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩) b
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)

theorem eq_zero_or_eq_natCast_of_add_self_eq_zero {N : ℕ} [NeZero N] (i : ZMod (2 * N))
    (hi : i + i = 0) : i = 0 ∨ i = (N : ZMod (2 * N)) := by
  haveI : NeZero (2 * N) := ⟨by have := NeZero.ne N; omega⟩
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hdvd : 2 * N ∣ i.val + i.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, ZMod.natCast_zmod_val, hi]
  obtain ⟨k, hk⟩ := hdvd
  have hlt : i.val < 2 * N := ZMod.val_lt i
  have hk2 : k < 2 := by
    by_contra h
    push Not at h
    have : 2 * N * 2 ≤ 2 * N * k := Nat.mul_le_mul_left (2 * N) h
    omega
  interval_cases k
  · left
    have h0 : i.val = 0 := by omega
    rw [← ZMod.natCast_zmod_val i, h0, Nat.cast_zero]
  · right
    have h1 : i.val = N := by omega
    rw [← ZMod.natCast_zmod_val i, h1]

theorem sq_eq_one_quaternion {N : ℕ} [NeZero N] (x : QuaternionGroup N) (hx : x ^ 2 = 1) :
    x = 1 ∨ x = QuaternionGroup.a (N : ZMod (2 * N)) := by
  haveI : NeZero (2 * N) := ⟨by have := NeZero.ne N; omega⟩
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  cases x with
  | a i =>
    rw [pow_two, QuaternionGroup.a_mul_a, QuaternionGroup.one_def] at hx
    rcases eq_zero_or_eq_natCast_of_add_self_eq_zero i (QuaternionGroup.a.inj hx) with rfl | rfl
    · exact Or.inl QuaternionGroup.one_def.symm
    · exact Or.inr rfl
  | xa i =>
    rw [QuaternionGroup.xa_sq, QuaternionGroup.one_def] at hx
    have h0 : ((N : ℕ) : ZMod (2 * N)) = 0 := QuaternionGroup.a.inj hx
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd hN h0
    exfalso
    omega

theorem eq_of_orderOf_eq_two_of_quaternion {P : Type} [Group P] [Finite P] {N : ℕ} [NeZero N]
    (e : P ≃* QuaternionGroup N) {a b : P} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  have key : ∀ x : P, orderOf x = 2 → e x = QuaternionGroup.a (N : ZMod (2 * N)) := by
    intro x hx
    have hx2 : x ^ 2 = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hx] at h
    have hsq : e x ^ 2 = 1 := by
      rw [← map_pow, hx2, map_one]
    have hne : e x ≠ 1 := by
      intro h1
      have h2 := MulEquiv.orderOf_eq e x
      rw [h1, orderOf_one, hx] at h2
      norm_num at h2
    rcases sq_eq_one_quaternion (e x) hsq with h1 | h1
    · exact absurd h1 hne
    · exact h1
  exact e.injective ((key a ha).trans (key b hb).symm)

theorem eq_of_orderOf_eq_two {P : Type} [Group P] [Finite P]
    (h : IsCyclic P ∨ ∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2))))
    {a b : P} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  rcases h with hc | ⟨n, -, ⟨e⟩⟩
  · exact eq_of_orderOf_eq_two_of_isCyclic ha hb
  · haveI : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
    exact eq_of_orderOf_eq_two_of_quaternion e ha hb

end CFSG.GF2Type.Aschbacher1976Full.LeafUniqueInvolution

namespace CFSG.GF2Type.Aschbacher1976Full

theorem leafUniqueInvolution_holds : Asc76LeafUniqueInvolution := by
  intro G _ _ z hS hH hU
  obtain ⟨hsimp, hnab, hz, -⟩ := hS
  haveI : IsSimpleGroup G := hsimp
  obtain ⟨g, hgne, hcomm⟩ := CFSG.OddStandard.Solomon75.exists_commuting_conj hnab hz
  have hzF : z ∈ Fz z := by
    rw [← hH]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have htF : g⁻¹ * z * g ∈ Fz z := by
    rw [← hH]
    exact Subgroup.mem_centralizer_singleton_iff.2 hcomm
  have htord : orderOf (g⁻¹ * z * g) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    simpa [MulAut.conj_apply, hz] using h
  have heq := LeafUniqueInvolution.eq_of_orderOf_eq_two hU
    ((Subgroup.orderOf_mk z hzF).trans hz) ((Subgroup.orderOf_mk _ htF).trans htord)
  exact hgne (congrArg Subtype.val heq).symm

end CFSG.GF2Type.Aschbacher1976Full

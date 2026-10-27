module

public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ClassicalInvolution.Asc77

open scoped MatrixGroups

theorem sq_eq_one_of_mem_center_quaternion {N : ℕ} (hN : 2 ≤ N) {x : QuaternionGroup N}
    (hx : x ∈ Subgroup.center (QuaternionGroup N)) : x ^ 2 = 1 := by
  have : NeZero N := ⟨by omega⟩
  cases x with
  | a i =>
    have h := Subgroup.mem_center_iff.mp hx (QuaternionGroup.xa 0)
    rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa] at h
    have h2 : (i : ZMod (2 * N)) + i = 0 := by
      have := QuaternionGroup.xa.inj h
      linear_combination this
    rw [sq, QuaternionGroup.a_mul_a, h2, QuaternionGroup.a_zero]
  | xa i =>
    exfalso
    have h := Subgroup.mem_center_iff.mp hx (QuaternionGroup.a 1)
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h
    have h2 : ((2 : ℕ) : ZMod (2 * N)) = 0 := by
      have := QuaternionGroup.xa.inj h
      push_cast
      linear_combination -this
    have := (ZMod.natCast_eq_zero_iff 2 (2 * N)).mp h2
    have := Nat.le_of_dvd (by norm_num) this
    omega

section SL2

variable {J : Type*} [Group J] [Finite J] {F : Type} [Field F] [Finite F]

theorem exists_quaternion_equiv_sylow (hodd : Odd (Nat.card F)) (e : J ≃* SL(2, F))
    (Q : Sylow 2 J) :
    ∃ k : ℕ, 1 ≤ k ∧ Nonempty ((Q : Subgroup J) ≃* QuaternionGroup (2 ^ k)) := by
  obtain ⟨n, hn, ⟨θ⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F hodd
    (Q.mapSurjective (f := e.toMonoidHom) e.surjective)
  refine ⟨n - 2, by omega, ⟨?_⟩⟩
  exact ((Q : Subgroup J).equivMapOfInjective e.toMonoidHom e.injective).trans θ


theorem sl2_witness (hodd : Odd (Nat.card F)) (e : J ≃* SL(2, F)) :
    ∃ (P : Sylow 2 J) (u j : J), u ∈ (P : Subgroup J) ∧
      (Subgroup.zpowers u).relIndex (P : Subgroup J) = 2 ∧ (∃ w, u * w ≠ w * u) ∧
      j ∈ Subgroup.zpowers u ∧ orderOf j = 4 ∧
      ∀ P' : Sylow 2 J, ∃ x ∈ (P' : Subgroup J), x * j ≠ j * x := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 J) := inferInstance
  obtain ⟨k, hk, ⟨θ⟩⟩ := exists_quaternion_equiv_sylow hodd e P
  have hN : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  let u' : ↥(P : Subgroup J) := θ.symm (QuaternionGroup.a 1)
  let u : J := u'
  have hou : orderOf u = 2 * 2 ^ k := by
    rw [show orderOf u = orderOf u' from Subgroup.orderOf_coe u',
      show orderOf u' = orderOf (QuaternionGroup.a 1 : QuaternionGroup (2 ^ k)) from
        MulEquiv.orderOf_eq θ.symm _]
    exact QuaternionGroup.orderOf_a_one
  have hoj : orderOf (u ^ (2 ^ k / 2)) = 4 := by
    have hdvd : 2 ^ k / 2 ∣ orderOf u := by
      rw [hou]
      exact Dvd.dvd.mul_left (Nat.div_dvd_of_dvd (dvd_pow_self 2 (by omega))) 2
    have hpos : 2 ^ k / 2 ≠ 0 := by
      have : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      have h2 : 0 < 2 ^ k := by positivity
      omega
    rw [orderOf_pow_of_dvd hpos hdvd, hou]
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ k = 2 * m := ⟨2 ^ (k - 1), by
      rw [← pow_succ' 2 (k - 1)]
      congr 1
      omega⟩
    rw [hm, Nat.mul_div_cancel_left _ (by norm_num)]
    have hm0 : 0 < m := by
      have h2 : 0 < 2 ^ k := by positivity
      omega
    rw [show 2 * (2 * m) = 4 * m by ring]
    exact Nat.mul_div_cancel _ hm0
  refine ⟨P, u, u ^ (2 ^ k / 2), u'.2, ?_, ?_, Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _,
    hoj, ?_⟩
  · have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers u) (P : Subgroup J)
    have hle : Subgroup.zpowers u ≤ (P : Subgroup J) := by
      rw [Subgroup.zpowers_le]
      exact u'.2
    rw [inf_eq_left.mpr hle, Nat.card_zpowers, hou] at h1
    have h2 : Nat.card (P : Subgroup J) = 4 * 2 ^ k := by
      rw [Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [h2] at h1
    have h3 : 0 < 2 * 2 ^ k := by positivity
    nlinarith
  · by_contra hcon
    have hcon' : ∀ w, u * w = w * u := fun w => by_contra fun h => hcon ⟨w, h⟩
    have hmem : u ∈ Subgroup.center J := Subgroup.mem_center_iff.mpr fun w => (hcon' w).symm
    have hd := Subgroup.orderOf_dvd_natCard (Subgroup.center J) hmem
    rw [CFSG.ClassicalInvolution.natCard_center_of_equiv_sl2 hodd e, hou] at hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  · intro P'
    by_contra hcon
    have hcon' : ∀ x ∈ (P' : Subgroup J), x * u ^ (2 ^ k / 2) = u ^ (2 ^ k / 2) * x :=
      fun x hx => by_contra fun h => hcon ⟨x, hx, h⟩
    generalize u ^ (2 ^ k / 2) = j at hoj hcon'
    have hjN : j ∈ Subgroup.normalizer ((P' : Subgroup J) : Set J) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have h1 := hcon' h hh
        rw [show j * h * j⁻¹ = h by rw [← h1]; group]
        exact hh
      · intro hh
        have h' := hcon' _ hh
        have h2 : j * h = j * (j * h * j⁻¹) := by
          calc j * h = (j * h * j⁻¹) * j := by group
            _ = j * (j * h * j⁻¹) := h'
        have h3 : h = j * h * j⁻¹ := mul_left_cancel h2
        rw [h3]
        exact hh
    have hz : IsPGroup 2 (Subgroup.zpowers j) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hoj]; norm_num)
    have hinf := hz.inf_normalizer_sylow P'
    have hjP : j ∈ (P' : Subgroup J) := by
      have : j ∈ Subgroup.zpowers j ⊓ Subgroup.normalizer (P' : Set J) :=
        ⟨Subgroup.mem_zpowers j, by rwa [Sylow.coe_coe] at hjN⟩
      rw [hinf] at this
      exact this.2
    have hcen : (⟨j, hjP⟩ : ↥(P' : Subgroup J)) ∈ Subgroup.center ↥(P' : Subgroup J) :=
      Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hcon' x x.2)
    obtain ⟨k', hk', ⟨θ'⟩⟩ := exists_quaternion_equiv_sylow hodd e P'
    have hN' : 2 ≤ 2 ^ k' := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) hk'
    have hcenQ : θ' ⟨j, hjP⟩ ∈ Subgroup.center (QuaternionGroup (2 ^ k')) := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      obtain ⟨x, rfl⟩ := θ'.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg θ' (Subgroup.mem_center_iff.mp hcen x)
    have hsq := sq_eq_one_of_mem_center_quaternion hN' hcenQ
    rw [← map_pow] at hsq
    have h1 : (⟨j, hjP⟩ : ↥(P' : Subgroup J)) ^ 2 = 1 := θ'.injective (by rw [hsq, map_one])
    have h2 : j ^ 2 = 1 := congrArg Subtype.val h1
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hoj] at this
    omega

end SL2

end CFSG.ClassicalInvolution.Asc77

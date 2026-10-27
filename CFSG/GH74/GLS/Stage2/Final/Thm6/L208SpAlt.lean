module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208SpPerm

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208Sp

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Stage1.Thm4.L97 CFSG.GH74.Uniqueness.SU.SU13.TA

variable {H : Type} [Group H] {n : ℕ} {π : H →* alternatingGroup (Fin n)}

theorem sq_of_map_eta (hπ : TwoCover π) (hn : 8 ≤ n) {x : H} {b : Fin 8}
    (hx : ((π x : alternatingGroup (Fin n)) : Perm (Fin n)) = iota hn (eta b)) : x ^ 2 = 1 := by
  by_cases hb : b = 0
  · subst hb
    have hk : x ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hx, eta_zero, map_one]
      rfl
    exact hπ.sq_eq_one_of_mem_ker' hk
  · exact hπ.sq_eq_one_of_cycleType_two_two_two_two hn
      (by rw [hx, cycleType_iota]; exact eta_ct b hb)

theorem odd_orderOf_map (ν : H) (hodd : Odd (orderOf ν)) :
    Odd (orderOf ((π ν : alternatingGroup (Fin n)) : Perm (Fin n))) := by
  have h : orderOf (((alternatingGroup (Fin n)).subtype.comp π) ν) ∣ orderOf ν :=
    orderOf_map_dvd ((alternatingGroup (Fin n)).subtype.comp π) ν
  exact Odd.of_dvd_nat hodd h

theorem std_case (hπ : TwoCover π) (hn : 8 ≤ n) (hn' : n ≤ 11) {t : H}
    (htπ : ((π t : alternatingGroup (Fin n)) : Perm (Fin n)) = iota hn (eta 1))
    {ν : H} (hodd : Odd (orderOf ν))
    (hνw : ∀ w : H, w ^ 2 = 1 → Commute w t → Commute ν w) : ν = 1 := by
  choose ηt hηt using fun a : Fin 8 => hπ.surj ⟨iota hn (eta a), mem_alt_eta hn a⟩
  have hηt' : ∀ a, ((π (ηt a) : alternatingGroup (Fin n)) : Perm (Fin n)) = iota hn (eta a) :=
    fun a => by rw [hηt a]
  have ht2 : t ^ 2 = 1 := sq_of_map_eta hπ hn htπ
  have hcomm_t : ∀ a, Commute (ηt a) t := by
    intro a
    have hcA : Commute (π (ηt a)) (π t) := by
      apply Subtype.ext
      show ((π (ηt a) * π t : alternatingGroup (Fin n)) : Perm (Fin n)) =
        ((π t * π (ηt a) : alternatingGroup (Fin n)) : Perm (Fin n))
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hηt', htπ, ← map_mul, ← map_mul, eta_comm]
    refine (hπ.commute_iff_sq_mul_eq_one (sq_of_map_eta hπ hn (hηt' a)) ht2 hcA).2 ?_
    refine sq_of_map_eta hπ hn (b := xor8 a 1) ?_
    rw [map_mul, Subgroup.coe_mul, hηt', htπ, ← map_mul, eta_mul]
  have hc : ∀ a : Fin 8, ((π ν : alternatingGroup (Fin n)) : Perm (Fin n)) * iota hn (eta a) =
      iota hn (eta a) * ((π ν : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [eta_zero, map_one, mul_one, one_mul]
    · have h1 : Commute ν (ηt a) := hνw (ηt a) (sq_of_map_eta hπ hn (hηt' a)) (hcomm_t a)
      have h2 : Commute (π ν) (π (ηt a)) := h1.map π
      have h3 := congrArg Subtype.val h2.eq
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hηt'] at h3
      exact h3
  have hσodd := odd_orderOf_map (π := π) ν hodd
  have hfix := fixes_first_eight hn hσodd hc
  have hfix' : ∀ i : Fin n, i.val < 8 →
      ((π ν : alternatingGroup (Fin n)) : Perm (Fin n)) i = i := by
    intro i hi
    have := hfix ⟨i.val, hi⟩
    have hpt : pt hn ⟨i.val, hi⟩ = i := Fin.ext rfl
    rwa [hpt] at this
  have hσ1 : ((π ν : alternatingGroup (Fin n)) : Perm (Fin n)) = 1 := by
    by_cases h11 : n = 11
    · subst h11
      have hv1 : ∃ v : H, ((π v : alternatingGroup (Fin 11)) : Perm (Fin 11)) = vbar1 :=
        (hπ.surj ⟨vbar1, mem_alt_of_ct vbar1_ct⟩).imp fun v hv => by rw [hv]
      have hv2 : ∃ v : H, ((π v : alternatingGroup (Fin 11)) : Perm (Fin 11)) = vbar2 :=
        (hπ.surj ⟨vbar2, mem_alt_of_ct vbar2_ct⟩).imp fun v hv => by rw [hv]
      obtain ⟨v1, hv1⟩ := hv1
      obtain ⟨v2, hv2⟩ := hv2
      have hsq1 : v1 ^ 2 = 1 :=
        hπ.sq_eq_one_of_cycleType_two_two_two_two hn (by rw [hv1]; exact vbar1_ct)
      have hsq2 : v2 ^ 2 = 1 :=
        hπ.sq_eq_one_of_cycleType_two_two_two_two hn (by rw [hv2]; exact vbar2_ct)
      have hcomm1 : Commute v1 t := by
        have hcA : Commute (π v1) (π t) := by
          apply Subtype.ext
          show ((π v1 * π t : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
            ((π t * π v1 : alternatingGroup (Fin 11)) : Perm (Fin 11))
          rw [Subgroup.coe_mul, Subgroup.coe_mul, hv1, htπ]
          exact vbar1_comm hn
        refine (hπ.commute_iff_sq_mul_eq_one hsq1 ht2 hcA).2 ?_
        refine hπ.sq_eq_one_of_cycleType_two_two_two_two hn ?_
        rw [map_mul, Subgroup.coe_mul, hv1, htπ]
        exact vbar1_eta_ct hn
      have hcomm2 : Commute v2 t := by
        have hcA : Commute (π v2) (π t) := by
          apply Subtype.ext
          show ((π v2 * π t : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
            ((π t * π v2 : alternatingGroup (Fin 11)) : Perm (Fin 11))
          rw [Subgroup.coe_mul, Subgroup.coe_mul, hv2, htπ]
          exact vbar2_comm hn
        refine (hπ.commute_iff_sq_mul_eq_one hsq2 ht2 hcA).2 ?_
        refine hπ.sq_eq_one_of_cycleType_two_two_two_two hn ?_
        rw [map_mul, Subgroup.coe_mul, hv2, htπ]
        exact vbar2_eta_ct hn
      have h1 : ((π ν : alternatingGroup (Fin 11)) : Perm (Fin 11)) * vbar1 =
          vbar1 * ((π ν : alternatingGroup (Fin 11)) : Perm (Fin 11)) := by
        have h := congrArg Subtype.val (((hνw v1 hsq1 hcomm1).map π).eq)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hv1] at h
        exact h
      have h2 : ((π ν : alternatingGroup (Fin 11)) : Perm (Fin 11)) * vbar2 =
          vbar2 * ((π ν : alternatingGroup (Fin 11)) : Perm (Fin 11)) := by
        have h := congrArg Subtype.val (((hνw v2 hsq2 hcomm2).map π).eq)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hv2] at h
        exact h
      exact tail_eleven hfix' h1 h2
    · exact tail_le_ten (by omega) hσodd hfix'
  have hνk : ν ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hσ1
  exact eq_one_of_sq_of_odd (hπ.sq_eq_one_of_mem_ker' hνk) hodd

theorem eq_one_of_commute_involutions (hπ : TwoCover π) (hn : 8 ≤ n) (hn' : n ≤ 11) {t : H}
    (ht : orderOf t = 2) (htk : t ∉ π.ker) {ν : H} (hν : Odd (orderOf ν))
    (hνw : ∀ w : H, w ^ 2 = 1 → Commute w t → Commute ν w) : ν = 1 := by
  have hct := hπ.cycleType_of_orderOf_eq_two hn hn' ht htk
  have hτ₀ : (((⟨iota hn (eta 1), mem_alt_eta hn 1⟩ : alternatingGroup (Fin n)) :
      alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = {2, 2, 2, 2} := by
    show (iota hn (eta 1)).cycleType = _
    rw [cycleType_iota]
    exact eta_ct 1 (by decide)
  obtain ⟨c, hc⟩ := isConj_iff.1
    (isConj_alternatingGroup_of_cycleType_eq_two_two_two_two hct hτ₀)
  obtain ⟨c', hc'⟩ := hπ.surj c
  have hconj : ∀ x : H, π (c' * x * c'⁻¹) = c * π x * c⁻¹ := fun x => by
    rw [map_mul, map_mul, map_inv, hc']
  have htπ : ((π (c' * t * c'⁻¹) : alternatingGroup (Fin n)) : Perm (Fin n)) = iota hn (eta 1) := by
    rw [hconj, hc]
  have hν' : Odd (orderOf (c' * ν * c'⁻¹)) := by
    have := MulEquiv.orderOf_eq (MulAut.conj c') ν
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hν
  have hνw' : ∀ w : H, w ^ 2 = 1 → Commute w (c' * t * c'⁻¹) → Commute (c' * ν * c'⁻¹) w := by
    intro w hw hwt
    have hw0 : (c'⁻¹ * w * c') ^ 2 = 1 := by
      have : (c'⁻¹ * w * c') ^ 2 = c'⁻¹ * w ^ 2 * c' := by
        rw [pow_two, pow_two]
        group
      rw [this, hw]
      group
    have hwt0 : Commute (c'⁻¹ * w * c') t := by
      have := hwt.map (MulAut.conj c'⁻¹).toMonoidHom
      simpa [MulAut.conj_apply, mul_assoc] using this
    have h1 := (hνw _ hw0 hwt0).map (MulAut.conj c').toMonoidHom
    simpa [MulAut.conj_apply, mul_assoc] using h1
  have hone := std_case hπ hn hn' htπ hν' hνw'
  have : ν = c'⁻¹ * (c' * ν * c'⁻¹) * c' := by group
  rw [this, hone]
  group

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208Sp

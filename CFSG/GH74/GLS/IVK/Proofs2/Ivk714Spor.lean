module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Ord
public import CFSG.GH74.Generic.S45.LSporMathA
public import CFSG.GH74.Generic.S45.LSporMathB
public import CFSG.GH74.Generic.S45.LSporJ3

public section

namespace CFSG.GH74.GLS.IVK

open CFSG CFSG.Blueprint CFSG.GH74.GLS Subgroup

theorem ivk714_card_fixedSubgroup_congr {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (z : MulAut K) :
    Nat.card ↥(fixedSubgroup K z) = Nat.card {x : K' // (MulAut.congr e z) x = x} := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)
  change z x = x ↔ (MulAut.congr e z) (e x) = e x
  rw [MulAut.congr_apply]
  simp

theorem ivk714_sq_eq_one {K : Type} [Group K] {z : MulAut K} (hz : orderOf z = 2) : z * z = 1 := by
  rw [← pow_two, ← hz]
  exact pow_orderOf_eq_one z

theorem ivk714_ne_one {K : Type} [Group K] {z : MulAut K} (hz : orderOf z = 2) : z ≠ 1 := by
  intro h
  rw [h, orderOf_one] at hz
  omega

theorem ivk714_congr_sq_eq_one {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {z : MulAut K}
    (hz : orderOf z = 2) : MulAut.congr e z * MulAut.congr e z = 1 := by
  rw [← map_mul, ivk714_sq_eq_one hz, map_one]

theorem ivk714_congr_ne_one {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {z : MulAut K}
    (hz : orderOf z = 2) : MulAut.congr e z ≠ 1 := fun h =>
  ivk714_ne_one hz ((MulAut.congr e).injective (by rw [h, map_one]))

theorem Ivk714Hyp.false_of_card_fixed {K K' : Type} [Group K] [Finite K] [Group K'] {z : MulAut K}
    (h : Ivk714Hyp K z) (e : K ≃* K') {n : ℕ}
    (hn : Nat.card {x : K' // (MulAut.congr e z) x = x} = n) (hnd : ¬ 2520 ∣ n) : False := by
  apply hnd
  have := h.two_five_two_zero_dvd
  rwa [ivk714_card_fixedSubgroup_congr e z, hn] at this

theorem Ivk714Hyp.center_eq_bot {K : Type} [Group K] [Finite K] [IsSimpleGroup K] {z : MulAut K}
    (h : Ivk714Hyp K z) : Subgroup.center K = ⊥ := by
  obtain ⟨H, -, x, -, y, -, hxy⟩ := h.exists_nonabelian_two_subgroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h1 | h1
  · exact h1
  · exfalso
    apply hxy
    have : x ∈ Subgroup.center K := by rw [h1]; trivial
    exact (Subgroup.mem_center_iff.mp this y).symm

end CFSG.GH74.GLS.IVK

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG CFSG.Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.IVK Subgroup

theorem ivk714_m11 :
    Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .M11) := by
  intro K _ _ _ hK z hz h
  obtain ⟨e⟩ := hK
  have e' : K ≃* NativeSporadic.M11 := e
  exact h.false_of_card_fixed e'
    (CFSG.GH74.Generic.S45.LAlt.m11_fixed_card _ (ivk714_congr_sq_eq_one e' hz)
      (ivk714_congr_ne_one e' hz))
    (by norm_num)

theorem ivk714_m22 :
    Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .M22) := by
  intro K _ _ _ hK z hz h
  obtain ⟨e⟩ := hK
  have e' : K ≃* NativeSporadic.M22 := e
  rcases CFSG.GH74.Generic.S45.m22_fixed_card _ (ivk714_congr_sq_eq_one e' hz)
    (ivk714_congr_ne_one e' hz) with hc | hc | hc
  · exact h.false_of_card_fixed e' hc (by norm_num)
  · exact h.false_of_card_fixed e' hc (by norm_num)
  · exact h.false_of_card_fixed e' hc (by norm_num)

theorem ivk714_m23 :
    Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .M23) := by
  intro K _ _ _ hK z hz h
  obtain ⟨e⟩ := hK
  have e' : K ≃* NativeSporadic.M23 := e
  exact h.false_of_card_fixed e'
    (CFSG.GH74.Generic.S45.LAlt.m23_fixed_card _ (ivk714_congr_sq_eq_one e' hz)
      (ivk714_congr_ne_one e' hz))
    (by norm_num)

theorem ivk714_j3 :
    Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .J3) := by
  intro K _ _ _ hK z hz h
  obtain ⟨e⟩ := hK
  rcases CFSG.GH74.Generic.S45.j3_fixed_card e z (ivk714_sq_eq_one hz) (ivk714_ne_one hz) with
    hc | hc
  · exact h.false_of_card_fixed e
      ((CFSG.GH74.Generic.S45.card_fixed_congr' e z).trans hc) (by norm_num)
  · exact h.false_of_card_fixed e
      ((CFSG.GH74.Generic.S45.card_fixed_congr' e z).trans hc) (by norm_num)

end CFSG.GH74.GLS.IVK.Proofs2

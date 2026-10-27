module

public import CFSG.ClassicalInvolution.Q3.Q3OFAlg
public import CFSG.ClassicalInvolution.Q3.Q3TY1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy
open scoped MatrixGroups commutatorElement

section Structure

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sq_eq_one_of_central_member {K : Subgroup G} {z : G} (hK : IsClassicalMember3 K z)
    (hex : classicalInvolutionOddCore ↥K = ⊥) {t : G} (ht : t ∈ K)
    (hc : ∀ y ∈ K, y * t = t * y) : t * t = 1 := by
  obtain ⟨e⟩ := hK.nonempty_equiv_sl2 hex
  set t' : ↥K := ⟨t, ht⟩ with ht'
  have hcen : e t' ∈ Subgroup.center SL(2, ZMod 3) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨n', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc (n' : G) n'.2)
  rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp hcen with h1 | h1
  · have h2 : t' = 1 := e.injective (by rw [h1, map_one])
    have h3 : t = 1 := congrArg Subtype.val h2
    rw [h3, one_mul]
  · have hsq : e t' * e t' = 1 := by
      rw [h1]
      have h3 := mul_inv_cancel (-1 : SL(2, ZMod 3))
      rwa [CFSG.ClassicalInvolution.Generic.neg_one_inv] at h3
    have h2 : t' * t' = 1 := e.injective (by rw [map_mul, hsq, map_one])
    exact congrArg Subtype.val h2

theorem eq_mul_of_isProductElt {K M : Subgroup G} {z w : G} (hK : IsClassicalMember3 K z)
    (hM : IsClassicalMember3 M w) (hexK : classicalInvolutionOddCore ↥K = ⊥) (hzw : z ≠ w)
    {x : G} (hx : IsProductElt3 K M x) : x = z * w := by
  obtain ⟨hKM, hxKM, hord, hxK, hxM⟩ := hx
  obtain ⟨k, hk, m, hm, rfl⟩ := exists_mul_of_mem_sup_of_commutes hKM hxKM
  have hx2 : k * m * (k * m) = 1 := by
    have := (orderOf_eq_prime_iff.mp hord).1
    rwa [pow_two] at this
  have hkm : k * m = m * k := hKM k hk m hm
  have hsq : k * k * (m * m) = 1 := by
    calc k * k * (m * m) = k * (k * m) * m := by group
      _ = k * (m * k) * m := by rw [hkm]
      _ = k * m * (k * m) := by group
      _ = 1 := hx2
  have htM : k * k ∈ M := by
    rw [eq_inv_of_mul_eq_one_left hsq]
    exact M.inv_mem (M.mul_mem hm hm)
  have htK : k * k ∈ K := K.mul_mem hk hk
  have ht2 : k * k * (k * k) = 1 :=
    sq_eq_one_of_central_member hK hexK htK fun y hy => hKM y hy (k * k) htM
  have ht1 : k * k = 1 := by
    by_contra hne
    have h1 : k * k = z := Q3TY.eq_of_mem_of_sq hK htK ht2 hne
    have h2 : k * k = w := Q3TY.eq_of_mem_of_sq hM htM ht2 hne
    exact hzw (h1.symm.trans h2)
  have hm1 : m * m = 1 := by
    rw [ht1, one_mul] at hsq
    exact hsq
  have hk' : k = 1 ∨ k = z := by
    by_cases hk1 : k = 1
    · exact Or.inl hk1
    · exact Or.inr (Q3TY.eq_of_mem_of_sq hK hk ht1 hk1)
  have hm' : m = 1 ∨ m = w := by
    by_cases hm0 : m = 1
    · exact Or.inl hm0
    · exact Or.inr (Q3TY.eq_of_mem_of_sq hM hm hm1 hm0)
  rcases hk' with hk0 | hkz <;> rcases hm' with hm0 | hmw
  · exfalso
    apply hxK
    rw [hk0, hm0, mul_one]
    exact K.one_mem
  · exfalso
    apply hxM
    rw [hk0, hmw, one_mul]
    exact hM.mem
  · exfalso
    apply hxK
    rw [hkz, hm0, mul_one]
    exact hK.mem
  · rw [hkz, hmw]

end Structure

end CFSG.ClassicalInvolution.Q3.Q3OF

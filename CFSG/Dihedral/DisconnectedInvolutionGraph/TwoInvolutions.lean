module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionGraph

public section

open CFSG.Open

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

theorem conjugate_product_eq_inv (t u : Involution G) :
    (MulAut.conj (t : G)) ((t : G) * u) = ((t : G) * u)⁻¹ := by
  have ht := inv_eq_self_of_orderOf_eq_two t.property
  have hu := inv_eq_self_of_orderOf_eq_two u.property
  have htsq : (t : G) * t = 1 := by
    simpa only [t.property, pow_two] using pow_orderOf_eq_one (t : G)
  simp only [MulAut.conj_apply, mul_inv_rev, ht, hu]
  calc
    (t : G) * ((t : G) * u) * t = ((t : G) * t) * u * t := by group
    _ = u * t := by rw [htsq, one_mul]

theorem conjugate_reverse_product_eq_inv (t u : Involution G) :
    (MulAut.conj (u : G)) ((t : G) * u) = ((t : G) * u)⁻¹ := by
  have ht := inv_eq_self_of_orderOf_eq_two t.property
  have hu := inv_eq_self_of_orderOf_eq_two u.property
  have husq : (u : G) * u = 1 := by
    simpa only [u.property, pow_two] using pow_orderOf_eq_one (u : G)
  simp only [MulAut.conj_apply, mul_inv_rev, ht, hu]
  calc
    (u : G) * ((t : G) * u) * u = u * t * ((u : G) * u) := by group
    _ = u * t := by rw [husq, mul_one]

theorem commute_of_conjugate_eq {g x : G} (hfixed : (MulAut.conj g) x = x) :
    g * x = x * g := by
  have heq := congrArg (fun value : G => value * g) hfixed
  simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using heq

theorem conjugate_pow_eq_inv (t u : Involution G) (exponent : ℕ) :
    (MulAut.conj (t : G)) (((t : G) * u) ^ exponent) =
      (((t : G) * u) ^ exponent)⁻¹ := by
  rw [map_pow, conjugate_product_eq_inv, inv_pow]

theorem even_product_common_involution [Finite G] (t u : Involution G)
    (heven : Even (orderOf ((t : G) * u))) :
    ∃ z : Involution G, (t : G) * z = z * t ∧ (u : G) * z = z * u := by
  have hdiv : 2 ∣ orderOf ((t : G) * u) := even_iff_two_dvd.mp heven
  let z : Involution G := ⟨((t : G) * u) ^ (orderOf ((t : G) * u) / 2),
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos _)) hdiv⟩
  have hzinv : (z : G)⁻¹ = z := inv_eq_self_of_orderOf_eq_two z.property
  refine ⟨z, ?_, ?_⟩
  · apply commute_of_conjugate_eq
    exact (conjugate_pow_eq_inv t u _).trans hzinv
  · apply commute_of_conjugate_eq
    change (MulAut.conj (u : G))
      (((t : G) * u) ^ (orderOf ((t : G) * u) / 2)) = z
    rw [map_pow, conjugate_reverse_product_eq_inv, inv_pow]
    exact hzinv

theorem reachable_of_even_product [Finite G] (t u : Involution G)
    (heven : Even (orderOf ((t : G) * u))) :
    (disconnectedInvolutionCommutingGraph G).Reachable t u := by
  obtain ⟨z, htz, huz⟩ := even_product_common_involution t u heven
  exact (reachable_of_commute t z htz).trans (reachable_of_commute u z huz).symm

theorem odd_product_conjugates (t u : Involution G)
    (hodd : Odd (orderOf ((t : G) * u))) :
    ∃ exponent : ℕ, conjugateInvolution (((t : G) * u) ^ exponent) t = u := by
  obtain ⟨exponent, horder⟩ := hodd
  refine ⟨exponent, ?_⟩
  apply Subtype.ext
  have ht := inv_eq_self_of_orderOf_eq_two t.property
  have htsq : (t : G) * t = 1 := by
    simpa only [t.property, pow_two] using pow_orderOf_eq_one (t : G)
  have hinvert := conjugate_pow_eq_inv t u exponent
  have hmove : (t : G) * (((t : G) * u) ^ exponent)⁻¹ =
      (((t : G) * u) ^ exponent) * t := by
    have heq := congrArg (fun value : G => (t : G) * value) hinvert
    simpa only [MulAut.conj_apply, ht, ← mul_assoc, htsq, one_mul]
      using heq.symm
  have hpower : ((t : G) * u) ^ (2 * exponent + 1) = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one _
  have hlast : ((t : G) * u) ^ (2 * exponent) * (t : G) = u := by
    have heq := congrArg (fun value : G => value * (u : G)) hpower
    have husq : (u : G) * u = 1 := by
      simpa only [u.property, pow_two] using pow_orderOf_eq_one (u : G)
    simpa only [pow_succ, mul_assoc, husq, mul_one, one_mul]
      using heq
  change (((t : G) * u) ^ exponent) * t * (((t : G) * u) ^ exponent)⁻¹ = u
  calc
    _ = (((t : G) * u) ^ exponent) * ((((t : G) * u) ^ exponent) * t) := by
      rw [mul_assoc, hmove]
    _ = ((t : G) * u) ^ (2 * exponent) * t := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    _ = u := hlast

end CFSG.DisconnectedInvolutionGraph.Helpers

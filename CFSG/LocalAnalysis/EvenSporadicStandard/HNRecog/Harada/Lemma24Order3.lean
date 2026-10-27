module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Ind

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {ι : Elem2 6 →* G}

theorem Induces.pow {x : G} {g : Equiv.Perm V6} (hx : Induces ι x g) (n : ℕ) :
    Induces ι (x ^ n) (g ^ n) := by
  induction n with
  | zero => simpa using induces_one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hx

theorem exists_order_three_induces (hι : Function.Injective ι)
    (hC : centralizer (ι.range : Set G) ≤ ι.range) (hind : inducedGroup ι = OmegaPlus) :
    ∃ a : G, a ^ 3 = 1 ∧ Induces ι a w3 := by
  have hw3 : w3 ∈ inducedGroup ι := by
    rw [hind]
    exact w3_mem_omegaPlus
  obtain ⟨n, -, hnw⟩ := hw3
  have hnwI : Induces ι n w3 := hnw
  have h3 : Induces ι (n ^ 3) (1 : Equiv.Perm V6) := by
    have h := hnwI.pow 3
    rwa [w3_pow_three] at h
  obtain ⟨c, hc⟩ := Induces.exists_eq_coordElt hC h3
  have hcadd : c + c = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (c i)
  have hc2 : coordElt ι c * coordElt ι c = 1 := by
    rw [← coordElt_add, hcadd, coordElt_zero]
  have hn6 : n ^ 6 = 1 := by
    have h : n ^ 6 = coordElt ι c * coordElt ι c := by
      rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add, hc]
    rw [h, hc2]
  refine ⟨n ^ 4, ?_, ?_⟩
  · have h : (n ^ 4) ^ 3 = n ^ 12 := by
      rw [← pow_mul, show (4 : ℕ) * 3 = 12 by norm_num]
    rw [h, show (12 : ℕ) = 6 * 2 by norm_num, pow_mul, hn6, one_pow]
  · have h : w3 ^ 4 = w3 := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, w3_pow_three, one_mul, pow_one]
    have h' := hnwI.pow 4
    rwa [h] at h'

theorem orderOf_eq_three_of_induces (hι : Function.Injective ι) {a : G} (ha3 : a ^ 3 = 1)
    (ha : Induces ι a w3) : orderOf a = 3 := by
  have hdvd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha3
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
  · exfalso
    have ha1 : a = 1 := orderOf_eq_one_iff.mp h1
    subst ha1
    exact w3_ne_one (Induces.unique hι ha induces_one)
  · exact h3

theorem mem_centralizer_of_induces_w3 {a t : G} (ht : coordElt ι tv = t) (ha : Induces ι a w3) :
    a ∈ centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := ha tv
  rw [w3_tv, ht] at h
  exact mul_inv_eq_iff_eq_mul.mp h

end CFSG.EvenSporadicStandard.HNRecog.Harada

module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public import Certificates.Certificate2195
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22InvolutionsInputs
public import Certificates.Certificate2032
public import Certificates.Certificate3029

public section

namespace CFSG.ComponentClassification.WittDesign

open MulAction CFSG.Sporadic.Mathieu

theorem count_aFun : m22Count (fun g => ∀ x, g x = aFun x) = 1 :=
  Certificates.certificate2032.1

theorem count_centralizer_a : m22Count (fun g => ∀ x, g (aFun x) = aFun (g x)) = 384 :=
  Certificates.certificate2032.2.1

theorem aFun_facts : (∀ x, aFun (aFun x) = x) ∧ aFun 0 ≠ 0 :=
  Certificates.certificate2032.2.2

theorem exists_a : ∃ t : M22, ⇑(t : Equiv.Perm (Fin 22)) = aFun := by
  obtain ⟨t, ht⟩ := exists_m22_of_count (fun g => ∀ x, g x = aFun x) (by rw [count_aFun]; norm_num)
  exact ⟨t, funext ht⟩

theorem orderOf_eq_two_of_coe {t : M22} (ht : ⇑(t : Equiv.Perm (Fin 22)) = aFun) :
    orderOf t = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · refine Subtype.ext (Equiv.ext fun x => ?_)
    change (t : Equiv.Perm (Fin 22)) ((t : Equiv.Perm (Fin 22)) x) = x
    rw [ht]
    exact aFun_facts.1 x
  · intro h
    have := congrArg (fun σ : M22 => (σ : Equiv.Perm (Fin 22)) 0) h
    simp only [ht] at this
    exact aFun_facts.2 this

theorem card_centralizer_of_coe {t : M22} (ht : ⇑(t : Equiv.Perm (Fin 22)) = aFun) :
    Nat.card (Subgroup.centralizer {t}) = 384 := by
  rw [← count_centralizer_a, ← card_m22_subtype]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, Subgroup.coe_mul,
    Subgroup.coe_mul, Equiv.ext_iff]
  simp only [Equiv.Perm.mul_apply, ht]

theorem card_centralizer_eq_stabilizer (t : M22) :
    Nat.card (Subgroup.centralizer {t}) = Nat.card (stabilizer (ConjAct M22) t) := by
  refine Nat.card_congr (ConjAct.toConjAct.toEquiv.subtypeEquiv fun g => ?_)
  change g ∈ Subgroup.centralizer {t} ↔ ConjAct.toConjAct g ∈ stabilizer (ConjAct M22) t
  rw [mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]

theorem orderOf_of_isConj {s t : M22} (h : IsConj s t) : orderOf s = orderOf t := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective s).symm

theorem card_orbit_conj (t : M22) :
    Nat.card (orbit (ConjAct M22) t) * Nat.card (Subgroup.centralizer {t}) = 443520 := by
  rw [card_centralizer_eq_stabilizer, natCard_orbit_mul_card_stabilizer,
    Nat.card_congr ConjAct.ofConjAct.toEquiv, card_M22]

theorem card_involutions : Nat.card {x : M22 // orderOf x = 2} = 1155 :=
  CFSG.Sporadic.Schreier.at_m22_image_pair_count.2.2.2.2.1

theorem orbit_a {t₀ : M22} (ht₀ : ⇑(t₀ : Equiv.Perm (Fin 22)) = aFun) :
    orbit (ConjAct M22) t₀ = {x | orderOf x = 2} := by
  have hsub : orbit (ConjAct M22) t₀ ⊆ {x | orderOf x = 2} := by
    intro x hx
    rw [ConjAct.mem_orbit_conjAct] at hx
    exact (orderOf_of_isConj hx).trans (orderOf_eq_two_of_coe ht₀)
  have hcard : (orbit (ConjAct M22) t₀).ncard = 1155 := by
    have h := card_orbit_conj t₀
    rw [card_centralizer_of_coe ht₀, Nat.card_coe_set_eq,
      show (443520 : ℕ) = 1155 * 384 by norm_num] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [hcard, ← Nat.card_coe_set_eq]
  exact card_involutions.le

theorem isConj_of_orderOf_eq_two {s t : M22} (hs : orderOf s = 2) (ht : orderOf t = 2) :
    IsConj s t := by
  obtain ⟨t₀, ht₀⟩ := exists_a
  have h1 : s ∈ orbit (ConjAct M22) t₀ := by rw [orbit_a ht₀]; exact hs
  have h2 : t ∈ orbit (ConjAct M22) t₀ := by rw [orbit_a ht₀]; exact ht
  rw [ConjAct.mem_orbit_conjAct] at h1 h2
  exact h1.trans h2.symm

theorem card_centralizer_involution {t : M22} (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer {t}) = 384 := by
  obtain ⟨t₀, ht₀⟩ := exists_a
  have horb : orbit (ConjAct M22) t = orbit (ConjAct M22) t₀ := by
    refine orbit_eq_iff.2 ?_
    rw [ConjAct.mem_orbit_conjAct]
    exact isConj_of_orderOf_eq_two ht (orderOf_eq_two_of_coe ht₀)
  have h := card_orbit_conj t
  rw [horb, Nat.card_coe_set_eq, orbit_a ht₀, ← Nat.card_coe_set_eq] at h
  have h2 : Nat.card ({x | orderOf x = 2} : Set M22) = 1155 := card_involutions
  rw [h2, show (443520 : ℕ) = 1155 * 384 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

end CFSG.ComponentClassification.WittDesign

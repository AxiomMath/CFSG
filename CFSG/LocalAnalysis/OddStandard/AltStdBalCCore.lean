module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25Datum
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup CFSG.EvenSporadicStandard.Finkelstein77
open CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

theorem eq_sq_of_commutator_involution {G : Type*} [Group G] [Finite G] {x : G}
    (hx : orderOf x = 4) (hwc : WeaklyClosedInNormalizer (zpowers x)) {t c : G}
    (ht : IsConj (x ^ 2) t) (hu1 : t * c * t⁻¹ * c⁻¹ ≠ 1)
    (hu2 : (t * c * t⁻¹ * c⁻¹) * (t * c * t⁻¹ * c⁻¹) = 1)
    (hux : (t * c * t⁻¹ * c⁻¹) * x = x * (t * c * t⁻¹ * c⁻¹)) :
    t * c * t⁻¹ * c⁻¹ = x ^ 2 := by
  have ht2 : t * t = 1 := sq_eq_one_of_isConj hx ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set t' : G := c * t * c⁻¹ with ht'
  have ht'c : IsConj (x ^ 2) t' := ht.trans (isConj_iff.mpr ⟨c, rfl⟩)
  have ht'2 : t' * t' = 1 := sq_eq_one_of_isConj hx ht'c
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
  have hu : t * c * t⁻¹ * c⁻¹ = t * t' := by
    rw [ht', htinv]
    group
  rw [hu] at hu1 hu2 hux ⊢
  have hcomm : t * t' = t' * t := by
    have h1 : t * t' = (t * t')⁻¹ := eq_inv_of_mul_eq_one_left hu2
    rw [mul_inv_rev, ht'inv, htinv] at h1
    exact h1
  have hne : t ≠ t' := by
    intro h
    apply hu1
    rw [← h]
    exact ht2
  have hconj : IsConj (x ^ 2) (t * t') := mul_isConj_of_commute hx hwc ht ht'c hne hcomm
  exact eq_sq_of_commute_conj hx hwc (IsConj.refl x) hconj hux

theorem exists_mem_orderOf_four {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hp : IsPGroup 2 P) (hc : IsCyclic P) (h4 : 4 ≤ Nat.card P) :
    ∃ x : G, x ∈ P ∧ orderOf x = 4 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
  have hord : orderOf g = Nat.card P := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hn2 : 2 ≤ n := by
    by_contra h
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨((g ^ (2 ^ (n - 2)) : P) : G), (g ^ (2 ^ (n - 2)) : P).2, ?_⟩
  rw [Subgroup.orderOf_coe,
    orderOf_pow_of_dvd (by positivity) (by rw [hord, hn]; exact Nat.pow_dvd_pow 2 (by omega)),
    hord, hn, Nat.pow_div (by omega) (by norm_num)]
  rw [show n - (n - 2) = 2 by omega]

end CFSG.OddStandard.AltStdBal

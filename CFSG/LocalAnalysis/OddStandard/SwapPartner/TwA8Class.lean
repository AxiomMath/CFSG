module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwDefs

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm

private lemma tw_card_conj_class_one :
    Nat.card {y : alternatingGroup (Fin 8) | IsConj (1 : alternatingGroup (Fin 8)) y} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨1, IsConj.refl 1⟩, fun y => ?_⟩
  have hy : (y : alternatingGroup (Fin 8)) = 1 := isConj_one_right.mp y.2
  exact Subtype.ext (by simpa using hy)

private lemma tw_card_conj_class_eq (σ : Perm (Fin 8)) {k : ℕ} (hk : k ≠ 0)
    (hcyc : σ.cycleType = Multiset.replicate k 2) :
    Nat.card {h : Perm (Fin 8) | IsConj σ h} =
      Nat.factorial 8 / (Nat.factorial (8 - k * 2) * 2 ^ k * Nat.factorial k) := by
  rw [Equiv.Perm.card_isConj_eq, hcyc]
  simp only [Fintype.card_fin, Multiset.sum_replicate, smul_eq_mul, Multiset.prod_replicate,
    Multiset.toFinset_replicate, if_neg hk, Finset.prod_singleton,
    Multiset.count_replicate_self]

theorem isConj_abType22_of_card_eq {x : alternatingGroup (Fin 8)} (hx : x * x = 1)
    (hc : Nat.card {y : alternatingGroup (Fin 8) | IsConj x y} = 210) :
    IsConj x abType22 := by
  let σ : Perm (Fin 8) := (x : Perm (Fin 8))
  have hσ2 : σ * σ = 1 := by
    have h := congrArg (Subtype.val) hx
    simpa [σ] using h
  have hx_ne : x ≠ 1 := by
    intro h
    rw [h] at hc
    rw [tw_card_conj_class_one] at hc
    norm_num at hc
  have hσ_ne : σ ≠ 1 := by
    intro h
    apply hx_ne
    exact Subtype.ext (by simpa [σ] using h)
  have hmem2 : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have hdvd : n ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hn
    have horder : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have hdvd2 : n ∣ 2 := hdvd.trans horder
    have hge : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have hle2 : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  have hcyc : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.mpr hmem2
  have hsum : σ.cycleType.sum = 2 * Multiset.card σ.cycleType := by
    rw [hcyc, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
    ring
  have hsum_le : σ.cycleType.sum ≤ 8 := by
    rw [Equiv.Perm.sum_cycleType]
    calc σ.support.card ≤ Fintype.card (Fin 8) := Finset.card_le_univ σ.support
      _ = 8 := by simp
  have hk_le : Multiset.card σ.cycleType ≤ 4 := by
    have h : 2 * Multiset.card σ.cycleType ≤ 8 := by rw [← hsum]; exact hsum_le
    omega
  have hk_ne : Multiset.card σ.cycleType ≠ 0 := by
    have hpos : 0 < Multiset.card σ.cycleType := Equiv.Perm.card_cycleType_pos.mpr hσ_ne
    omega
  have hsign : σ.sign = 1 := Equiv.Perm.mem_alternatingGroup.mp x.2
  have heven : Even (Multiset.card σ.cycleType) := by
    have h1 : (-1 : ℤˣ) ^ (σ.cycleType.sum + Multiset.card σ.cycleType) = 1 := by
      rw [← Equiv.Perm.sign_of_cycleType]
      exact hsign
    rw [hsum] at h1
    have h3 : (-1 : ℤˣ) ^ (3 * Multiset.card σ.cycleType) = 1 := by
      rw [show 3 * Multiset.card σ.cycleType =
        2 * Multiset.card σ.cycleType + Multiset.card σ.cycleType by ring]
      exact h1
    have h3' : ((-1 : ℤˣ) ^ 3) ^ Multiset.card σ.cycleType = 1 := by
      simpa only [pow_mul] using h3
    rw [show (-1 : ℤˣ) ^ 3 = -1 by decide] at h3'
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp h3'
  have hk_cases : Multiset.card σ.cycleType = 2 ∨ Multiset.card σ.cycleType = 4 := by
    obtain ⟨m, hm⟩ := heven
    have h1 : 1 ≤ m := by omega
    have h2 : m ≤ 2 := by omega
    interval_cases m <;> omega
  let f : {y : alternatingGroup (Fin 8) | IsConj x y} →
      {h : Perm (Fin 8) | IsConj σ h} :=
    fun y => ⟨(y.1 : Perm (Fin 8)),
      MonoidHom.map_isConj (Subgroup.subtype (alternatingGroup (Fin 8))) y.2⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h1 : (f a).1 = (f b).1 := congrArg Subtype.val hab
    have h2 : (a.1 : Perm (Fin 8)) = (b.1 : Perm (Fin 8)) := h1
    exact Subtype.ext (Subtype.ext h2)
  have hle : Nat.card {y : alternatingGroup (Fin 8) | IsConj x y} ≤
      Nat.card {h : Perm (Fin 8) | IsConj σ h} :=
    Nat.card_le_card_of_injective f hf_inj
  have hk_ne_four : Multiset.card σ.cycleType ≠ 4 := by
    intro hk4
    have hS : Nat.card {h : Perm (Fin 8) | IsConj σ h} = 105 := by
      rw [tw_card_conj_class_eq σ hk_ne hcyc, hk4]
      norm_num
    have h210 : 210 ≤ 105 := by
      calc 210 = Nat.card {y : alternatingGroup (Fin 8) | IsConj x y} := hc.symm
        _ ≤ Nat.card {h : Perm (Fin 8) | IsConj σ h} := hle
        _ = 105 := hS
    norm_num at h210
  have hk2 : Multiset.card σ.cycleType = 2 := by
    rcases hk_cases with h | h
    · exact h
    · exact absurd h hk_ne_four
  have hS : Nat.card {h : Perm (Fin 8) | IsConj σ h} = 210 := by
    rw [tw_card_conj_class_eq σ hk_ne hcyc, hk2]
    norm_num
  have hcard : Nat.card {h : Perm (Fin 8) | IsConj σ h} ≤
      Nat.card {y : alternatingGroup (Fin 8) | IsConj x y} := by
    rw [hS, hc]
  have hf_surj : Function.Surjective f := (hf_inj.bijective_of_nat_card_le hcard).2
  have hσcyc : σ.cycleType = Multiset.replicate 2 2 := by
    rw [hcyc, hk2]
  have habType : (abType22 : Perm (Fin 8)).cycleType = Multiset.replicate 2 2 := by
    change (swap 0 1 * swap 2 3 : Perm (Fin 8)).cycleType = Multiset.replicate 2 2
    rw [Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)]
    decide
  have hab : IsConj σ (abType22 : Perm (Fin 8)) :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (hσcyc.trans habType.symm)
  obtain ⟨y, hy⟩ := hf_surj ⟨(abType22 : Perm (Fin 8)), hab⟩
  have hyval : (y.1 : Perm (Fin 8)) = (abType22 : Perm (Fin 8)) :=
    congrArg (fun z : {h : Perm (Fin 8) | IsConj σ h} => (z.1 : Perm (Fin 8))) hy
  have hy1 : y.1 = abType22 := Subtype.ext hyval
  rw [← hy1]
  exact y.2

end CFSG.OddStandard.AltStdSec.SwapPartner

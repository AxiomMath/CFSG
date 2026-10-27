module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NK
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NCore

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

private theorem odd_card_oddCore''' (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (CFSG.oddCore H)) := by
  have h := LocalCores.piCore_isPiSubgroup (G := H) {q : Nat.Primes | q.val ≠ 2}
  rw [← CFSG.oddCore_eq_piCore] at h
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  exact h ⟨2, Nat.prime_two⟩ h2 rfl

namespace Inst

variable (I : Inst S)

theorem odd_orderOf_of_mem_K {k : X} (hk : k ∈ A7Base.oddCoreIn (normalizer (I.E : Set X))) :
    Odd (orderOf k) := by
  obtain ⟨o, ho, rfl⟩ := hk
  have h1 := orderOf_dvd_natCard (⟨o, ho⟩ : CFSG.oddCore (normalizer (I.E : Set X)))
  rw [Subgroup.orderOf_mk] at h1
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  exact (odd_card_oddCore''' _).of_dvd_nat h1

theorem conj_mem_K {n k : X} (hn : n ∈ normalizer (I.E : Set X))
    (hk : k ∈ A7Base.oddCoreIn (normalizer (I.E : Set X))) :
    n * k * n⁻¹ ∈ A7Base.oddCoreIn (normalizer (I.E : Set X)) := by
  obtain ⟨o, ho, rfl⟩ := hk
  refine ⟨⟨n, hn⟩ * o * ⟨n, hn⟩⁻¹, (CFSG.oddCore_normal _).conj_mem _ ho _, ?_⟩
  simp

theorem exists_mul_K {c : X} (hc : c ∈ centralizer (I.E : Set X)) :
    ∃ e ∈ I.E, ∃ k ∈ A7Base.oddCoreIn (normalizer (I.E : Set X)), c = e * k := by
  obtain ⟨K, -, hKO, hdec⟩ := I.exists_complement
  obtain ⟨e, he, k, hk, h⟩ := hdec c hc
  exact ⟨e, he, k, hKO hk, h⟩

theorem eq_one_of_mem_E_K {e : X} (he : e ∈ I.E)
    (hk : e ∈ A7Base.oddCoreIn (normalizer (I.E : Set X))) : e = 1 :=
  eq_one_of_odd_of_pow_two_pow (I.odd_orderOf_of_mem_K hk) (a := 1) (by simpa using I.sq_eq_one he)

theorem eq_of_mul_K {e e' k k' : X} (he : e ∈ I.E) (he' : e' ∈ I.E)
    (hk : k ∈ A7Base.oddCoreIn (normalizer (I.E : Set X)))
    (hk' : k' ∈ A7Base.oddCoreIn (normalizer (I.E : Set X)))
    (h : e * k = e' * k') : e = e' ∧ k = k' := by
  have h1 : e'⁻¹ * e = k' * k⁻¹ := by
    calc e'⁻¹ * e = e'⁻¹ * (e * k) * k⁻¹ := by group
      _ = k' * k⁻¹ := by rw [h]; group
  have h2 : e'⁻¹ * e = 1 := I.eq_one_of_mem_E_K (mul_mem (inv_mem he') he)
    (h1 ▸ mul_mem hk' (inv_mem hk))
  have h3 : e = e' := by
    calc e = e' * (e'⁻¹ * e) := by group
      _ = e' := by rw [h2, mul_one]
  subst h3
  exact ⟨rfl, mul_left_cancel h⟩

theorem mem_K_of_odd {c : X} (hc : c ∈ centralizer (I.E : Set X)) (hodd : Odd (orderOf c)) :
    c ∈ A7Base.oddCoreIn (normalizer (I.E : Set X)) := by
  obtain ⟨e, he, k, hk, rfl⟩ := I.exists_mul_K hc
  set m := orderOf (e * k)
  have hcomm : e * k = k * e := ((mem_centralizer_iff.mp (I.oddCoreIn_le_centralizerE hk)) e he)
  have hpow : (e * k) ^ m = e ^ m * k ^ m := (Commute.mul_pow hcomm m)
  have h1 : e ^ m * k ^ m = 1 * 1 := by rw [← hpow, pow_orderOf_eq_one, one_mul]
  obtain ⟨-, hkm⟩ := I.eq_of_mul_K (pow_mem he m) (one_mem _) (pow_mem hk m) (one_mem _) h1
  have hem : e ^ m = 1 := by
    have := h1
    rw [hkm, mul_one, mul_one] at this
    exact this
  have he1 : e = 1 := by
    obtain ⟨j, hj⟩ := hodd
    rw [hj, pow_succ, pow_mul, I.sq_eq_one he, one_pow, one_mul] at hem
    exact hem
  rw [he1, one_mul]
  exact hk

theorem commute_of_mem_K {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hQN : Q ≤ normalizer (I.E : Set X))
    {k : X} (hk : k ∈ A7Base.oddCoreIn (normalizer (I.E : Set X)))
    (hkQ : k ∈ normalizer (Q : Set X))
    {q : X} (hq : q ∈ Q) : k * q = q * k := by
  set c := k * q * k⁻¹ * q⁻¹ with hc
  have hcK : c ∈ A7Base.oddCoreIn (normalizer (I.E : Set X)) := by
    have := mul_mem hk (I.conj_mem_K (hQN hq) (inv_mem hk))
    rwa [show k * (q * k⁻¹ * q⁻¹) = c by rw [hc]; group] at this
  have hcQ : c ∈ Q := by
    have h1 : k * q * k⁻¹ ∈ Q := (mem_normalizer_iff.mp hkQ q).mp hq
    exact mul_mem h1 (inv_mem hq)
  obtain ⟨a, ha⟩ := hQ ⟨c, hcQ⟩
  have hca : c ^ (2 ^ a) = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have h1 := eq_one_of_odd_of_pow_two_pow (I.odd_orderOf_of_mem_K hcK) hca
  have := mul_inv_eq_one.mp h1
  calc k * q = k * q * k⁻¹ * k := by group
    _ = q * k := by rw [this]

end Inst

end CFSG.ComponentClassification.HSFLit.KD46

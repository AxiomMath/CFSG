module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NMat
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NCore

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem card_sup_zpowers {G : Type*} [Group G] [Finite G] {M : Subgroup G} {g : G}
    (hg : g ∈ normalizer (M : Set G)) (hg2 : g ^ 2 ∈ M) (hgM : g ∉ M) :
    Nat.card (M ⊔ zpowers g : Subgroup G) = 2 * Nat.card M := by
  have hset : ((M ⊔ zpowers g : Subgroup G) : Set G) =
      (M : Set G) ∪ (fun x => g * x) '' (M : Set G) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_union, Set.mem_image]
    rw [mem_sup_zpowers_iff hg hg2]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨g⁻¹ * x, h, by group⟩
    · rintro (h | ⟨m, hm, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (by simpa using hm)
  have hdisj : Disjoint (M : Set G) ((fun x => g * x) '' (M : Set G)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨m, hm, rfl⟩
    apply hgM
    have e : g = g * m * m⁻¹ := by group
    rw [e]
    exact mul_mem hx (inv_mem hm)
  have h1 : Nat.card (M ⊔ zpowers g : Subgroup G) =
      ((M ⊔ zpowers g : Subgroup G) : Set G).ncard := (Nat.card_coe_set_eq _).symm
  have h2 : Nat.card M = (M : Set G).ncard := (Nat.card_coe_set_eq _).symm
  rw [h1, h2, hset, Set.ncard_union_eq hdisj,
    Set.ncard_image_of_injective _ (mul_right_injective g)]
  ring

theorem eq_one_of_odd_of_pow_two_pow {G : Type*} [Group G] {g : G} (hodd : Odd (orderOf g))
    {a : ℕ} (h : g ^ (2 ^ a) = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · simpa using hj
  · rw [hj, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.odd_iff, Nat.mul_mod_left])

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {T₁ : Subgroup X}

private theorem odd_card_oddCore''' (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (CFSG.oddCore H)) := by
  have h := LocalCores.piCore_isPiSubgroup (G := H) {q : Nat.Primes | q.val ≠ 2}
  rw [← CFSG.oddCore_eq_piCore] at h
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  exact h ⟨2, Nat.prime_two⟩ h2 rfl

namespace Inst

variable (I : S.Inst)

theorem odd_orderOf_of_mem_K {k : X} (hk : k ∈ oddCoreIn (normalizer (I.E : Set X))) :
    Odd (orderOf k) := by
  obtain ⟨o, ho, rfl⟩ := hk
  have h1 := orderOf_dvd_natCard (⟨o, ho⟩ : CFSG.oddCore (normalizer (I.E : Set X)))
  rw [Subgroup.orderOf_mk] at h1
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  exact (odd_card_oddCore''' _).of_dvd_nat h1

theorem conj_mem_K {n k : X} (hn : n ∈ normalizer (I.E : Set X))
    (hk : k ∈ oddCoreIn (normalizer (I.E : Set X))) :
    n * k * n⁻¹ ∈ oddCoreIn (normalizer (I.E : Set X)) := by
  obtain ⟨o, ho, rfl⟩ := hk
  refine ⟨⟨n, hn⟩ * o * ⟨n, hn⟩⁻¹, (CFSG.oddCore_normal _).conj_mem _ ho _, ?_⟩
  simp

theorem exists_mul_K {c : X} (hc : c ∈ centralizer (I.E : Set X)) :
    ∃ e ∈ I.E, ∃ k ∈ oddCoreIn (normalizer (I.E : Set X)), c = e * k := by
  obtain ⟨K, -, hKO, hdec⟩ := I.exists_complement
  obtain ⟨e, he, k, hk, h⟩ := hdec c hc
  exact ⟨e, he, k, hKO hk, h⟩

theorem eq_one_of_mem_E_K {e : X} (he : e ∈ I.E) (hk : e ∈ oddCoreIn (normalizer (I.E : Set X))) :
    e = 1 :=
  eq_one_of_odd_of_pow_two_pow (I.odd_orderOf_of_mem_K hk) (a := 1) (by simpa using I.sq_eq_one he)

theorem eq_of_mul_K {e e' k k' : X} (he : e ∈ I.E) (he' : e' ∈ I.E)
    (hk : k ∈ oddCoreIn (normalizer (I.E : Set X)))
    (hk' : k' ∈ oddCoreIn (normalizer (I.E : Set X)))
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
    c ∈ oddCoreIn (normalizer (I.E : Set X)) := by
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
    {k : X} (hk : k ∈ oddCoreIn (normalizer (I.E : Set X))) (hkQ : k ∈ normalizer (Q : Set X))
    {q : X} (hq : q ∈ Q) : k * q = q * k := by
  set c := k * q * k⁻¹ * q⁻¹ with hc
  have hcK : c ∈ oddCoreIn (normalizer (I.E : Set X)) := by
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

end A7Base

end CFSG.ComponentClassification.HSFLit

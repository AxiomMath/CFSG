module

public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneCover

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.Plane

open CFSG.Open CFSG.AGLEmbedding

@[expose] def PLGood {Y : Type*} [Group Y] (J : Subgroup Y) (p : ℕ) : Prop :=
  ¬ p ^ 2 ∣ Nat.card J ∨ ∃ R : Subgroup Y, R ≤ J ∧ ⁅R, R⁆ = R ∧
    ∀ x ∈ J, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ R

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem PLGood.false_of_plane {J : Subgroup Y} {p : ℕ} (h : PLGood J p) (hp : p.Prime)
    (hcyc : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → ∀ Q : Subgroup Y, Q ≤ V → IsPGroup p Q →
      IsCyclic Q)
    {E : Subgroup Y} (hEJ : E ≤ J) (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    False := by
  rcases h with h | h
  · exact false_of_plane_of_card h hEJ hEc
  · exact false_of_plane_of_cover hp hcyc h hEJ hEel hEc

omit [Finite Y] in
theorem exists_psi {J : Subgroup Y} {X : Type*} [Group X]
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* X) :
    ∃ ψ : ↥J →* X, Function.Surjective ψ ∧ ∀ t, ψ t = 1 → ∃ m : ℕ, t ^ 2 ^ m = 1 := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun t ht => ?_⟩
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥J) t = 1 := by
    simpa using ht
  have h2 : t ∈ CFSG.pCore 2 ↥J := (QuotientGroup.eq_one_iff t).mp h1
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) ⟨t, h2⟩
  exact ⟨m, congrArg Subtype.val hm⟩

theorem plGood_of_perfect {J : Subgroup Y} {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* X) (B : Subgroup X) (hB : Group.IsPerfect B)
    (hX : ∀ x : X, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ B) : PLGood J p := by
  obtain ⟨ψ, hψ, hker⟩ := exists_psi e
  exact Or.inr (exists_perfect_cover J ψ hψ hker B hB hp hp2 hX)

theorem plGood_of_not_dvd {J : Subgroup Y} {X : Type*} [Group X] {p : ℕ}
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* X) (hp : p.Prime) (hp2 : p ≠ 2) (hX : ¬ p ^ 2 ∣ Nat.card X) :
    PLGood J p := by
  obtain ⟨ψ, hψ, hker⟩ := exists_psi e
  refine Or.inl fun h => ?_
  obtain ⟨a, ha⟩ := card_eq_two_pow_mul ψ hψ hker
  rw [ha] at h
  have hcop : Nat.Coprime (p ^ 2) (2 ^ a) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact hX (hcop.dvd_of_dvd_mul_left h)

theorem not_pow_two_dvd_factorial_le_four {p n : ℕ} (hp5 : 5 ≤ p) (hn : n ≤ 4) :
    ¬ p ^ 2 ∣ n.factorial := by
  intro h
  have h1 : p ^ 2 ≤ n.factorial := Nat.le_of_dvd (Nat.factorial_pos n) h
  have h2 : n.factorial ≤ 24 := by
    have := Nat.factorial_le hn
    simpa [Nat.factorial] using this
  have h3 : 25 ≤ p ^ 2 := by nlinarith
  omega

theorem plGood_perm {J : Subgroup Y} {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n)) : PLGood J p := by
  have hp2 : p ≠ 2 := by omega
  by_cases hn : n ≤ 4
  · refine plGood_of_not_dvd e hp hp2 ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    exact not_pow_two_dvd_factorial_le_four hp5 hn
  · have hn5 : 5 ≤ n := by omega
    refine plGood_of_perfect hp hp2 e (alternatingGroup (Fin n))
      (Subgroup.isPerfect_iff.mpr (commutator_alternatingGroup_eq_self (by
        rw [Nat.card_fin]; exact hn5))) ?_
    rintro σ ⟨k, hk⟩
    exact perm_mem_alternatingGroup_of_odd hp hp2 σ hk

theorem perm_central_p {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (z : Equiv.Perm (Fin n))
    (hz : ∀ w : Equiv.Perm (Fin n), w * z = z * w) (hzp : z ^ p = 1) : z = 1 := by
  by_cases hn : 3 ≤ n
  · exact perm_central_eq_one hn z hz
  ·
    have h1 : z ^ n.factorial = 1 := by
      have := pow_card_eq_one' (G := Equiv.Perm (Fin n)) (x := z)
      rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this
    have hcop : Nat.Coprime n.factorial p := by
      have hn2 : n.factorial ∣ 2 := by
        interval_cases n <;> decide
      exact Nat.Coprime.coprime_dvd_left hn2
        ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
    have := pow_gcd_eq_one.mpr ⟨h1, hzp⟩
    rwa [hcop.gcd_eq_one, pow_one] at this

theorem plGood_perm_prod {J : Subgroup Y} {r m p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 5 ≤ m)
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* (Equiv.Perm (Fin r) × Equiv.Perm (Fin m))) : PLGood J p := by
  have hp2 : p ≠ 2 := by omega
  have hAm : ⁅alternatingGroup (Fin m), alternatingGroup (Fin m)⁆ = alternatingGroup (Fin m) :=
    commutator_alternatingGroup_eq_self (by rw [Nat.card_fin]; exact hm)
  by_cases hr : 5 ≤ r
  · refine plGood_of_perfect hp hp2 e ((alternatingGroup (Fin r)).prod (alternatingGroup (Fin m)))
      (Subgroup.isPerfect_iff.mpr ?_) ?_
    · rw [Subgroup.commutator_prod_prod, hAm,
        commutator_alternatingGroup_eq_self (by rw [Nat.card_fin]; exact hr)]
    · rintro ⟨σ, τ⟩ ⟨k, hk⟩
      have hk' := Prod.ext_iff.mp (show (σ, τ) ^ p ^ k = 1 from hk)
      exact ⟨perm_mem_alternatingGroup_of_odd hp hp2 σ hk'.1,
        perm_mem_alternatingGroup_of_odd hp hp2 τ hk'.2⟩
  · refine plGood_of_perfect hp hp2 e ((⊥ : Subgroup (Equiv.Perm (Fin r))).prod
      (alternatingGroup (Fin m))) (Subgroup.isPerfect_iff.mpr ?_) ?_
    · rw [Subgroup.commutator_prod_prod, hAm, Subgroup.commutator_bot_left]
    · rintro ⟨σ, τ⟩ ⟨k, hk⟩
      have hk' := Prod.ext_iff.mp (show (σ, τ) ^ p ^ k = 1 from hk)
      refine ⟨?_, perm_mem_alternatingGroup_of_odd hp hp2 τ hk'.2⟩
      have h1 : σ ^ r.factorial = 1 := by
        have := pow_card_eq_one' (G := Equiv.Perm (Fin r)) (x := σ)
        rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this
      have hcop : Nat.Coprime r.factorial (p ^ k) := by
        refine Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp ?_)
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hd
        have h24 : p ∣ 2 ^ 3 * 3 :=
          hd.trans (by simpa [Nat.factorial] using
            Nat.factorial_dvd_factorial (show r ≤ 4 by omega))
        rcases (Nat.Prime.dvd_mul hp).mp h24 with h | h
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
          omega
        · have := Nat.le_of_dvd (by norm_num) h
          omega
      have := pow_gcd_eq_one.mpr ⟨h1, hk'.1⟩
      rw [hcop.gcd_eq_one, pow_one] at this
      rw [Subgroup.mem_bot.mpr this]
      exact Subgroup.one_mem _

end CFSG.HardMathSupport.Curtis.Coordinator.Plane

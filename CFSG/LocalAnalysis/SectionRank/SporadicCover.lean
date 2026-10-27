module

public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.J1

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint

variable {E S : Type*} [Group E] [Finite E] [Group S] [Finite S]

theorem isCyclic_or_isElemAbelian_of_card_eq_sq {P : Type*} [Group P] [Finite P] {p : ℕ}
    [hp : Fact p.Prime] (hP : Nat.card P = p ^ 2) :
    IsCyclic P ∨ (IsMulCommutative P ∧ ∀ x : P, x ^ p = 1) := by
  have hcomm : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hP
  by_cases hcyc : IsCyclic P
  · exact Or.inl hcyc
  · refine Or.inr ⟨hcomm, fun x => ?_⟩
    have hdvd : orderOf x ∣ p ^ 2 := hP ▸ orderOf_dvd_natCard x
    obtain ⟨k, hk, hx⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
    have hk2 : k ≠ 2 := by
      rintro rfl
      exact hcyc (isCyclic_of_orderOf_eq_card x (hx.trans hP.symm))
    have hk1 : k ≤ 1 := by omega
    have : orderOf x ∣ p := by
      rw [hx]
      simpa using pow_dvd_pow p hk1
    exact orderOf_dvd_iff_pow_eq_one.1 this

theorem odd_cover_one_square_order_bound [Group.IsPerfect E] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (π : E →* S) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (hℓS : ¬ ℓ ^ 3 ∣ Nat.card S)
    (hrS : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ ℓ → ¬ r ^ 2 ∣ Nat.card S) :
    (Nat.card π.ker = 1 ∨ Nat.card π.ker = ℓ) ∧
      ∀ (A : Subgroup E) [A.Normal], A ≤ π.ker → IsStronglyQuasithin (E ⧸ A) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hpos : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
  have hprime : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card π.ker → d = ℓ := by
    intro d hd hdvd
    have : Fact d.Prime := ⟨hd⟩
    by_contra hdℓ
    have hd2 : d ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
    obtain ⟨Cd⟩ := (inferInstance : Nonempty (Sylow d π.ker))
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow d S))
    exact Sylow.ne_bot_of_dvd_card Cd hdvd
      (CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC Cd Q
        (sylow_isCyclic_of_not_sq_dvd (hrS d hd hd2 hdℓ) Q))
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hpos hprime
  set k := (Nat.card π.ker).primeFactorsList.length with hk
  obtain ⟨Cℓ⟩ := (inferInstance : Nonempty (Sylow ℓ π.ker))
  have hCℓ := Sylow.card_eq_multiplicity Cℓ
  rw [hpow] at hCℓ
  simp only [Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self hℓ,
    smul_eq_mul, mul_one] at hCℓ
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow ℓ S))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 Q.isPGroup'
  have hm2 : m ≤ 2 := by
    by_contra hm2
    push Not at hm2
    have hdvd : ℓ ^ m ∣ Nat.card S := hm ▸ Subgroup.card_subgroup_dvd_card _
    exact hℓS ((pow_dvd_pow ℓ hm2).trans hdvd)
  have hCle : Nat.card (Cℓ : Subgroup π.ker) ≤ ℓ := by
    have hcases : IsCyclic (Q : Subgroup S) ∨
        (IsElemAbelian ℓ (Q : Subgroup S) ∧ Nat.card (Q : Subgroup S) = ℓ ^ 2) := by
      interval_cases m
      · rw [pow_zero] at hm
        have : Subsingleton (Q : Subgroup S) := (Nat.card_eq_one_iff_unique.1 hm).1
        exact Or.inl isCyclic_of_subsingleton
      · rw [pow_one] at hm
        exact Or.inl (isCyclic_of_prime_card hm)
      · rcases isCyclic_or_isElemAbelian_of_card_eq_sq hm with h | ⟨hc, hx⟩
        · exact Or.inl h
        · refine Or.inr ⟨⟨hc, fun y hy => ?_⟩, hm⟩
          exact congrArg Subtype.val (hx ⟨y, hy⟩)
    rcases hcases with hcyc | ⟨helem, hcard⟩
    · rw [CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC Cℓ Q hcyc,
        Subgroup.card_bot]
      exact hℓ.one_lt.le
    · exact (CFSG.ShultStronglyClosedTI.central_cover_elementary_rank_two_sylow_kernel_bound π hπ
        hC Cℓ Q helem hcard).2
  rw [hCℓ] at hCle
  have hk1 : k ≤ 1 := by
    by_contra hk1
    push Not at hk1
    have : ℓ ^ 2 ≤ ℓ ^ k := Nat.pow_le_pow_right hℓ.pos hk1
    have := hℓ.two_le
    nlinarith
  have hcard : Nat.card π.ker = 1 ∨ Nat.card π.ker = ℓ := by
    interval_cases k
    · left; rw [hpow, pow_zero]
    · right; rw [hpow, pow_one]
  refine ⟨hcard, ?_⟩
  have hSQT_S : IsStronglyQuasithin S := by
    rw [isStronglyQuasithin_iff]
    intro r hr hr2
    have : Fact r.Prime := ⟨hr⟩
    refine pRank_le hr.one_lt fun F _ hF => ?_
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (show IsPGroup r F from fun g => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hF.2 _ g.2)⟩)
    have hdvd : r ^ j ∣ Nat.card S := hj ▸ Subgroup.card_subgroup_dvd_card F
    rw [hj]
    refine Nat.pow_le_pow_right hr.pos ?_
    by_contra hj2
    push Not at hj2
    by_cases hrℓ : r = ℓ
    · subst hrℓ
      exact hℓS ((pow_dvd_pow r hj2).trans hdvd)
    · exact hrS r hr hr2 hrℓ ((pow_dvd_pow r (by omega : 2 ≤ j)).trans hdvd)
  let eS : E ⧸ π.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have hSQT_E : IsStronglyQuasithin E := by
    rw [isStronglyQuasithin_iff]
    intro r hr hr2
    have : Fact r.Prime := ⟨hr⟩
    by_cases hrℓ : r = ℓ
    · subst hrℓ
      rcases hcard with h1 | h3
      ·
        have hbot : π.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
        have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hbot
        exact (pRank_top_le_of_injective hr.one_lt π hinj).trans
          (isStronglyQuasithin_iff.1 hSQT_S r hr hr2)
      ·
        refine pRank_le hr.one_lt fun F _ hF => ?_
        have hFp : IsPGroup r F := fun g => ⟨1, Subtype.ext (by
          rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hF.2 _ g.2)⟩
        obtain ⟨P, hFP⟩ := hFp.exists_le_sylow
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hFp
        have hE : Nat.card E = Nat.card S * r := by
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker, Nat.card_congr eS.toEquiv,
            h3]
        have hle3 : ∀ i, r ^ i ∣ Nat.card E → i ≤ 3 := by
          intro i hi
          by_contra hi3
          push Not at hi3
          have h4 : r ^ 3 * r ∣ Nat.card S * r := by
            rw [← pow_succ, ← hE]
            exact (pow_dvd_pow r hi3).trans hi
          exact hℓS (Nat.dvd_of_mul_dvd_mul_right hr.pos h4)
        have hj3 : j ≤ 3 := hle3 j (hj ▸ Subgroup.card_subgroup_dvd_card F)
        rw [hj]
        refine Nat.pow_le_pow_right hr.pos ?_
        by_contra hj2
        push Not at hj2
        have hj3' : j = 3 := by omega
        subst hj3'
        obtain ⟨i, hi⟩ := IsPGroup.iff_card.1 P.isPGroup'
        have hi3 : i ≤ 3 := hle3 i (hi ▸ Subgroup.card_subgroup_dvd_card _)
        have hFeq : F = P := Subgroup.eq_of_le_of_card_ge hFP (by
          rw [hi, hj]; exact Nat.pow_le_pow_right hr.pos hi3)
        have hcomm : IsMulCommutative (P : Subgroup E) := hFeq ▸ hF.1
        have hker := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P π.ker hC
          (IsPGroup.of_card (by rw [h3, pow_one]))
        rw [commutator_eq_bot (P : Subgroup E), Subgroup.map_bot, le_bot_iff] at hker
        rw [hker, Subgroup.card_bot] at h3
        exact hr.one_lt.ne h3
    ·
      have hcop : ¬ r ∣ Nat.card π.ker := by
        rcases hcard with h1 | h3
        · rw [h1]; exact hr.not_dvd_one
        · rw [h3]; intro h
          exact hrℓ ((Nat.prime_dvd_prime_iff_eq hr hℓ).1 h)
      rw [← pRank_quotient_eq π.ker hcop, pRank_top_eq_of_mulEquiv hr.one_lt eS]
      exact isStronglyQuasithin_iff.1 hSQT_S r hr hr2
  intro A _ hA
  have hdvd : Nat.card A ∣ Nat.card π.ker := Subgroup.card_dvd_of_le hA
  have hA1 : Nat.card A = 1 ∨ A = π.ker := by
    rcases hcard with h1 | hℓ'
    · exact Or.inl (Nat.dvd_one.1 (h1 ▸ hdvd))
    · rw [hℓ'] at hdvd
      rcases (Nat.dvd_prime hℓ).1 hdvd with h1 | hAℓ
      · exact Or.inl h1
      · exact Or.inr (Subgroup.eq_of_le_of_card_ge hA (by rw [hAℓ, hℓ']))
  rcases hA1 with h1 | rfl
  · obtain rfl : A = ⊥ := Subgroup.eq_bot_of_card_eq A h1
    exact isStronglyQuasithin_of_mulEquiv QuotientGroup.quotientBot hSQT_E
  · exact isStronglyQuasithin_of_mulEquiv eS hSQT_S

theorem ker_eq_bot_of_not_sq_dvd [Group.IsPerfect E] (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker))
    (hrS : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ^ 2 ∣ Nat.card S) : π.ker = ⊥ := by
  by_contra hne
  have hnt : Nontrivial π.ker := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card_iff_nontrivial.2 hnt).ne'
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrd)
  obtain ⟨Cr⟩ := (inferInstance : Nonempty (Sylow r π.ker))
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r S))
  exact Sylow.ne_bot_of_dvd_card Cr hrd
    (CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC Cr Q
      (sylow_isCyclic_of_not_sq_dvd (hrS r hr hr2) Q))

theorem not_sq_dvd_of_not_sq_dvd_cofactor {r a b m : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hm : ¬ r ^ 2 ∣ m) : ¬ r ^ 2 ∣ 2 ^ a * 3 ^ b * m := by
  intro h
  have hcop : Nat.Coprime (r ^ 2) (2 ^ a * 3 ^ b) := by
    refine Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right ?_ ?_)
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_three).2 hr3)
  exact hm (hcop.dvd_of_dvd_mul_left h)

theorem not_sq_dvd_of_bound {r m B : ℕ} (hm : 0 < m) (hB : m < B ^ 2)
    (hcheck : ∀ r < B, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 2 ∣ m) (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) : ¬ r ^ 2 ∣ m := by
  intro h
  have hle := Nat.le_of_dvd hm h
  have hrB : r < B := by
    by_contra hrB
    push Not at hrB
    have : B ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hrB 2
    omega
  exact hcheck r hrB hr hr2 hr3 h

theorem card_small_sporadic
    {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M22 ∨ s = .M23 ∨ s = .J1) :
    Nat.card (NativeSporadic.Carrier s) = 7920 ∨ Nat.card (NativeSporadic.Carrier s) = 443520 ∨
      Nat.card (NativeSporadic.Carrier s) = 10200960 ∨
      Nat.card (NativeSporadic.Carrier s) = 175560 := by
  rcases hs with rfl | rfl | rfl | rfl
  · exact Or.inl CFSG.Sporadic.Mathieu.card_M11
  · exact Or.inr (Or.inl CFSG.Sporadic.Mathieu.card_M22)
  · refine Or.inr (Or.inr (Or.inl ?_))
    change Nat.card NativeSporadic.M23 = _
    rw [CFSG.Sporadic.Mathieu.nativeM23_eq, Nat.card_eq_fintype_card]
    exact CFSG.M23.M23Group.card_M23
  · exact Or.inr (Or.inr (Or.inr CFSG.Sporadic.J1.card_J1))

theorem small_sporadic_order_conditions {n : ℕ}
    (hn : n = 7920 ∨ n = 443520 ∨ n = 10200960 ∨ n = 175560) :
    ¬ 3 ^ 3 ∣ n ∧ ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 2 ∣ n := by
  refine ⟨by rcases hn with rfl | rfl | rfl | rfl <;> decide, fun r hr hr2 hr3 => ?_⟩
  rcases hn with rfl | rfl | rfl | rfl
  · rw [show 7920 = 2 ^ 4 * 3 ^ 2 * 55 by norm_num]
    exact not_sq_dvd_of_not_sq_dvd_cofactor hr hr2 hr3
      (not_sq_dvd_of_bound (B := 8) (by norm_num) (by norm_num) (by decide) hr hr2 hr3)
  · rw [show 443520 = 2 ^ 7 * 3 ^ 2 * 385 by norm_num]
    exact not_sq_dvd_of_not_sq_dvd_cofactor hr hr2 hr3
      (not_sq_dvd_of_bound (B := 20) (by norm_num) (by norm_num) (by decide) hr hr2 hr3)
  · rw [show 10200960 = 2 ^ 7 * 3 ^ 2 * 8855 by norm_num]
    exact not_sq_dvd_of_not_sq_dvd_cofactor hr hr2 hr3
      (not_sq_dvd_of_bound (B := 95) (by norm_num) (by norm_num) (by decide) hr hr2 hr3)
  · rw [show 175560 = 2 ^ 3 * 3 ^ 1 * 7315 by norm_num]
    exact not_sq_dvd_of_not_sq_dvd_cofactor hr hr2 hr3
      (not_sq_dvd_of_bound (B := 86) (by norm_num) (by norm_num) (by decide) hr hr2 hr3)

theorem four_small_sporadic_odd_cover_step
    {L : Type} [Group L] [Finite L] (hL : IsQuasisimple L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M22 ∨ s = .M23 ∨ s = .J1)
    (e : L ⧸ Subgroup.center L ≃* NativeSporadic.Carrier s) :
    CatalogStepConclusion L ∧ (s = .J1 → Subgroup.center L = ⊥) := by
  have : Group.IsPerfect L := hL.1
  have : Finite (NativeSporadic.Carrier s) := Finite.of_equiv _ e.toEquiv
  let π : L →* NativeSporadic.Carrier s :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hC : π.ker ≤ Subgroup.center L := hker.le
  have hodd' : Odd (Nat.card π.ker) := by rw [hker]; exact hodd
  obtain ⟨h27, hr⟩ := small_sporadic_order_conditions (card_small_sporadic hs)
  obtain ⟨h13, hquot⟩ := odd_cover_one_square_order_bound Nat.prime_three (by norm_num) π hπ hC
    hodd' h27 hr
  refine ⟨⟨hker ▸ h13, fun A _ hA => hquot A (hker ▸ hA)⟩, fun hJ1 => ?_⟩
  subst hJ1
  rw [← hker]
  refine ker_eq_bot_of_not_sq_dvd π hπ hC hodd' fun r hr' hr2 => ?_
  change ¬ r ^ 2 ∣ Nat.card NativeSporadic.J1
  rw [CFSG.Sporadic.J1.card_J1]
  by_cases hr3 : r = 3
  · subst hr3
    decide
  · exact (small_sporadic_order_conditions (n := 175560) (by norm_num)).2 r hr' hr2 hr3

end CFSG.SectionRank

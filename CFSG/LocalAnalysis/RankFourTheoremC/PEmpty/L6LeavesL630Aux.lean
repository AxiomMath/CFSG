module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup

theorem prime_eq_two_three_or_five {q : ℕ} (hq : q.Prime) (h : q ∣ 720) :
    q = 2 ∨ q = 3 ∨ q = 5 := by
  have h' : q ∣ 2 ^ 4 * 3 ^ 2 * 5 := by
    norm_num
    exact h
  rcases (Nat.Prime.dvd_mul hq).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
        (hq.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1))

theorem card_perm_fin_six : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_dvd_of_isInvolvedIn {H : Type} [Group H]
    (hH : IsInvolvedIn H (Equiv.Perm (Fin 6))) : Nat.card H ∣ 720 := by
  have hH' : ∃ (A : Subgroup (Equiv.Perm (Fin 6))) (N : Subgroup A) (_ : N.Normal),
      Nonempty ((A ⧸ N) ≃* H) := hH
  obtain ⟨A, N, _, ⟨e⟩⟩ := hH'
  rw [← card_perm_fin_six, ← Nat.card_congr e.toEquiv]
  exact (Subgroup.card_quotient_dvd_card N).trans (Subgroup.card_subgroup_dvd_card A)

theorem pow_fixes {E : Type} [Group E] {δ : MulAut E} {a : E} (h : δ a = a) (n : ℕ) :
    (δ ^ n) a = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, h, ih]

theorem scalar_eq_one {E : Type} [Group E] {f : ℕ} (hf : f.Prime) (hexp : ∀ e : E, e ^ f = 1)
    (g : MulAut E) {k : ℕ} (hk : ∀ e : E, g e = e ^ k) {a : E} (ha1 : a ≠ 1) (hga : g a = a) :
    g = 1 := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hoa : orderOf a = f := orderOf_eq_prime (hexp a) ha1
  have hak : a ^ k = a ^ 1 := by
    rw [pow_one, ← hk a, hga]
  have hkmod : k ≡ 1 [MOD orderOf a] := pow_eq_pow_iff_modEq.mp hak
  rw [hoa] at hkmod
  ext e
  rw [MulAut.one_apply, hk e]
  have hdvd : orderOf e ∣ f := orderOf_dvd_of_pow_eq_one (hexp e)
  have hem : k ≡ 1 [MOD orderOf e] := Nat.ModEq.of_dvd hdvd hkmod
  exact (pow_eq_pow_iff_modEq.mpr hem).trans (pow_one e)

theorem two_pow_mem_ker_of_fixed {Γ : Type} [Group Γ] [Finite Γ] {E : Type} [Group E]
    (ψ : Γ →* MulAut E)
    (hfree : ∀ g : Γ, ∀ q : ℕ, q.Prime → q ≠ 2 → orderOf (ψ g) = q →
      ∀ a : E, ψ g a = a → a = 1)
    (g : Γ) {a : E} (hga : ψ g a = a) (ha : a ≠ 1) : ∃ n : ℕ, ψ (g ^ (2 ^ n)) = 1 := by
  have hpos : 0 < orderOf g := orderOf_pos g
  have hdvd : orderOf (ψ g) ∣ orderOf g := orderOf_map_dvd ψ g
  have hne : orderOf (ψ g) ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff] at hdvd
    omega
  obtain ⟨k, m, hmodd, hm⟩ := Nat.exists_eq_two_pow_mul_odd hne
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hdvd2 : 2 ^ k ∣ orderOf (ψ g) := ⟨m, hm⟩
  have hβ : orderOf ((ψ g) ^ (2 ^ k)) = m := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd2, hm, Nat.mul_div_cancel_left m (by positivity)]
  by_cases hm1 : m = 1
  · refine ⟨k, ?_⟩
    rw [map_pow]
    exact orderOf_eq_one_iff.mp (hβ.trans hm1)
  · exfalso
    obtain ⟨q, hqp, hqm⟩ := Nat.exists_prime_and_dvd hm1
    have hq2 : q ≠ 2 := by
      rintro rfl
      obtain ⟨c, hc⟩ := hqm
      rw [hc] at hmodd
      exact (Nat.not_even_iff_odd.mpr hmodd) ⟨c, by ring⟩
    have hqdiv : m / q ∣ m := Nat.div_dvd_of_dvd hqm
    have hqpos : m / q ≠ 0 := by
      intro h0
      have := Nat.div_mul_cancel hqm
      rw [h0, zero_mul] at this
      exact hm0 this.symm
    have hord : orderOf (((ψ g) ^ (2 ^ k)) ^ (m / q)) = q := by
      rw [orderOf_pow_of_dvd hqpos (by rw [hβ]; exact hqdiv), hβ, Nat.div_div_self hqm hm0]
    have hfixβ : (((ψ g) ^ (2 ^ k)) ^ (m / q)) a = a :=
      pow_fixes (pow_fixes hga (2 ^ k)) (m / q)
    have hmap : ψ (g ^ (2 ^ k * (m / q))) = ((ψ g) ^ (2 ^ k)) ^ (m / q) := by
      rw [map_pow, pow_mul]
    have hg' : orderOf (ψ (g ^ (2 ^ k * (m / q)))) = q := by
      rw [hmap, hord]
    have hfix' : ψ (g ^ (2 ^ k * (m / q))) a = a := by
      rw [hmap]
      exact hfixβ
    exact ha (hfree _ q hqp hq2 hg' a hfix')

theorem eq_one_of_mem_odd_two {Y : Type} [Group Y] [Finite Y] {O Q : Subgroup Y}
    (hO : ¬ 2 ∣ Nat.card O) (hQ : IsPGroup 2 Q) {c : Y} (hcO : c ∈ O) (hcQ : c ∈ Q) :
    c = 1 := by
  obtain ⟨n, hn⟩ := hQ ⟨c, hcQ⟩
  have h2n : c ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hdQ : orderOf c ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2n
  have hdO : orderOf c ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨c, hcO⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  have hnot2 : ¬ 2 ∣ orderOf c := fun h => hO (h.trans hdO)
  have hcop : Nat.Coprime (orderOf c) (2 ^ n) :=
    Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnot2).symm
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdQ)

theorem mul_decomp_of_mem_sup {Y : Type} [Group Y] (X O Q : Subgroup Y)
    (hOX : O ≤ X) (hQX : Q ≤ X) (hO : (O.subgroupOf X).Normal) (hQ : (Q.subgroupOf X).Normal)
    {w : Y} (hwOQ : w ∈ O ⊔ Q) (hwX : w ∈ X) : ∃ o ∈ O, ∃ t ∈ Q, w = o * t := by
  let T : Subgroup Y :=
    { carrier := {w | w ∈ X ∧ ∃ o ∈ O, ∃ t ∈ Q, w = o * t}
      one_mem' := ⟨X.one_mem, 1, O.one_mem, 1, Q.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro a b ⟨haX, o1, ho1, t1, ht1, rfl⟩ ⟨hbX, o2, ho2, t2, ht2, rfl⟩
        have hc : t1 * o2 * t1⁻¹ ∈ O := by
          have := hO.conj_mem (⟨o2, hOX ho2⟩ : ↥X) (Subgroup.mem_subgroupOf.mpr ho2)
            (⟨t1, hQX ht1⟩ : ↥X)
          rw [Subgroup.mem_subgroupOf] at this
          simpa using this
        refine ⟨X.mul_mem haX hbX, o1 * (t1 * o2 * t1⁻¹), O.mul_mem ho1 hc, t1 * t2,
          Q.mul_mem ht1 ht2, ?_⟩
        group
      inv_mem' := by
        rintro a ⟨haX, o1, ho1, t1, ht1, rfl⟩
        have hc : t1⁻¹ * o1⁻¹ * t1 ∈ O := by
          have := hO.conj_mem (⟨o1⁻¹, X.inv_mem (hOX ho1)⟩ : ↥X)
            (Subgroup.mem_subgroupOf.mpr (O.inv_mem ho1)) (⟨t1⁻¹, X.inv_mem (hQX ht1)⟩ : ↥X)
          rw [Subgroup.mem_subgroupOf] at this
          simpa using this
        refine ⟨X.inv_mem haX, t1⁻¹ * o1⁻¹ * t1, hc, t1⁻¹, Q.inv_mem ht1, ?_⟩
        group }
  have hle : O ⊔ Q ≤ T := by
    refine sup_le (fun o ho => ⟨hOX ho, o, ho, 1, Q.one_mem, (mul_one o).symm⟩)
      (fun t ht => ⟨hQX ht, 1, O.one_mem, t, ht, (one_mul t).symm⟩)
  obtain ⟨_, hw⟩ := hle hwOQ
  exact hw

theorem mem_of_odd_of_mem_sup {Y : Type} [Group Y] [Finite Y] (X O Q : Subgroup Y)
    (hOX : O ≤ X) (hQX : Q ≤ X) (hO : (O.subgroupOf X).Normal) (hQ : (Q.subgroupOf X).Normal)
    (hOodd : ¬ 2 ∣ Nat.card O) (hQ2 : IsPGroup 2 Q) {w : Y} (hwX : w ∈ X)
    (hwOQ : w ∈ O ⊔ Q) (hwodd : Odd (orderOf w)) : w ∈ O := by
  obtain ⟨o, ho, t, ht, rfl⟩ := mul_decomp_of_mem_sup X O Q hOX hQX hO hQ hwOQ hwX
  have hoX : o ∈ X := hOX ho
  have htX : t ∈ X := hQX ht
  have hcomm : o * t = t * o := by
    have hc1 : o * t * o⁻¹ * t⁻¹ ∈ Q := by
      have h1 : o * t * o⁻¹ ∈ Q := by
        have := hQ.conj_mem (⟨t, htX⟩ : ↥X) (Subgroup.mem_subgroupOf.mpr ht) (⟨o, hoX⟩ : ↥X)
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
      exact Q.mul_mem h1 (Q.inv_mem ht)
    have hc2 : o * t * o⁻¹ * t⁻¹ ∈ O := by
      have h2 : t * o⁻¹ * t⁻¹ ∈ O := by
        have := hO.conj_mem (⟨o⁻¹, X.inv_mem hoX⟩ : ↥X)
          (Subgroup.mem_subgroupOf.mpr (O.inv_mem ho)) (⟨t, htX⟩ : ↥X)
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
      have hrw : o * t * o⁻¹ * t⁻¹ = o * (t * o⁻¹ * t⁻¹) := by group
      rw [hrw]
      exact O.mul_mem ho h2
    have hc : o * t * o⁻¹ * t⁻¹ = 1 := eq_one_of_mem_odd_two hOodd hQ2 hc2 hc1
    calc o * t = (o * t * o⁻¹ * t⁻¹) * (t * o) := by group
      _ = t * o := by rw [hc, one_mul]
  set m := orderOf (o * t) with hmdef
  have hpow : o ^ m * t ^ m = 1 := by
    rw [← Commute.mul_pow (show Commute o t from hcomm) m]
    exact pow_orderOf_eq_one (o * t)
  have htm : t ^ m = 1 := by
    have hinv : t ^ m = (o ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hpow
    have hmemO : t ^ m ∈ O := by
      rw [hinv]
      exact O.inv_mem (O.pow_mem ho m)
    exact eq_one_of_mem_odd_two hOodd hQ2 hmemO (Q.pow_mem ht m)
  have ht1 : t = 1 := by
    obtain ⟨n, hn⟩ := hQ2 ⟨t, ht⟩
    have h2n : t ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hd1 : orderOf t ∣ m := orderOf_dvd_of_pow_eq_one htm
    have hd2 : orderOf t ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2n
    have h2m : Nat.Coprime 2 m :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hwodd.not_two_dvd_nat
    have hcop2 : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n h2m
    have hcop : Nat.Coprime (orderOf t) m := Nat.Coprime.coprime_dvd_left hd2 hcop2
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hd1)
  rw [ht1, mul_one]
  exact ho

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

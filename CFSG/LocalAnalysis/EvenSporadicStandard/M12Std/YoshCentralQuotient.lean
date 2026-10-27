module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshInput
import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshBurnside

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open scoped commutatorElement

theorem commutator_eq_top_of_normalizer_le {C : Type*} [Group C] [Finite C] (S L : Subgroup C)
    (hS : Nat.card S = 2 ^ (Nat.card C).factorization 2) (hSL : S ≤ L)
    (hLperf : ⁅L, L⁆ = L)
    (hnorm : ∀ p : C, p ∈ Subgroup.normalizer (S : Set C) → p ∈ L) :
    commutator C = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLC : L ≤ commutator C :=
    calc L = ⁅L, L⁆ := hLperf.symm
      _ ≤ commutator C := Subgroup.commutator_mono le_top le_top
  let P : Sylow 2 C := Sylow.ofCard S hS
  haveI : Finite (Sylow 2 C) := Sylow.finite_of_finiteIndex P
  have hPN : (P : Subgroup C) ≤ commutator C := hSL.trans hLC
  have hfrat := Sylow.normalizer_sup_eq_top' P hPN
  have hle : Subgroup.normalizer (P : Set C) ≤ commutator C := fun p hp => hLC (hnorm p hp)
  rwa [sup_eq_right.2 hle] at hfrat

theorem odd_normal_eq_bot_of_order_three {G : Type*} [Group G] [Finite G] (H Q : Subgroup G)
    (hH : Nat.card H = 384) (hQH : Q ≤ H) (hQn : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (hodd : Odd (Nat.card Q))
    (hfact : ∀ y ∈ H, orderOf y = 3 → ∃ z ∈ H, z * y * z⁻¹ ∉ Subgroup.zpowers y) : Q = ⊥ := by
  by_contra hne
  have hdvd : Nat.card Q ∣ 2 ^ 7 * 3 := by
    have h := Subgroup.card_dvd_of_le hQH
    rwa [hH, show (384 : ℕ) = 2 ^ 7 * 3 by norm_num] at h
  have hQ3 : Nat.card Q = 3 := by
    have h2 : ¬ 2 ∣ Nat.card Q := by
      rintro ⟨j, hj⟩
      obtain ⟨k, hk⟩ := hodd
      omega
    have hcop : Nat.Coprime (Nat.card Q) (2 ^ 7) :=
      Nat.Coprime.pow_right 7 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2).symm
    rcases (Nat.dvd_prime Nat.prime_three).1 (hcop.dvd_of_dvd_mul_left hdvd) with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq Q h) hne
    · exact h
  obtain ⟨⟨y, hyQ⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hord : orderOf y = 3 := by
    have hd : orderOf y ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard Q hyQ
      rwa [hQ3] at h
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1'
    · exact h
  have hzp : Subgroup.zpowers y = Q := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hyQ) (le_of_eq ?_)
    rw [Nat.card_zpowers, hord, hQ3]
  obtain ⟨z, hzH, hz⟩ := hfact y (hQH hyQ) hord
  exact hz (by rw [hzp]; exact hQn z hzH y hyQ)

theorem center_quotient_eq_bot_of_commutators_mem_center {C : Type*} [Group C]
    (hZZ : ∀ z : C, (∀ y : C, ⁅z, y⁆ ∈ Subgroup.center C) → z ∈ Subgroup.center C) :
    Subgroup.center (C ⧸ Subgroup.center C) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  refine (QuotientGroup.eq_one_iff z).2 (hZZ z fun y => (QuotientGroup.eq_one_iff _).1 ?_)
  have hxy : (y : C ⧸ Subgroup.center C) * z = z * y := Subgroup.mem_center_iff.1 hx y
  show (QuotientGroup.mk' (Subgroup.center C)) ⁅z, y⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hxy.symm

theorem eq_top_of_isPGroup_quotient_of_isPerfect {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] (N : Subgroup K) [N.Normal] (hN : IsPGroup 2 (K ⧸ N)) : N = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Subsingleton (K ⧸ N) := by
    by_contra hns
    haveI : Nontrivial (K ⧸ N) := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hN.isNilpotent
  exact eq_top_iff.2 fun k _ => (QuotientGroup.eq_one_iff k).1 (Subsingleton.elim _ _)

theorem odd_normal_quotient_eq_bot_of_central_order_two {C : Type*} [Group C] [Finite C]
    (Z : Subgroup C) [Z.Normal] (hZc : ∀ z ∈ Z, ∀ g : C, z * g = g * z) (hZ2 : Nat.card Z = 2)
    (hO : ∀ Q : Subgroup C, Q.Normal → Odd (Nat.card Q) → Q = ⊥)
    (Qbar : Subgroup (C ⧸ Z)) [Qbar.Normal] (hodd : Odd (Nat.card Qbar)) : Qbar = ⊥ := by
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup C, Q = Qbar.comap (QuotientGroup.mk' Z) := ⟨_, rfl⟩
  haveI hQn : Q.Normal := by
    rw [hQ]
    exact Subgroup.Normal.comap inferInstance _
  have hQmem : ∀ x : C, x ∈ Q ↔ (x : C ⧸ Z) ∈ Qbar := fun x => by rw [hQ]; rfl
  have hZQ : Z ≤ Q := fun z hz => (hQmem z).2 (by
    rw [(QuotientGroup.eq_one_iff z).2 hz]
    exact Qbar.one_mem)
  have hQcard : Nat.card Q = 2 * Nat.card Qbar := by
    have h1 : Nat.card Q * Q.index = Nat.card C := Subgroup.card_mul_index Q
    have h2 : Nat.card Qbar * Qbar.index = Nat.card (C ⧸ Z) := Subgroup.card_mul_index Qbar
    have h3 : Nat.card (C ⧸ Z) * Nat.card Z = Nat.card C :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
    have h4 : Q.index = Qbar.index := by
      rw [hQ]
      exact Subgroup.index_comap_of_surjective Qbar (QuotientGroup.mk'_surjective Z)
    have h5 : Qbar.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h5) ?_
    calc Nat.card Q * Qbar.index = Nat.card C := by rw [← h4]; exact h1
      _ = Nat.card (C ⧸ Z) * Nat.card Z := h3.symm
      _ = 2 * Nat.card Qbar * Qbar.index := by rw [← h2, hZ2]; ring
  have hfac : (Nat.card Q).factorization 2 = 1 := by
    rw [hQcard, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd, add_zero]
    rintro ⟨j, hj⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  have hA : Nat.card Z = 2 ^ (Nat.card Q).factorization 2 := by rw [hfac, hZ2, pow_one]
  obtain ⟨K₀, hK₀Q, hK₀odd, hQK₀, -⟩ :=
    exists_normal_twoComplement Q Z hZQ (fun a ha h _ => hZc a ha h) hA
  haveI hK₀n : K₀.Normal := ⟨fun k hk g => by
    have hkQ : k ∈ Q := hK₀Q hk
    have hconj : g * k * g⁻¹ ∈ Q := hQn.conj_mem k hkQ g
    have hs : SemiconjBy g k (g * k * g⁻¹) := (inv_mul_cancel_right (g * k) g).symm
    refine (hK₀odd _ hconj).2 ?_
    rw [← SemiconjBy.orderOf_eq g hs]
    exact (hK₀odd k hkQ).1 hk⟩
  have hK₀card : Nat.card K₀ = Nat.card Qbar := by
    rw [hQcard, hZ2] at hQK₀
    omega
  have hK₀bot : K₀ = ⊥ := hO K₀ hK₀n (by rw [hK₀card]; exact hodd)
  refine Subgroup.eq_bot_of_card_eq Qbar ?_
  rw [← hK₀card, hK₀bot, Subgroup.card_bot]

theorem fusionSimple_quotient {C : Type} [Group C] [Finite C]
    (hperf : commutator C = ⊤)
    (hO : ∀ Q : Subgroup C, Q.Normal → Odd (Nat.card Q) → Q = ⊥)
    (hZ2 : Nat.card (Subgroup.center C) = 2)
    (hZZ : ∀ z : C, (∀ y : C, ⁅z, y⁆ ∈ Subgroup.center C) → z ∈ Subgroup.center C) :
    CFSG.EvenSporadicStandard.M12Std.FusionSimple (C ⧸ Subgroup.center C) := by
  haveI : Group.IsPerfect C := Group.isPerfect_def.2 hperf
  unfold CFSG.EvenSporadicStandard.M12Std.FusionSimple
  exact ⟨fun Qbar _ hodd => odd_normal_quotient_eq_bot_of_central_order_two (Subgroup.center C)
      (fun z hz g => (Subgroup.mem_center_iff.1 hz g).symm) hZ2 hO Qbar hodd,
    center_quotient_eq_bot_of_commutators_mem_center hZZ,
    fun N _ hN => eq_top_of_isPGroup_quotient_of_isPerfect N hN⟩

theorem exists_normal_isPGroup_of_commutators_mem_pair {C : Type*} [Group C] [Finite C] (c : C)
    (hc : c ∈ Subgroup.center C) (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hO : ∀ Q : Subgroup C, Q.Normal → Odd (Nat.card Q) → Q = ⊥) :
    ∃ W : Subgroup C, W.Normal ∧ IsPGroup 2 W ∧
      ∀ z : C, (∀ y : C, ⁅z, y⁆ = 1 ∨ ⁅z, y⁆ = c) → z ∈ W := by
  have hcc : ∀ g : C, g * c = c * g := Subgroup.mem_center_iff.1 hc
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hconj : ∀ g : C, g * c * g⁻¹ = c := fun g => by rw [hcc g, mul_inv_cancel_right]
  have hcpow : ∀ n : ℕ, Odd n → c ^ n = c := by
    rintro n ⟨k, rfl⟩
    rw [pow_succ, pow_mul, sq, hc2, one_pow, one_mul]
  obtain ⟨W, hWmem⟩ : ∃ W : Subgroup C, ∀ z, z ∈ W ↔ ∀ y, ⁅z, y⁆ = 1 ∨ ⁅z, y⁆ = c := by
    refine ⟨{ carrier := {z | ∀ y, ⁅z, y⁆ = 1 ∨ ⁅z, y⁆ = c}
              one_mem' := fun y => Or.inl (commutatorElement_one_left y)
              mul_mem' := ?_
              inv_mem' := ?_ }, fun z => Iff.rfl⟩
    · intro a b ha hb y
      have key : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ :=
        commutatorElement_mul_left_eq_conj_mul a b y
      rw [key]
      rcases hb y with h1 | h1 <;> rcases ha y with h2 | h2 <;> rw [h1, h2] <;>
        simp [hconj, hc2]
    · intro a ha y
      have key : ⁅a⁻¹, y⁆ = (a⁻¹ * ⁅a, y⁆ * a)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [key]
      rcases ha y with h1 | h1
      · rw [h1]; simp
      · have hc' : a⁻¹ * c * a = c := by simpa using hconj a⁻¹
        rw [h1, hc', hcinv]
        exact Or.inr rfl
  have hWn : W.Normal := ⟨fun n hn g => (hWmem _).2 fun y => by
    have key : ⁅g * n * g⁻¹, y⁆ = g * ⁅n, g⁻¹ * y * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [key]
    rcases (hWmem n).1 hn (g⁻¹ * y * g) with h1 | h1
    · rw [h1]; simp
    · rw [h1, hconj]
      exact Or.inr rfl⟩
  have hodd : ∀ w ∈ W, Odd (orderOf w) → w = 1 := by
    intro w hw ho
    have hcen : ∀ g : C, g * w * g⁻¹ = w := by
      intro g
      have hconjw : g * w * g⁻¹ = ⁅w, g⁆⁻¹ * w := by
        simp only [commutatorElement_def]; group
      rcases (hWmem w).1 hw g with h1 | h1
      · rw [hconjw, h1, inv_one, one_mul]
      · exfalso
        rw [h1, hcinv] at hconjw
        have h2 : (g * w * g⁻¹) ^ orderOf w = 1 := by
          rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
        rw [hconjw, Commute.mul_pow ((hcc w).symm), pow_orderOf_eq_one, mul_one,
          hcpow _ ho] at h2
        exact hc1 h2
    haveI : (Subgroup.zpowers w).Normal := ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      rw [← conj_zpow, hcen g]
      exact Subgroup.zpow_mem_zpowers w k⟩
    refine Subgroup.zpowers_eq_bot.1 (hO _ inferInstance ?_)
    rwa [Nat.card_zpowers]
  have hpow : ∀ z ∈ W, ∃ k : ℕ, z ^ 2 ^ k = 1 := by
    intro z hz
    obtain ⟨k, m, hm, hzm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
    have h2k : (2 : ℕ) ^ k ≠ 0 := by positivity
    have hdvd : 2 ^ k ∣ orderOf z := by rw [hzm]; exact dvd_mul_right _ _
    have hord : orderOf (z ^ 2 ^ k) = m := by
      rw [orderOf_pow_of_dvd h2k hdvd, hzm, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h2k)]
    exact ⟨k, hodd _ (W.pow_mem hz _) (by rw [hord]; exact hm)⟩
  refine ⟨W, hWn, fun g => ?_, fun z hz => (hWmem z).2 hz⟩
  obtain ⟨k, hk⟩ := hpow g g.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem second_center_le {C : Type*} [Group C] [Finite C] (c : C) (L S E N : Subgroup C) (y₀ h : C)
    (hc : c ∈ Subgroup.center C) (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hO : ∀ Q : Subgroup C, Q.Normal → Odd (Nat.card Q) → Q = ⊥)
    (hS : Nat.card S = 2 ^ (Nat.card C).factorization 2) (hSL : S ≤ L)
    (hcE : c ∈ E) (hEL : E ≤ L)
    (hZLE : ∀ z ∈ L, (∀ ℓ ∈ L, ⁅z, ℓ⁆ ∈ E) → z ∈ E)
    (hZN : ∀ y ∈ E, (∀ n ∈ N, ⁅y, n⁆ = 1 ∨ ⁅y, n⁆ = c) →
      y = 1 ∨ y = c ∨ y = y₀ ∨ y = y₀ * c)
    (hh : ⁅y₀, h⁆ ≠ 1 ∧ ⁅y₀, h⁆ ≠ c) :
    ∀ z : C, (∀ y : C, ⁅z, y⁆ = 1 ∨ ⁅z, y⁆ = c) → z = 1 ∨ z = c := by
  intro z hz
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hWn, hWp, hzW⟩ := exists_normal_isPGroup_of_commutators_mem_pair c hc hc2 hc1 hO
  have hWS : W ≤ S := hWp.le_sylow_of_normal (Sylow.ofCard S hS)
  have hzE : z ∈ E := by
    refine hZLE z (hSL (hWS (hzW z hz))) fun ℓ _ => ?_
    rcases hz ℓ with h1 | h1
    · rw [h1]; exact E.one_mem
    · rw [h1]; exact hcE
  have hcc : ∀ g : C, g * c = c * g := Subgroup.mem_center_iff.1 hc
  rcases hZN z hzE (fun n _ => hz n) with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    rw [h1] at hz
    rcases hz h with h2 | h2
    · exact hh.1 h2
    · exact hh.2 h2
  · exfalso
    have h3 : c * h * c⁻¹ = h := by rw [← hcc h, mul_inv_cancel_right]
    have hcomm : ⁅y₀ * c, h⁆ = ⁅y₀, h⁆ :=
      calc ⁅y₀ * c, h⁆ = y₀ * (c * h * c⁻¹) * y₀⁻¹ * h⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = y₀ * h * y₀⁻¹ * h⁻¹ := by rw [h3]
        _ = ⁅y₀, h⁆ := rfl
    have h4 := hz h
    rw [h1, hcomm] at h4
    rcases h4 with h2 | h2
    · exact hh.1 h2
    · exact hh.2 h2

end CFSG.EvenSporadicStandard.M12Std.Yosh

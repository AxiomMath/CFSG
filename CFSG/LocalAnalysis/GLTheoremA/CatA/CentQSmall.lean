module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQLift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieQHolds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

private theorem solvable_of_card_pow_pow {P : Type*} [Group P] [Finite P] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card P = p ^ a * q ^ b) :
    Group.IsSolvable P := by
  haveI : Fintype P := Fintype.ofFinite P
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card, h])

theorem solvable_of_card_dvd_168 {P : Type*} [Group P] [Finite P] (h : Nat.card P ∣ 168)
    (h84 : Nat.card P ≠ 84) (h168 : Nat.card P ≠ 168) : Group.IsSolvable P := by
  have hmem : Nat.card P ∈ Nat.divisors 168 := by simp [h]
  have hdiv : Nat.divisors 168 = {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by
    decide +kernel
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hsq : Squarefree (Nat.card P) → Group.IsSolvable P := fun hs => by
    have : IsZGroup P := IsZGroup.of_squarefree hs
    infer_instance
  rcases hmem with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact hsq (by rw [h1]; decide +kernel)
  · exact hsq (by rw [h1]; decide +kernel)
  · exact hsq (by rw [h1]; decide +kernel)
  · exact solvable_of_card_pow_pow Nat.prime_two Nat.prime_three (by norm_num) (a := 2) (b := 0)
      (by rw [h1]; norm_num)
  · exact hsq (by rw [h1]; decide +kernel)
  · exact hsq (by rw [h1]; decide +kernel)
  · exact solvable_of_card_pow_pow Nat.prime_two Nat.prime_three (by norm_num) (a := 3) (b := 0)
      (by rw [h1]; norm_num)
  · exact solvable_of_card_pow_pow Nat.prime_two Nat.prime_three (by norm_num) (a := 2) (b := 1)
      (by rw [h1]; norm_num)
  · exact hsq (by rw [h1]; decide +kernel)
  · exact hsq (by rw [h1]; decide +kernel)
  · exact solvable_of_card_pow_pow Nat.prime_two Nat.prime_three (by norm_num) (a := 3) (b := 1)
      (by rw [h1]; norm_num)
  · exact solvable_of_card_pow_pow Nat.prime_two Nat.prime_seven (by norm_num) (a := 2) (b := 1)
      (by rw [h1]; norm_num)
  · exact hsq (by rw [h1]; decide +kernel)
  · exact solvable_of_card_pow_pow Nat.prime_two Nat.prime_seven (by norm_num) (a := 3) (b := 1)
      (by rw [h1]; norm_num)
  · exact absurd h1 h84
  · exact absurd h1 h168

theorem centCompQuasi_card168 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (hc : Nat.card S = 168) {x : S} (hx1 : x ≠ 1) (r : ℕ) :
    CentCompQuasi S x r := by
  apply centCompQuasi_of_noPerfect
  intro P hPC hperf
  by_contra hPne
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hperf
  have hCtop : Subgroup.centralizer ({x} : Set S) ≠ ⊤ := by
    intro htop
    apply hx1
    have hz : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Subgroup.centralizer ({x} : Set S) := by rw [htop]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    rw [b3Lie_center_eq_bot hnc, Subgroup.mem_bot] at hz
    exact hz
  have hPtop : P ≠ ⊤ := fun h => hCtop (top_le_iff.1 (h ▸ hPC))
  have hidx : P.index ≠ 1 := fun h => hPtop (Subgroup.index_eq_one.1 h)
  have hmul := Subgroup.card_mul_index P
  rw [hc] at hmul
  have hdvd : Nat.card ↥P ∣ 168 := ⟨P.index, hmul.symm⟩
  have h168 : Nat.card ↥P ≠ 168 := by
    intro h
    rw [h] at hmul
    have : P.index = 1 := by omega
    exact hidx this
  have h84 : Nat.card ↥P ≠ 84 := by
    intro h
    rw [h] at hmul
    have h2 : P.index = 2 := by omega
    haveI : P.Normal := Subgroup.normal_of_index_eq_two h2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
    · exact hPne h
    · exact hPtop h
  exact Group.IsPerfect.not_isSolvable ↥P (solvable_of_card_dvd_168 hdvd h84 h168)

theorem seven_elt_centralizes {S : Type} [Group S] [Finite S] {R : Subgroup S} {a : S}
    (hRcard : Nat.card R ∣ 27) (ha7 : a ^ 7 = 1)
    (hn : ∀ r ∈ R, a * r * a⁻¹ ∈ R ∧ a⁻¹ * r * a ∈ R) :
    ∀ r ∈ R, r * a = a * r := by
  classical
  haveI : Fintype ↥R := Fintype.ofFinite ↥R
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let σ : Equiv.Perm ↥R :=
    { toFun := fun r => ⟨a * r * a⁻¹, (hn r r.2).1⟩
      invFun := fun r => ⟨a⁻¹ * r * a, (hn r r.2).2⟩
      left_inv := fun r => Subtype.ext (by simp [mul_assoc])
      right_inv := fun r => Subtype.ext (by simp [mul_assoc]) }
  have hσapply : ∀ r : ↥R, ((σ r : ↥R) : S) = a * r * a⁻¹ := fun r => rfl
  have hpow : ∀ (n : ℕ) (r : ↥R), (((σ ^ n) r : ↥R) : S) = a ^ n * r * (a ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
      intro r
      rw [pow_succ', Equiv.Perm.mul_apply, hσapply, ih]
      simp [pow_succ', mul_assoc, mul_inv_rev]
  have hσ7 : σ ^ 7 ^ 1 = 1 := by
    ext r
    rw [pow_one, hpow, ha7]
    simp
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 7) (n := 1) hσ7
  set H' : Subgroup ↥R := (Subgroup.centralizer ({a} : Set S)).subgroupOf R with hH'
  have hmH : Nat.card ↥H' = σ.supportᶜ.card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun r => ?_)
    simp only [hH', Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Finset.mem_compl, Equiv.Perm.mem_support, not_not]
    constructor
    · intro h
      exact Subtype.ext (by rw [hσapply, ← h]; simp [mul_assoc])
    · intro h
      have := congrArg Subtype.val h
      rw [hσapply] at this
      calc (r : S) * a = a * r * a⁻¹ * a := by rw [this]
        _ = a * r := by simp
  have hdvd : Nat.card ↥H' ∣ Nat.card ↥R := Subgroup.card_subgroup_dvd_card H'
  rw [← Nat.card_eq_fintype_card] at hmod
  rw [← hmH] at hmod
  have hmem : Nat.card ↥R ∈ Nat.divisors 27 := Nat.mem_divisors.2 ⟨hRcard, by norm_num⟩
  have hdiv27 : Nat.divisors 27 = {1, 3, 9, 27} := by decide +kernel
  rw [hdiv27] at hmem
  have heq : Nat.card ↥H' = Nat.card ↥R := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hle : Nat.card ↥H' ≤ Nat.card ↥R := Nat.le_of_dvd Nat.card_pos hdvd
    unfold Nat.ModEq at hmod
    rcases hmem with h | h | h | h <;> rw [h] at hdvd hmod hle ⊢ <;>
      · have hm27 : Nat.card ↥H' ∣ 27 := hdvd.trans (by norm_num)
        have hmem' : Nat.card ↥H' ∈ Nat.divisors 27 := Nat.mem_divisors.2 ⟨hm27, by norm_num⟩
        rw [hdiv27] at hmem'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
        omega
  have htop : H' = ⊤ := (Subgroup.card_eq_iff_eq_top H').1 heq
  intro r hr
  have : (⟨r, hr⟩ : ↥R) ∈ H' := by rw [htop]; exact Subgroup.mem_top _
  exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 this)

section U33


private theorem cq_lieIndexChar_eq (d : TauCeti.LieTypeIndex) : lieIndexChar d = d.characteristic := by
  cases d <;> simp [lieIndexChar]

private theorem cq_isChevIndexOfChar {d : TauCeti.LieTypeIndex} {q : ℕ} (h : d.characteristic = q) :
    IsChevIndexOfChar q d := by
  unfold IsChevIndexOfChar
  split
  · left
    simpa using h
  · left
    simpa using h
  · rw [cq_lieIndexChar_eq]
    exact h

private theorem not_dvd_6048 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hr7 : r ≠ 7) :
    ¬ r ∣ 6048 := by
  intro h
  have h' : r ∣ 2 ^ 5 * 3 ^ 3 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hr).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h2))
  · exact hr7 ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1)

theorem not_seven_dvd_card_cent_u33 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 3)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (hc : Nat.card S = 6048) {x : S}
    (hx : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ¬ 7 ∣ Nat.card (Subgroup.centralizer ({x} : Set S)) := by
  intro h7
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a', ha'⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer ({x} : Set S))) 7 h7
  set a : S := (a' : S) with ha_def
  have ha7 : a ^ 7 = 1 := by
    have := pow_orderOf_eq_one a'
    rw [ha'] at this
    simpa using congrArg Subtype.val this
  have haord : orderOf a = 7 := (Subgroup.orderOf_coe a').trans ha'
  have hax : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.1 a'.2
  have hxord : orderOf x = 3 := orderOf_eq_prime hx hx1
  set Q : Subgroup S := Subgroup.zpowers x with hQ
  have hQne : Q ≠ ⊥ := fun h => hx1 (Subgroup.zpowers_eq_bot.1 h)
  have hQp : IsPGroup 3 ↥Q := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord]; norm_num)
  have hLQ := CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrainedInner_odd
    (q := 3) Nat.prime_three (by norm_num) S hS hnc ⟨d, cq_isChevIndexOfChar hd, ⟨e⟩⟩ Q hQne hQp
  have hcommQ : ∀ h ∈ Q, a * h * a⁻¹ = h := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_right (show Commute a x from hax) k).mul_inv_cancel
  have hcommQ' : ∀ h ∈ Q, a⁻¹ * h * a = h := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have := (Commute.zpow_right (show Commute a⁻¹ x from (show Commute a x from hax).inv_left) k)
    simpa using this.mul_inv_cancel
  set N : Subgroup S := Subgroup.normalizer (Q : Set S) with hN
  have haN : a ∈ N := by
    rw [hN, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hcommQ h hh]
      exact hh
    · intro hh
      have h1 := hcommQ' _ hh
      have e : a⁻¹ * (a * h * a⁻¹) * a = h := by group
      rw [e] at h1
      rw [h1]
      exact hh
  set R : Subgroup S := pCoreOf 3 N with hR
  have hR3 : IsPGroup 3 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 3) N
  have hRcard : Nat.card ↥R ∣ 27 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR3
    have h1 : Nat.card ↥R ∣ 6048 := hc ▸ Subgroup.card_subgroup_dvd_card R
    rw [hk] at h1 ⊢
    have hcop : Nat.Coprime (3 ^ k) 224 := Nat.Coprime.pow_left k (by norm_num)
    exact hcop.dvd_of_dvd_mul_right (by simpa using h1)
  have hnorm : ∀ r ∈ R, a * r * a⁻¹ ∈ R ∧ a⁻¹ * r * a ∈ R := fun r hr =>
    ⟨(Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 3 N haN) r).1 hr,
      by simpa using (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 3 N (inv_mem haN)) r).1 hr⟩
  have hcent := seven_elt_centralizes hRcard ha7 hnorm
  have haR : a ∈ R := hLQ a haN (fun r hr => (hcent r hr).symm)
  obtain ⟨k, hk⟩ := hR3 ⟨a, haR⟩
  have hak : a ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h7' : 7 ∣ 3 ^ k := haord ▸ orderOf_dvd_of_pow_eq_one hak
  exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h7') (by norm_num)

theorem centCompQuasi_u33 {S : Type} [Group S] [Finite S] [hS : IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 3)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (hc : Nat.card S = 6048) {x : S}
    (hx : x ^ 3 = 1) (hx1 : x ≠ 1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CentCompQuasi S x r := by
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv S e.toEquiv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x = 3 := orderOf_eq_prime hx hx1
  by_cases hr3 : r = 3
  · subst hr3
    refine centCompQuasi_of_mulEquiv e hr ?_
    intro J hJ
    exfalso
    have hle : J ≤ GLAPLayer 3 (Subgroup.centralizer ({e x} : Set (TauCeti.CFSGIndex.lie d).Group)) :=
      le_sSup hJ
    have hord' : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hord
    rw [CFSG.LocalAnalysis.GLTheoremA.kdCharP_holds Nat.prime_three (by norm_num) d hd (e x) hord',
      le_bot_iff] at hle
    exact cq_glaPComponent_ne_bot hJ hle
  · intro J hJ
    exfalso
    apply CFSG.LocalAnalysis.GLTheoremA.AltDown.not_coprime_card_of_glaPComponent hr hJ
    have hJC : J ≤ Subgroup.centralizer ({x} : Set S) := hJ.1
    refine (Nat.Prime.coprime_iff_not_dvd hr).2 fun hdvd => ?_
    by_cases hr7 : r = 7
    · subst hr7
      exact not_seven_dvd_card_cent_u33 hS hnc d hd e hc hx hx1
        (hdvd.trans (Subgroup.card_dvd_of_le hJC))
    · exact not_dvd_6048 hr hr2 hr3 hr7
        (hdvd.trans ((Subgroup.card_subgroup_dvd_card J).trans (by rw [hc])))

end U33

end CFSG.LocalAnalysis.GLTheoremA

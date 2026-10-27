module

public import CFSG.ClassicalInvolution.Q3.Q3MApp
public import CFSG.ClassicalInvolution.Q3.Q3MOdd

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

theorem mem_of_odd_orderOf {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hH : ∀ g : G, ∀ p k : ℕ, p.Prime → p ≠ 2 → g ^ p ^ k = 1 → g ∈ H) :
    ∀ g : G, Odd (orderOf g) → g ∈ H := by
  suffices key : ∀ n : ℕ, ∀ g : G, orderOf g = n → Odd n → g ∈ H from
    fun g hg => key _ g rfl hg
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hn hodd
    have hn0 : n ≠ 0 := hn ▸ (orderOf_pos g).ne'
    by_cases hn1 : n = 1
    · rw [hn1, orderOf_eq_one_iff] at hn
      rw [hn]
      exact H.one_mem
    have hpp : n.minFac.Prime := Nat.minFac_prime hn1
    have hpn : n.minFac ∣ n := Nat.minFac_dvd n
    set p := n.minFac with hpdef
    have hp2 : p ≠ 2 := by
      intro h2
      have h2n : 2 ∣ n := h2 ▸ hpn
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2n)
    obtain ⟨a, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hpp.ne_one
    have hcop : Nat.Coprime (p ^ a) m :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpm)
    have hbez := Nat.gcd_eq_gcd_ab (p ^ a) m
    rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
    have hgn : g ^ n = 1 := hn ▸ pow_orderOf_eq_one g
    have hcast : ((p ^ a : ℕ) : ℤ) * (m : ℤ) = (n : ℤ) := by
      rw [hnm]; push_cast; ring
    have hsplit : g = g ^ (((p ^ a : ℕ) : ℤ) * (p ^ a).gcdA m) *
        g ^ ((m : ℤ) * (p ^ a).gcdB m) := by
      rw [← zpow_add, ← hbez, zpow_one]
    rw [hsplit]
    refine H.mul_mem ?_ ?_
    · have hpow : (g ^ (((p ^ a : ℕ) : ℤ) * (p ^ a).gcdA m)) ^ m = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_right_comm, hcast, zpow_mul, zpow_natCast, hgn,
          one_zpow]
      have hdvd := orderOf_dvd_of_pow_eq_one hpow
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hnm
        exact hn0 hnm
      have ha : a ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hnm
        exact hpm (hnm ▸ hpn)
      have hmn : m < n := by
        rw [hnm]
        have h1 : 1 < p ^ a := Nat.one_lt_pow ha hpp.one_lt
        calc m = 1 * m := (one_mul m).symm
          _ < p ^ a * m := Nat.mul_lt_mul_of_pos_right h1 (Nat.pos_of_ne_zero hm0)
      have hmodd : Odd m := hodd.of_dvd_nat (Dvd.intro_left _ hnm.symm)
      exact ih _ (lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd) hmn) _ rfl
        (hmodd.of_dvd_nat hdvd)
    · refine hH _ p a hpp hp2 ?_
      rw [← zpow_natCast, ← zpow_mul, mul_assoc, mul_comm _ ((p ^ a : ℕ) : ℤ),
        ← mul_assoc, mul_comm (m : ℤ), hcast, zpow_mul, zpow_natCast, hgn, one_zpow]

theorem sl2_closure_three_eq_top :
    Subgroup.closure {y : SL(2, ZMod 3) | y ^ 3 = 1} = ⊤ := by
  set s : Set SL(2, ZMod 3) := {y | y ^ 3 = 1} with hs
  have hconj : Group.conjugatesOfSet s ⊆ s := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hax
    show (c * a * c⁻¹) ^ 3 = 1
    rw [conj_pow, show a ^ 3 = 1 from ha, mul_one, mul_inv_cancel]
  have hle : Subgroup.normalClosure s ≤ Subgroup.closure s :=
    Subgroup.closure_mono hconj
  obtain ⟨g₀, hg₀3, hg₀1⟩ := M.sl2_exists_three
  have hg₀s : g₀ ∈ Subgroup.normalClosure s := Subgroup.subset_normalClosure hg₀3
  have hg₀2 : g₀ ^ 2 ≠ 1 := by
    intro h
    apply hg₀1
    calc g₀ = g₀ ^ 3 * (g₀ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hg₀3, h, inv_one, mul_one]
  have hQ : sl2ThreeQ ≤ Subgroup.normalClosure s := M.sl2_normal_Q _ hg₀s hg₀2
  have hg₀Q : g₀ ∉ sl2ThreeQ := by
    intro h
    have h4 : g₀ ^ 4 = 1 := mem_sl2ThreeQ_iff.mp h
    apply hg₀1
    calc g₀ = g₀ ^ 4 * (g₀ ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, hg₀3, inv_one, mul_one]
  have hcard : Nat.card (Subgroup.normalClosure s) = 24 := by
    have h8 : 8 ∣ Nat.card (Subgroup.normalClosure s) := natCard_sl2ThreeQ ▸
      Subgroup.card_dvd_of_le hQ
    have h24 : Nat.card (Subgroup.normalClosure s) ∣ 24 :=
      natCard_sl2Three ▸ Subgroup.card_subgroup_dvd_card _
    have hne : Nat.card (Subgroup.normalClosure s) ≠ 8 := by
      intro h
      have heq : sl2ThreeQ = Subgroup.normalClosure s :=
        Subgroup.eq_of_le_of_card_ge hQ (by rw [h, natCard_sl2ThreeQ])
      exact hg₀Q (heq ▸ hg₀s)
    obtain ⟨k, hk⟩ := h8
    have hk3 : k ∣ 3 := by
      rw [hk] at h24
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 8)
        (show 8 * k ∣ 8 * 3 by simpa using h24)
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with h | h
    · exact absurd (by rw [hk, h]) hne
    · rw [hk, h]
  have htop : Subgroup.normalClosure s = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hcard, natCard_sl2Three])
  exact top_le_iff.mp (htop ▸ hle)

theorem sl2_involution_unique : ∀ a b : SL(2, ZMod 3), a ^ 2 = 1 → a ≠ 1 → b ^ 2 = 1 → b ≠ 1 →
    a = b := by
  decide +kernel

theorem oddCore_eq_bot_of_mulEquiv_sl2 {H : Type*} [Group H] [Finite H]
    (e : H ≃* SL(2, ZMod 3)) : classicalInvolutionOddCore H = ⊥ := by
  set N := classicalInvolutionOddCore H with hNdef
  have hodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card H
  set N' : Subgroup SL(2, ZMod 3) := N.map e.toMonoidHom with hN'def
  have hN'n : N'.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have hcard : Nat.card N' = Nat.card N := Subgroup.card_map_of_injective e.injective
  refine (Subgroup.map_eq_bot_iff_of_injective N (f := e.toMonoidHom) e.injective).mp ?_
  by_contra hne
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hy1' : (y : SL(2, ZMod 3)) ≠ 1 := fun h => hy1 (Subtype.ext h)
  by_cases hy2 : (y : SL(2, ZMod 3)) ^ 2 = 1
  · have hord : orderOf y = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime hy2 hy1'
    have h2 := orderOf_dvd_natCard y
    rw [hord, hcard] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · have hQ := M.sl2_normal_Q N' y.2 hy2
    have h8 : 8 ∣ Nat.card N' := natCard_sl2ThreeQ ▸ Subgroup.card_dvd_of_le hQ
    rw [hcard] at h8
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_trans (by norm_num) h8))

theorem mem_of_isSubnormal_of_mulEquiv_sl2 {H : Type*} [Group H] [Finite H]
    (e : H ≃* SL(2, ZMod 3)) {K : Subgroup H} (hK : IsSubnormal K ⊤) (hne : K ≠ ⊥) {w : H}
    (hw : orderOf w = 2) : w ∈ K := by
  by_cases hodd : Odd (Nat.card K)
  · exact absurd (M.eq_bot_of_isSubnormal_odd (oddCore_eq_bot_of_mulEquiv_sl2 e) hK hodd) hne
  · have h2 : 2 ∣ Nat.card K := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hk' : orderOf (e k) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hk]
    have hw' : orderOf (e w) = 2 := by rw [MulEquiv.orderOf_eq, hw]
    have hsq : ∀ a : SL(2, ZMod 3), orderOf a = 2 → a ^ 2 = 1 ∧ a ≠ 1 := fun a ha =>
      ⟨by have h1 := pow_orderOf_eq_one a; rwa [ha] at h1,
        fun h => by rw [h, orderOf_one] at ha; omega⟩
    have heq : e k = e w :=
      sl2_involution_unique _ _ (hsq _ hk').1 (hsq _ hk').2 (hsq _ hw').1 (hsq _ hw').2
    rw [← e.injective heq]
    exact k.2

theorem pow_four_pow_of_pow_three {G : Type*} [Group G] {y : G} (hy : y ^ 3 = 1) :
    ∀ e : ℕ, y ^ 4 ^ e = y
  | 0 => by rw [pow_zero, pow_one]
  | e + 1 => by
    rw [pow_succ, pow_mul, pow_four_pow_of_pow_three hy e,
      show y ^ 4 = y ^ 3 * y by group, hy, one_mul]

theorem le_of_forall_oddPrimePow_mem {X : Type} [Group X] [Finite X] {L : Subgroup X} {z : X}
    (hz : IsClassicalMember3 L z) {H : Subgroup X}
    (hH : ∀ g ∈ L, ∀ p k : ℕ, p.Prime → p ≠ 2 → g ^ p ^ k = 1 → g ∈ H) : L ≤ H := by
  obtain ⟨φ, hφs, hφodd⟩ := M.exists_hom_of_member hz
  set H' : Subgroup L := H.subgroupOf L with hH'def
  have hodd' : ∀ g : L, Odd (orderOf g) → g ∈ H' := by
    refine mem_of_odd_orderOf H' fun g p k hp hp2 hg => ?_
    refine Subgroup.mem_subgroupOf.mpr (hH g g.2 p k hp hp2 ?_)
    have := congrArg (fun x : L => (x : X)) hg
    simpa using this
  have hker : φ.ker ≤ H' := by
    intro g hg
    refine hodd' g (hφodd.of_dvd_nat ?_)
    have := orderOf_dvd_natCard (⟨g, hg⟩ : φ.ker)
    rwa [Subgroup.orderOf_mk] at this
  have hthree : ∀ y : SL(2, ZMod 3), y ^ 3 = 1 → y ∈ H'.map φ := by
    intro y hy
    obtain ⟨g₀, rfl⟩ := hφs y
    obtain ⟨e, u, hu, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g₀).ne'
    refine ⟨g₀ ^ 4 ^ e, hodd' _ ?_, ?_⟩
    · have h4 : (4 : ℕ) ^ e = 2 ^ e * 2 ^ e := by rw [← mul_pow]; norm_num
      have hpow : (g₀ ^ 4 ^ e) ^ u = 1 := by
        rw [← pow_mul, h4, show 2 ^ e * 2 ^ e * u = 2 ^ e * u * 2 ^ e by ring, ← hn, pow_mul,
          pow_orderOf_eq_one, one_pow]
      exact hu.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
    · rw [map_pow]
      exact pow_four_pow_of_pow_three hy e
  have htop : H'.map φ = ⊤ := by
    rw [eq_top_iff, ← sl2_closure_three_eq_top, Subgroup.closure_le]
    exact fun y hy => hthree y hy
  intro g hg
  have hgφ : φ ⟨g, hg⟩ ∈ H'.map φ := htop ▸ Subgroup.mem_top _
  obtain ⟨h, hh, hhg⟩ := hgφ
  have hk : h⁻¹ * ⟨g, hg⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hhg, inv_mul_cancel]
  have hmem : (⟨g, hg⟩ : L) ∈ H' := by
    have := H'.mul_mem hh (hker hk)
    simpa using this
  exact Subgroup.mem_subgroupOf.mp hmem

end CFSG.ClassicalInvolution.Q3.Q3T

module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10AltFive
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10AltThreeLow
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10AltThreeConstr
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10AltThreeBound
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10AltThreeSix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.Balance.Alt

set_option linter.unusedSectionVars false

theorem i1910a3_arith_contra {n r β q a : ℕ} (hr : r = 2 ∨ r = 4) (hrn : 3 ^ 2 + r ≤ n)
    (hβ : 3 ^ 2 * β + 2 * r ≤ 2 * n + 3 ^ 2 * (r / 3)) (hq : q = (n - 4) / 3)
    (h : (q + 1) * 3 ^ a ≤ a + β) : False := by
  have hpa := i1910_two_mul_add_one_le_pow (by norm_num : 3 ≤ 3) a
  have hqb : q + 1 ≤ β := by
    by_contra hcon
    push Not at hcon
    have h6 : (q + 1) * (2 * a + 1) ≤ (q + 1) * 3 ^ a := Nat.mul_le_mul_left _ hpa
    nlinarith
  have hq1 : 3 * q ≤ n - 4 := by rw [hq]; exact Nat.mul_div_le _ _
  have hq2 : n - 4 < 3 * (q + 1) := by
    rw [hq]
    exact Nat.lt_mul_div_succ (n - 4) (by norm_num)
  rcases hr with rfl | rfl <;> norm_num at hβ hrn <;> omega

theorem localTwoBalanceAltThree_proved : LocalTwoBalanceAltThree := by
  intro G _ _ _ X _ B hBX hB hrank _ L hL n hn
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨e⟩ := hn
  have hperf : Group.IsPerfect (barOf 3 L) := isPerfect_barOf hL
  have hAe := isElemAbelian_autBar hB L
  by_cases hn6 : n = 6
  · subst hn6
    exact (IsLocallyBalancedAbs.of_quotient_center (isQuasisimple_barOf hp hL).1
      (IsLocallyBalancedAbs.of_mulEquiv e i1910a3_altSix)).isLocallyBalanced _
  intro D hD H hH _
  by_contra hΔ
  obtain ⟨hDA, hDe, hD2⟩ := hD
  by_cases hn4 : n ≤ 4
  · have h1 : Group.IsSolvable (alternatingGroup (Fin n)) :=
      alternatingGroup.isSolvable (by simpa using hn4)
    have h2 : Group.IsSolvable (barOf 3 L ⧸ Subgroup.center (barOf 3 L)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have h3 : Group.IsSolvable (barOf 3 L) :=
      Group.isSolvable_of_subgroup_quotient (Subgroup.center _)
    have h4 : Subsingleton (barOf 3 L) := by
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact Group.IsPerfect.not_isSolvable (barOf 3 L) h3
    have h5 : Subsingleton (MulAut (barOf 3 L)) :=
      ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    have h6 : Subsingleton D := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    have := Finite.card_le_one_iff_subsingleton.2 h6
    have : 1 < 3 ^ 2 := by norm_num
    omega
  have hn5 : 5 ≤ n := by omega
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  obtain ⟨ι, hιinj, hιinner⟩ := exists_embedding_perm e hbij
  obtain ⟨r, β, hr, hrn, hβ, hβn⟩ := i1910a3_upper_bound_three ι hιinj (innerAut (barOf 3 L))
    hιinner (autBar 3 B L) D H hDA hAe hDe hD2 hH hΔ
  have hn8 : 8 ≤ n := by norm_num at hrn; omega
  have hZ0 : Subgroup.center (barOf 3 L) = ⊥ :=
    center_eq_bot_of_odd hn8 e (odd_card_center_barOf hp hp2 L)
  have hZ : ∀ x : barOf 3 L, (∀ y, x * y = y * x) → x = 1 := by
    intro x hx
    have : x ∈ Subgroup.center (barOf 3 L) := Subgroup.mem_center_iff.2 fun g => (hx g).symm
    rw [hZ0] at this
    exact this
  let η : barOf 3 L →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (barOf 3 L)))
  have hηinj : Function.Injective η := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center (barOf 3 L)) x = 1 := by
      apply e.injective
      rw [map_one]; exact hx
    have h2 : x ∈ Subgroup.center (barOf 3 L) := (QuotientGroup.eq_one_iff x).1 h1
    rw [hZ0] at h2
    exact h2
  have hηsurj : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ψ : barOf 3 L ≃* alternatingGroup (Fin n) := MulEquiv.ofBijective η ⟨hηinj, hηsurj⟩
  obtain ⟨E, T, hEc, hEe, hEcard, hT1, hT2, hET⟩ :=
    i1910a3_exists_elemAbelian_normalizing_two (show 4 ≤ n by omega)
  set q := (n - 4) / 3 with hq
  have hψinj := ψ.symm.injective
  obtain ⟨P, S, hPc, hPe, hPcard, hS, hS2, hPS⟩ := i1910a3_exists_twoLocal_lower hp hp2 hBX hB hL hZ
    (E.map ψ.symm.toMonoidHom) (T.map ψ.symm.toMonoidHom) (q + 1)
    ⟨isMulCommutative_map _ E hEc, by rintro _ ⟨x, hx, rfl⟩; rw [← map_pow, hEe x hx, map_one],
      by rw [Subgroup.card_map_of_injective hψinj]; exact hEcard⟩
    ⟨fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective T hψinj).1 h), hT2.map _⟩
    ((Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map _))
  have hpgB : IsPGroup 3 B := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hB.2 _ g.2)⟩
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.card B = 3 ^ m := IsPGroup.iff_card.1 hpgB
  have hCle : ∀ x, x ∈ centB 3 B L → x ∈ B := fun x hx => centB_le 3 B L hx
  have hpgC : IsPGroup 3 (centB 3 B L) := hpgB.to_le (centB_le 3 B L)
  obtain ⟨γ, hγ⟩ : ∃ γ, Nat.card (centB 3 B L) = 3 ^ γ := IsPGroup.iff_card.1 hpgC
  have hcardB := card_B_eq 3 B L
  rw [hm, hβ, hγ] at hcardB
  have hdvd : (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B ∣ 3 ^ m :=
    ⟨3 ^ β * 3 ^ γ, hcardB.trans rfl⟩
  obtain ⟨a, ha⟩ := (Nat.dvd_prime_pow hp).1 hdvd |>.imp fun a h => h.2
  have hmaβγ : m = a + (β + γ) := by
    rw [ha, ← pow_add, ← pow_add] at hcardB
    exact Nat.pow_right_injective hp.two_le hcardB
  have hPcard' : Nat.card P = 3 ^ (γ + (q + 1) * 3 ^ a) := by
    rw [hPcard, hγ, ha, ← pow_add]
  have hrkP : CFSG.Open.pRank 3 P = γ + (q + 1) * 3 ^ a :=
    pRank_eq_of_card hp ⟨hPc, hPe⟩ hPcard'
  have hrkB : CFSG.Open.pRank 3 B = m := pRank_eq_of_card hp hB hm
  have h1 : CFSG.Open.pRank 3 P ≤ GLATwoLocalRank 3 ↥X :=
    pRank_le_glaTwoLocalRank_of_normalizes hp hS hS2 hPS
  have h2 : γ + (q + 1) * 3 ^ a ≤ a + (β + γ) := by
    rw [← hrkP, ← hmaβγ, ← hrkB]
    exact h1.trans hrank
  exact i1910a3_arith_contra (a := a) hr hrn hβn hq (by omega)


end CFSG.HardMathSupport.Solomon.Coordinator

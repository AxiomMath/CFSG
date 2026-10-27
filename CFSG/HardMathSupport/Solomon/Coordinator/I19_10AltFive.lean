module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutSix
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutTransfer
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Construct
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Lower
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.AltUpper
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.Balance.Alt

set_option linter.unusedSectionVars false

@[expose] def LocalTwoBalanceAltThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G →
    ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X → IsElemAbelian 3 B →
      GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B → 2 ≤ CFSG.Open.pRank 3 B →
      ∀ L : Subgroup G, GLAPComponent 3 X L → ∀ n : ℕ,
        Nonempty ((barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ≃* ↥(alternatingGroup (Fin n))) →
          IsCompLocallyBalanced 3 2 B L

@[expose] def LocalTwoBalanceAltFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G →
    ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X → IsElemAbelian 5 B →
      GLATwoLocalRank 5 ↥X ≤ CFSG.Open.pRank 5 B → 2 ≤ CFSG.Open.pRank 5 B →
      ∀ L : Subgroup G, GLAPComponent 5 X L → ∀ n : ℕ,
        Nonempty ((barOf 5 L ⧸ Subgroup.center (barOf 5 L)) ≃* ↥(alternatingGroup (Fin n))) →
          IsCompLocallyBalanced 5 2 B L

theorem localTwoBalanceAltLow_of_three_five (h3 : LocalTwoBalanceAltThree)
    (h5 : LocalTwoBalanceAltFive) : LocalTwoBalanceAltLow := by
  intro G _ _ hG p hp hp35 X hX B hBX hB hrank h2 L hL n hn
  rcases hp35 with rfl | rfl
  · exact h3 G hG X hX B hBX hB hrank h2 L hL n hn
  · exact h5 G hG X hX B hBX hB hrank h2 L hL n hn

theorem i1910_two_mul_add_one_le_pow {p : ℕ} (hp : 3 ≤ p) (a : ℕ) : 2 * a + 1 ≤ p ^ a := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith

theorem i1910_arith_contra_five {p n β q a : ℕ} (hp : p = 5) (h1 : p ^ 2 ≤ n)
    (h2 : p ^ 2 * β ≤ 2 * n + p ^ 2) (hq : q = (n - 4) / p) (h4 : q * p ^ a ≤ a + β) :
    False := by
  subst hp
  have hpa := i1910_two_mul_add_one_le_pow (by norm_num : 3 ≤ 5) a
  have hq1 : 5 * q ≤ n - 4 := by rw [hq]; exact Nat.mul_div_le _ _
  have hq2 : n - 4 < 5 * (q + 1) := by
    rw [hq]
    exact Nat.lt_mul_div_succ (n - 4) (by norm_num)
  have hqβ : β + 1 ≤ q := by
    by_contra h
    have : q ≤ β := by omega
    omega
  have h6 : q * (2 * a + 1) ≤ q * 5 ^ a := Nat.mul_le_mul_left q hpa
  nlinarith

theorem i1910_conj_injective_alternatingGroup_six :
    Function.Injective
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun e : MulAut (alternatingGroup (Fin 6)) => e h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc h * g = g * h * g⁻¹ * g := by rw [this]
      _ = g * h := by group
  rw [alternatingGroup.center_eq_bot (by simp)] at hc
  exact hc

theorem i1910_card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem i1910_dvd_card_mulAut_alternatingGroup_six :
    360 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
  obtain ⟨hfin, -⟩ := finite_and_card_mulAut_alternatingGroup_six_le
  have h := Subgroup.card_subgroup_dvd_card
    (MonoidHom.range (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))))
  rwa [← Nat.card_congr
      (MonoidHom.ofInjective i1910_conj_injective_alternatingGroup_six).toEquiv,
    i1910_card_alternatingGroup_six] at h

theorem i1910_no_elemAbelian_square_alt_six_five {p : ℕ} (hp : p.Prime) (hp5 : p = 5)
    (D : Subgroup (MulAut (alternatingGroup (Fin 6)))) :
    ¬ (IsMulCommutative D ∧ (∀ x ∈ D, x ^ p = 1) ∧ Nat.card D = p ^ 2) := by
  rintro ⟨-, -, hD⟩
  obtain ⟨hfin, hle⟩ := finite_and_card_mulAut_alternatingGroup_six_le
  have h1 : p ^ 2 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
    rw [← hD]
    exact Subgroup.card_subgroup_dvd_card D
  obtain ⟨j, hj⟩ := i1910_dvd_card_mulAut_alternatingGroup_six
  rw [hj] at h1 hle
  subst hp5
  have hj4 : j ≤ 4 := by omega
  have h1' : 25 ∣ 360 * j := by simpa using h1
  have hpos := Nat.card_pos (α := MulAut (alternatingGroup (Fin 6)))
  omega

theorem i1910_altFive_core {p : ℕ} (hp : p.Prime) (hp5 : p = 5) :
    ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G →
      ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X → IsElemAbelian p B →
        GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → 2 ≤ CFSG.Open.pRank p B →
        ∀ L : Subgroup G, GLAPComponent p X L → ∀ n : ℕ,
          Nonempty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃* ↥(alternatingGroup (Fin n))) →
            IsCompLocallyBalanced p 2 B L := by
  intro G _ _ _ X _ B hBX hB hrank _ L hL n hn
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e⟩ := hn
  intro D hD H hH _
  by_contra hΔ
  obtain ⟨hDA, hDe, hD2⟩ := hD
  have hp3 : 3 ≤ p := by omega
  have hperf : Group.IsPerfect (barOf p L) := isPerfect_barOf hL
  have hAe := isElemAbelian_autBar hB L
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD2
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  by_cases hn4 : n ≤ 4
  · have h1 : Group.IsSolvable (alternatingGroup (Fin n)) :=
      alternatingGroup.isSolvable (by simpa using hn4)
    have h2 : Group.IsSolvable (barOf p L ⧸ Subgroup.center (barOf p L)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have h3 : Group.IsSolvable (barOf p L) :=
      Group.isSolvable_of_subgroup_quotient (Subgroup.center _)
    have h4 : Subsingleton (barOf p L) := by
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact Group.IsPerfect.not_isSolvable (barOf p L) h3
    have h5 : Subsingleton (MulAut (barOf p L)) :=
      ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    have h6 : Subsingleton D := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    have := Finite.card_le_one_iff_subsingleton.2 h6
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  by_cases hn6 : n = 6
  · subst hn6
    let φ : MulAut (barOf p L) →* MulAut (alternatingGroup (Fin 6)) :=
      (MulAut.congr e).toMonoidHom.comp (CFSG.HardMathSupport.Timmesfeld.Balance.Alt.autCenterQuot (barOf p L))
    have hφ : Function.Injective φ :=
      (MulAut.congr e).injective.comp (CFSG.HardMathSupport.Timmesfeld.Balance.Alt.autCenterQuot_injective _)
    refine i1910_no_elemAbelian_square_alt_six_five hp hp5 (D.map φ) ⟨?_, ?_, ?_⟩
    · exact isMulCommutative_map φ D hDe.1
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hDe.2 x hx, map_one]
    · rw [Subgroup.card_map_of_injective hφ]; exact hD2
  have hn5 : 5 ≤ n := by omega
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  obtain ⟨ι, hιinj, hιinner⟩ := exists_embedding_perm e hbij
  obtain ⟨hpn, β, hβ, hβn⟩ := upper_bound_of_delta_two hp hp2 ι hιinj (innerAut (barOf p L))
    hιinner (autBar p B L) D H hDA hAe hDe hD2 hH hΔ
  have hp27 : 25 ≤ p ^ 2 := by rw [hp5]; norm_num
  have hn8 : 8 ≤ n := by omega
  have hZ0 : Subgroup.center (barOf p L) = ⊥ :=
    center_eq_bot_of_odd hn8 e (odd_card_center_barOf hp hp2 L)
  have hZ : ∀ x : barOf p L, (∀ y, x * y = y * x) → x = 1 := by
    intro x hx
    have : x ∈ Subgroup.center (barOf p L) := Subgroup.mem_center_iff.2 fun g => (hx g).symm
    rw [hZ0] at this
    exact this
  let η : barOf p L →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (barOf p L)))
  have hηinj : Function.Injective η := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center (barOf p L)) x = 1 := by
      apply e.injective
      rw [map_one]; exact hx
    have h2 : x ∈ Subgroup.center (barOf p L) := (QuotientGroup.eq_one_iff x).1 h1
    rw [hZ0] at h2
    exact h2
  have hηsurj : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ψ : barOf p L ≃* alternatingGroup (Fin n) := MulEquiv.ofBijective η ⟨hηinj, hηsurj⟩
  obtain ⟨E, T, hEc, hEe, hEcard, hT1, hT2, hET⟩ :=
    exists_elemAbelian_centralizing_two hp hp2 (show 4 ≤ n by omega)
  set q := (n - 4) / p with hq
  have hψinj := ψ.symm.injective
  obtain ⟨P, S, hPc, hPe, hPcard, hS, hS2, hPS⟩ := exists_twoLocal_lower hp hp2 hBX hB hL hZ
    (E.map ψ.symm.toMonoidHom) (T.map ψ.symm.toMonoidHom) q
    ⟨isMulCommutative_map _ E hEc, by rintro _ ⟨x, hx, rfl⟩; rw [← map_pow, hEe x hx, map_one],
      by rw [Subgroup.card_map_of_injective hψinj]; exact hEcard⟩
    ⟨fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective T hψinj).1 h), hT2.map _⟩
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 (hET hx) t ht
      rw [← map_mul, ← map_mul, this])
  have hpgB : IsPGroup p B := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hB.2 _ g.2)⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.card B = p ^ m := IsPGroup.iff_card.1 hpgB
  have hCle : ∀ x, x ∈ centB p B L → x ∈ B := fun x hx => centB_le p B L hx
  have hpgC : IsPGroup p (centB p B L) := hpgB.to_le (centB_le p B L)
  obtain ⟨γ, hγ⟩ : ∃ γ, Nat.card (centB p B L) = p ^ γ := IsPGroup.iff_card.1 hpgC
  have hcardB := card_B_eq p B L
  rw [hm, hβ, hγ] at hcardB
  have hdvd : (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B ∣ p ^ m :=
    ⟨p ^ β * p ^ γ, hcardB.trans rfl⟩
  obtain ⟨a, ha⟩ := (Nat.dvd_prime_pow hp).1 hdvd |>.imp fun a h => h.2
  have hmaβγ : m = a + (β + γ) := by
    rw [ha, ← pow_add, ← pow_add] at hcardB
    exact Nat.pow_right_injective hp.two_le hcardB
  have hPcard' : Nat.card P = p ^ (γ + q * p ^ a) := by
    rw [hPcard, hγ, ha, ← pow_add]
  have hrkP : CFSG.Open.pRank p P = γ + q * p ^ a :=
    pRank_eq_of_card hp ⟨hPc, hPe⟩ hPcard'
  have hrkB : CFSG.Open.pRank p B = m := pRank_eq_of_card hp hB hm
  have h1 : CFSG.Open.pRank p P ≤ GLATwoLocalRank p ↥X :=
    pRank_le_glaTwoLocalRank_of_normalizes hp hS hS2 hPS
  have h2 : γ + q * p ^ a ≤ a + (β + γ) := by
    rw [← hrkP, ← hmaβγ, ← hrkB]
    exact h1.trans hrank
  exact i1910_arith_contra_five (a := a) hp5 hpn hβn hq (by omega)

theorem localTwoBalanceAltFive_proved : LocalTwoBalanceAltFive :=
  i1910_altFive_core Nat.prime_five rfl

end CFSG.HardMathSupport.Solomon.Coordinator

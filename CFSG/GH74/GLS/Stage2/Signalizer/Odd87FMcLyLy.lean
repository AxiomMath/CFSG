module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87QuotFaith
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint
open scoped commutatorElement

theorem noQuotCfg_Ly
    {Y : Type} [Group Y] [Finite Y]
    (hY : NativeSporadic.IsSporadic Y .Ly) {p : ℕ} {α : MulAut Y} {Xh : Subgroup Y}
    (h : QuotCfg p α Xh) : False := by
  classical
  obtain ⟨e⟩ := hY
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card Y = 51765179004000000 := by
    rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.Ly.card_Ly
  have hinner : ∀ φ : MulAut NativeSporadic.Ly, ∃ g : NativeSporadic.Ly, φ = MulAut.conj g := fun φ => by
    obtain ⟨g, hg⟩ := (Subgroup.eq_top_iff' _).mp
      CFSG.ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput φ
    exact ⟨g, hg.symm⟩
  obtain ⟨t, hαt⟩ := exists_conj_of_equiv e hinner α
  obtain ⟨hto, ht2, hfix, htα⟩ := h.of_inner hαt
  have hcent : ∀ u : Y, orderOf u = 2 → CFSG.IsQuasisimple ↥(centralizer ({u} : Set Y)) ∧
      Nat.card ↥(Subgroup.center ↥(centralizer ({u} : Set Y))) = 2 ∧
      Nat.card ↥(centralizer ({u} : Set Y)) = 39916800 := by
    intro u hu
    obtain ⟨hq, hZ, ⟨E⟩⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ u hu
    refine ⟨hq, hZ, ?_⟩
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(centralizer ({u} : Set Y)))
    have hA : Nat.card ↥(alternatingGroup (Fin 11)) = 19958400 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      norm_num [Nat.factorial]
    rw [hZ, Nat.card_congr E.toEquiv, hA] at h1
    rw [h1]
  obtain ⟨hquasi, hZc, hCcard⟩ := hcent t hto
  have htC : t ∈ centralizer ({t} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hEα : ∀ y ∈ centralizer ({t} : Set Y), α y = y := fun y hy => (hfix y).2 hy
  have hpdvd : p ∣ 51765179004000000 := hcard ▸ h.dvd_card
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 31 ∨ p = 37 ∨ p = 67 := by
    have h1 : p ∈ Nat.primeFactorsList 51765179004000000 :=
      (Nat.mem_primeFactorsList (by norm_num)).mpr ⟨hp, hpdvd⟩
    have e1 : Nat.primeFactorsList 51765179004000000 =
        [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 7, 11, 31, 37, 67] := by
      norm_num
    rw [e1] at h1
    have h2 := h.odd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    omega
  rcases hp' with rfl | rfl | hp'
  ·
    refine h.false_of_quasisimple_row (E := centralizer ({t} : Set Y)) hquasi hEα htC htα
      (q := 11) (by norm_num) (by norm_num) (by rw [hCcard]; norm_num)
      (by rw [hZc]; norm_num) hcard hCcard ?_
    intro r k hdiv hk1 hkr
    have hr : r ≤ 3 := by
      by_contra hr
      have h1 : 3 ^ 4 * 39916800 ∣ 3 ^ r * 39916800 :=
        Nat.mul_dvd_mul_right (pow_dvd_pow 3 (by omega)) _
      have := h1.trans hdiv
      norm_num at this
    have hk3 : k ≤ 3 := by omega
    interval_cases k <;> norm_num
  ·
    refine h.false_of_quasisimple_row (E := centralizer ({t} : Set Y)) hquasi hEα htC htα
      (q := 11) (by norm_num) (by norm_num) (by rw [hCcard]; norm_num)
      (by rw [hZc]; norm_num) hcard hCcard ?_
    intro r k hdiv hk1 hkr
    have hr : r ≤ 4 := by
      by_contra hr
      have h1 : 5 ^ 5 * 39916800 ∣ 5 ^ r * 39916800 :=
        Nat.mul_dvd_mul_right (pow_dvd_pow 5 (by omega)) _
      have := h1.trans hdiv
      norm_num at this
    have hk4 : k ≤ 4 := by omega
    interval_cases k <;> norm_num
  · have hsyl : ∀ Q : Subgroup Y, IsPGroup p ↥Q → Nat.card ↥Q ≤ p := by
      apply sylow_card_le_of_not_sq_dvd hp
      rw [hcard]
      rcases hp' with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have htclos : t ∈ Subgroup.closure {y : Y | α y = y ∧ Odd (orderOf y)} :=
      fixSub_le_closure_odd_of_perfect_aux _ α hEα
        (perfect_le_closure_odd _ hquasi.1 htC)
    rcases hp' with rfl | rfl | hp'
    ·
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 7 (by rw [hCcard]; norm_num)
      exact h.false_of_sylow_row hsyl (Or.inl ⟨(s : Y), hEα _ s.2, by
        rw [Subgroup.orderOf_coe]; exact hs⟩)
    ·
      obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 11 (by rw [hCcard]; norm_num)
      exact h.false_of_sylow_row hsyl (Or.inl ⟨(s : Y), hEα _ s.2, by
        rw [Subgroup.orderOf_coe]; exact hs⟩)
    ·
      refine h.false_of_sylow_row hsyl (Or.inr ⟨t, ht2, ?_, htclos, ?_⟩)
      · intro ht1; rw [ht1, orderOf_one] at hto; omega
      · rw [hCcard]
        rcases hp' with rfl | rfl | rfl <;> norm_num

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentU62Perfect
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentChain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentU62Twist

public section

namespace CFSG.AGLEmbedding.U62O10Cent

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
  CFSG.AGLEmbedding.U62ThreeCent

theorem prod_zmod_three {M : Type*} [CommMonoid M] (f : ZMod 3 → M) :
    ∏ t : ZMod 3, f t = f 0 * f 1 * f 2 :=
  Fin.prod_univ_three f

theorem card_gramU_fib (κ : Fin 6 → ZMod 3) (t : ZMod 3) {n : ℕ} (h : Ncnt κ t = n) (hn : n ≤ 3) :
    Nat.card (gramU uData (1 : Matrix (Fib κ t) (Fib κ t) F4)) =
      (![1, 3, 18, 648] : Fin 4 → ℕ) ⟨n, by omega⟩ :=
  card_gramU_one h hn

theorem Ncnt_ne_six (κ : Fin 6 → ZMod 3) (a : gramSU uData M6) (ha : (a : GL (Fin 6) F4) = dK κ)
    (hx : orderOf (a : P6) = 3) (t : ZMod 3) : Ncnt κ t ≠ 6 := by
  intro h6
  have h0 : Fintype.card {i // κ i ≠ t} = 0 := by
    rw [card_ne_Ncnt, h6]
  have hall : ∀ i, κ i = t := fun i => by
    by_contra hi
    have : Nonempty {i // κ i ≠ t} := ⟨⟨i, hi⟩⟩
    exact Fintype.card_ne_zero h0
  have hmem : a ∈ normOneScalars uData (gramSU uData M6) 6 := by
    refine ⟨rootUnit t, norm_eq_one _, ?_, ?_⟩
    · rw [show 6 = 3 * 2 from rfl, pow_mul, units_pow_three, one_pow]
    · rw [ha]
      apply Units.ext
      rw [coe_diagGL6, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      simp [hall]
  have : (a : P6) = 1 := (QuotientGroup.eq_one_iff a).2 hmem
  rw [this, orderOf_one] at hx
  omega

theorem prod_card_gramU_fib (κ : Fin 6 → ZMod 3) {a b c : ℕ} (h0 : Ncnt κ 0 = a)
    (h1 : Ncnt κ 1 = b) (h2 : Ncnt κ 2 = c) (ha : a ≤ 3) (hb : b ≤ 3) (hc : c ≤ 3) :
    ∏ t : ZMod 3, Nat.card (gramU uData (1 : Matrix (Fib κ t) (Fib κ t) F4)) =
      (![1, 3, 18, 648] : Fin 4 → ℕ) ⟨a, by omega⟩ * (![1, 3, 18, 648] : Fin 4 → ℕ) ⟨b, by omega⟩ *
        (![1, 3, 18, 648] : Fin 4 → ℕ) ⟨c, by omega⟩ := by
  rw [prod_zmod_three, card_gramU_fib κ 0 h0 ha, card_gramU_fib κ 1 h1 hb,
    card_gramU_fib κ 2 h2 hc]

theorem prod_card_gramU_330 (κ : Fin 6 → ZMod 3) (h0 : Ncnt κ 0 = 3) (h1 : Ncnt κ 1 = 3)
    (h2 : Ncnt κ 2 = 0) :
    ∏ t : ZMod 3, Nat.card (gramU uData (1 : Matrix (Fib κ t) (Fib κ t) F4)) = 648 * 648 * 1 := by
  rw [prod_card_gramU_fib κ h0 h1 h2 (by norm_num) (by norm_num) (by norm_num)]
  rfl

theorem prod_card_gramU_303 (κ : Fin 6 → ZMod 3) (h0 : Ncnt κ 0 = 3) (h1 : Ncnt κ 1 = 0)
    (h2 : Ncnt κ 2 = 3) :
    ∏ t : ZMod 3, Nat.card (gramU uData (1 : Matrix (Fib κ t) (Fib κ t) F4)) = 648 * 1 * 648 := by
  rw [prod_card_gramU_fib κ h0 h1 h2 (by norm_num) (by norm_num) (by norm_num)]
  rfl

theorem prod_card_gramU_033 (κ : Fin 6 → ZMod 3) (h0 : Ncnt κ 0 = 0) (h1 : Ncnt κ 1 = 3)
    (h2 : Ncnt κ 2 = 3) :
    ∏ t : ZMod 3, Nat.card (gramU uData (1 : Matrix (Fib κ t) (Fib κ t) F4)) = 1 * 648 * 648 := by
  rw [prod_card_gramU_fib κ h0 h1 h2 (by norm_num) (by norm_num) (by norm_num)]
  rfl

theorem prod_card_gramU_222 (κ : Fin 6 → ZMod 3) (h0 : Ncnt κ 0 = 2) (h1 : Ncnt κ 1 = 2)
    (h2 : Ncnt κ 2 = 2) :
    ∏ t : ZMod 3, Nat.card (gramU uData (1 : Matrix (Fib κ t) (Fib κ t) F4)) = 18 * 18 * 18 := by
  rw [prod_card_gramU_fib κ h0 h1 h2 (by norm_num) (by norm_num) (by norm_num)]
  rfl

theorem dvd_of_aut_count {S C B s s₀ r : ℕ} (heq : S * 3 = C * s * r) (hC : C ∣ B) (hs : s ∣ s₀)
    (hr : r ∣ 2) (hB : B * s₀ * 2 ∣ 2 ^ 7 * 3 ^ 7 * 3) : S ∣ 2 ^ 7 * 3 ^ 7 := by
  have h1 : S * 3 ∣ 2 ^ 7 * 3 ^ 7 * 3 := by
    rw [heq]
    exact (mul_dvd_mul (mul_dvd_mul hC hs) hr).trans hB
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1

theorem centAlt_diag (κ : Fin 6 → ZMod 3) (a : gramSU uData M6)
    (ha : (a : GL (Fin 6) F4) = dK κ) (hx : orderOf (a : P6) = 3) : CentAlt (a : P6) := by
  have hdet : ∏ i, rootUnit (κ i) = 1 := by
    have h1 := a.2.2
    rw [ha, coe_diagGL6, det_diagonal] at h1
    apply Units.ext
    rw [Units.coe_prod, Units.val_one]
    exact h1
  let y : GU6 := ⟨(a : GL (Fin 6) F4), a.2.1⟩
  have hy : (y : GL (Fin 6) F4) = dK κ := ha
  have hy' : conj6 y = MulAut.conj (a : P6) := primeFormConjHom_eq_conj uData M6 a
  have hker8 := (unitary_prime_form_full_semilinear_realization uData hC6 hn6 hq6).2.2.2.2.2.2.2.1
  have hker : (primeFormFieldFactor uData hC6 hn6 hq6).ker = conj6.range := hker8
  obtain ⟨r, s, hr, hs, hstrong, heq⟩ := card_centralizer_aut_mul conj6
    (primeFormFieldFactor uData hC6 hn6 hq6) hker ker_conj6_le_center (a : P6) y hy'
  rw [card_ringAut_F4] at hr
  rw [card_ker_conj6] at hs heq
  have hC := card_centralizer_dvd_prod hy
  have hN6 := Ncnt_ne_six κ a ha hx
  rcases type_cases κ hdet with h6 | h4 | h33 | h222
  · exfalso
    rcases h6 with h | h | h
    · exact hN6 0 h
    · exact hN6 1 h
    · exact hN6 2 h
  · refine Or.inl ?_
    rcases h4 with h | h | h
    · exact exists_perfect_of_four κ a ha 0 h
    · exact exists_perfect_of_four κ a ha 1 h
    · exact exists_perfect_of_four κ a ha 2 h
  · refine Or.inr ?_
    have hpat : ¬(Ncnt κ 0 = Ncnt κ 1 ∧ Ncnt κ 1 = Ncnt κ 2) := by omega
    have hs1 : s ∣ 1 := by
      rw [hstrong (fun g hg => commute_of_not_constant κ hy hpat g hg)]
    rcases h33 with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · rw [prod_card_gramU_330 κ h0 h1 h2] at hC
      exact dvd_of_aut_count heq hC hs1 hr (by norm_num)
    · rw [prod_card_gramU_303 κ h0 h1 h2] at hC
      exact dvd_of_aut_count heq hC hs1 hr (by norm_num)
    · rw [prod_card_gramU_033 κ h0 h1 h2] at hC
      exact dvd_of_aut_count heq hC hs1 hr (by norm_num)
  · refine Or.inr ?_
    obtain ⟨h0, h1, h2⟩ := h222
    rw [prod_card_gramU_222 κ h0 h1 h2] at hC
    exact dvd_of_aut_count heq hC hs hr (by norm_num)

end CFSG.AGLEmbedding.U62O10Cent

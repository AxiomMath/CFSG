module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WModule

public section

namespace CFSG.OddStandard.Seitz77

open CFSG.ComponentClassification.PSL3Four

namespace Lift4

theorem no_commuting_lifts_int (A B : Fin 4 → Fin 4 → ℤ)
    (hA : ∀ i j, 2 ∣ A i j - WFacts.lowA i j) (hB : ∀ i j, 2 ∣ B i j - WFacts.lowB i j)
    (haa : ∀ i j, 4 ∣ (∑ l, A i l * A l j) - (if i = j then 1 else 0))
    (hbb : ∀ i j, 4 ∣ (∑ l, B i l * B l j) - (if i = j then 1 else 0))
    (hab : ∀ i j, 4 ∣ (∑ l, A i l * B l j) - (∑ l, B i l * A l j)) : False := by
  obtain ⟨x, hx⟩ : ∃ x : Fin 4 → Fin 4 → ℤ, ∀ i j, A i j = WFacts.lowA i j + 2 * x i j :=
    ⟨fun i j => (A i j - WFacts.lowA i j) / 2, fun i j => by
      beta_reduce; obtain ⟨k, hk⟩ := hA i j; omega⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin 4 → Fin 4 → ℤ, ∀ i j, B i j = WFacts.lowB i j + 2 * y i j :=
    ⟨fun i j => (B i j - WFacts.lowB i j) / 2, fun i j => by
      beta_reduce; obtain ⟨k, hk⟩ := hB i j; omega⟩
  have a02 := haa 0 2
  have a13 := haa 1 3
  have b03 := hbb 0 3
  have b12 := hbb 1 2
  have b13 := hbb 1 3
  have c02 := hab 0 2
  have c03 := hab 0 3
  have c12 := hab 1 2
  simp only [Fin.sum_univ_four, hx, hy, WFacts.lowA, WFacts.lowB] at a02 a13 b03 b12 b13 c02 c03 c12
  simp at a02 a13 b03 b12 b13 c02 c03 c12
  ring_nf at a02 a13 b03 b12 b13 c02 c03 c12
  omega

section Coords

variable {W : Type} [AddCommGroup W]

def comb (w : Fin 4 → W) (k : Fin 4 → ℤ) : W := ∑ i, k i • w i

theorem comb_sub (w : Fin 4 → W) (k k' : Fin 4 → ℤ) :
    comb w (fun i => k i - k' i) = comb w k - comb w k' := by
  simp [comb, sub_smul, Finset.sum_sub_distrib]

theorem comb_single (w : Fin 4 → W) (j : Fin 4) :
    comb w (fun i => if i = j then 1 else 0) = w j := by
  simp [comb]

theorem comb_two_mul (w : Fin 4 → W) (l : Fin 4 → ℤ) :
    comb w (fun i => 2 * l i) = comb w l + comb w l := by
  simp [comb, mul_smul, two_smul, Finset.sum_add_distrib]

theorem delta_comb (δ : W →+ F4V) (w : Fin 4 → W) (hw : ∀ i, δ (w i) = WFacts.basisE i)
    (k : Fin 4 → ℤ) : δ (comb w k) = ∑ i, k i • WFacts.basisE i := by
  simp [comb, map_sum, map_zsmul, hw]

theorem coords (hW : Nat.card W = 256) (δ : W →+ F4V) (hδ : Function.Surjective δ)
    (h2 : ∀ x : W, x + x = 0 → δ x = 0) :
    ∃ w : Fin 4 → W, (∀ i, δ (w i) = WFacts.basisE i) ∧
      (∀ k : Fin 4 → ℤ, comb w k = 0 → ∀ i, 4 ∣ k i) ∧
      (∀ x : W, ∃ k : Fin 4 → ℤ, x = comb w k) := by
  choose w hw using fun i => hδ (WFacts.basisE i)
  have hind : ∀ k : Fin 4 → ℤ, comb w k = 0 → ∀ i, 4 ∣ k i := by
    intro k hk
    have h1 : ∑ i, k i • WFacts.basisE i = 0 := by rw [← delta_comb δ w hw, hk, map_zero]
    have h2k := WFacts.basisE_indep k h1
    choose l hl using h2k
    have hkl : k = fun i => 2 * l i := funext hl
    have h3 : comb w l + comb w l = 0 := by rw [← comb_two_mul, ← hkl]; exact hk
    have h4 := h2 _ h3
    rw [delta_comb δ w hw] at h4
    have h5 := WFacts.basisE_indep l h4
    intro i
    rw [hl i]
    obtain ⟨m, hm⟩ := h5 i
    exact ⟨m, by rw [hm]; ring⟩
  refine ⟨w, hw, hind, ?_⟩
  have : Finite W := Nat.finite_of_card_ne_zero (by omega)
  let Φ : (Fin 4 → Fin 4) → W := fun b => comb w (fun i => ((b i : ℕ) : ℤ))
  have hΦ : Function.Injective Φ := by
    intro b b' h
    have h' : comb w (fun i => ((b i : ℕ) : ℤ) - ((b' i : ℕ) : ℤ)) = 0 := by
      rw [comb_sub]; exact sub_eq_zero.mpr h
    funext i
    have h4 := hind _ h' i
    apply Fin.ext
    have hb := (b i).isLt
    have hb' := (b' i).isLt
    omega
  have hbij : Function.Bijective Φ :=
    hΦ.bijective_of_nat_card_le (by simp [Nat.card_eq_fintype_card, hW])
  intro x
  obtain ⟨b, rfl⟩ := hbij.2 x
  exact ⟨fun i => ((b i : ℕ) : ℤ), rfl⟩

theorem hom_comb (w : Fin 4 → W) (f : W →+ W) (M : Fin 4 → Fin 4 → ℤ)
    (hM : ∀ j, f (w j) = comb w (fun i => M i j)) (k : Fin 4 → ℤ) :
    f (comb w k) = comb w (fun i => ∑ j, M i j * k j) := by
  simp only [comb, map_sum, map_zsmul, hM]
  simp only [Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem no_commuting_lifts_add (hW : Nat.card W = 256) (δ : W →+ F4V)
    (hδ : Function.Surjective δ) (h2 : ∀ x : W, x + x = 0 → δ x = 0) (a b : W →+ W)
    (haa : ∀ x, a (a x) = x) (hbb : ∀ x, b (b x) = x) (hab : ∀ x, a (b x) = b (a x))
    (ha : ∀ x, δ (a x) = cUp 1 (δ x)) (hb : ∀ x, δ (b x) = cUp F4.ω (δ x)) : False := by
  obtain ⟨w, hw1, hw2, hw3⟩ := coords hW δ hδ h2
  choose Ac hAc using fun j => hw3 (a (w j))
  choose Bc hBc using fun j => hw3 (b (w j))
  have hAw : ∀ j, a (w j) = comb w (fun i => Ac j i) := hAc
  have hBw : ∀ j, b (w j) = comb w (fun i => Bc j i) := hBc
  have hAcomb := hom_comb w a (fun i j => Ac j i) hAw
  have hBcomb := hom_comb w b (fun i j => Bc j i) hBw
  have hAp : ∀ i j, 2 ∣ Ac j i - WFacts.lowA i j := by
    intro i j
    have h1 : ∑ i, (Ac j i - WFacts.lowA i j) • WFacts.basisE i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← delta_comb δ w hw1 (fun i => Ac j i), ← hAw j, ha, hw1, WFacts.cUp_one_basisE, sub_self]
    exact WFacts.basisE_indep _ h1 i
  have hBp : ∀ i j, 2 ∣ Bc j i - WFacts.lowB i j := by
    intro i j
    have h1 : ∑ i, (Bc j i - WFacts.lowB i j) • WFacts.basisE i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← delta_comb δ w hw1 (fun i => Bc j i), ← hBw j, hb, hw1, WFacts.cUp_omega_basisE,
        sub_self]
    exact WFacts.basisE_indep _ h1 i
  have haaA : ∀ i j, 4 ∣ (∑ l, Ac l i * Ac j l) - (if i = j then 1 else 0) := by
    intro i j
    have h1 : comb w (fun i => ∑ l, Ac l i * Ac j l) =
        comb w (fun i => if i = j then 1 else 0) := by
      rw [← hAcomb (fun l => Ac j l), ← hAw j, haa, comb_single]
    have h2' : comb w (fun i => (∑ l, Ac l i * Ac j l) - (if i = j then 1 else 0)) = 0 := by
      rw [comb_sub, h1, sub_self]
    exact hw2 _ h2' i
  have hbbB : ∀ i j, 4 ∣ (∑ l, Bc l i * Bc j l) - (if i = j then 1 else 0) := by
    intro i j
    have h1 : comb w (fun i => ∑ l, Bc l i * Bc j l) =
        comb w (fun i => if i = j then 1 else 0) := by
      rw [← hBcomb (fun l => Bc j l), ← hBw j, hbb, comb_single]
    have h2' : comb w (fun i => (∑ l, Bc l i * Bc j l) - (if i = j then 1 else 0)) = 0 := by
      rw [comb_sub, h1, sub_self]
    exact hw2 _ h2' i
  have habAB : ∀ i j, 4 ∣ (∑ l, Ac l i * Bc j l) - (∑ l, Bc l i * Ac j l) := by
    intro i j
    have h1 : comb w (fun i => ∑ l, Ac l i * Bc j l) = comb w (fun i => ∑ l, Bc l i * Ac j l) := by
      rw [← hAcomb (fun l => Bc j l), ← hBw j, hab, hAw j, hBcomb (fun l => Ac j l)]
    have h2' : comb w (fun i => (∑ l, Ac l i * Bc j l) - (∑ l, Bc l i * Ac j l)) = 0 := by
      rw [comb_sub, h1, sub_self]
    exact hw2 _ h2' i
  exact no_commuting_lifts_int (fun i j => Ac j i) (fun i j => Bc j i) hAp hBp haaA hbbB habAB

end Coords

theorem no_commuting_lifts_mul {W : Type} [CommGroup W] (hW : Nat.card W = 256)
    (δ : W →* Multiplicative F4V) (hδ : Function.Surjective δ)
    (h2 : ∀ x : W, x * x = 1 → δ x = 1) (a b : W →* W) (haa : ∀ x, a (a x) = x)
    (hbb : ∀ x, b (b x) = x) (hab : ∀ x, a (b x) = b (a x))
    (ha : ∀ x, δ (a x) = Multiplicative.ofAdd (cUp 1 (Multiplicative.toAdd (δ x))))
    (hb : ∀ x, δ (b x) = Multiplicative.ofAdd (cUp F4.ω (Multiplicative.toAdd (δ x)))) : False := by
  refine no_commuting_lifts_add (W := Additive W) (by rwa [Nat.card_congr Additive.toMul]) 
    (MonoidHom.toAdditiveLeft δ) hδ ?_ (MonoidHom.toAdditive a) (MonoidHom.toAdditive b) haa hbb hab
    ?_ ?_
  · exact h2
  · exact ha
  · exact hb

end Lift4

end CFSG.OddStandard.Seitz77

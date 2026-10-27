module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.TransvAa

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Native
open scoped Matrix

section Aa


theorem conj_eq_of_eqRows {n g y : J} {R Rg Ry : Array V4} (hR : IsRows R n) (hg : IsRows Rg g)
    (hy : IsRows Ry y) (h : eqRows (mulRows R Rg) (mulRows Ry R) = true) : n * g * n⁻¹ = y := by
  have e := (hR.mul hg).eq_of_eqRows (hy.mul hR) h
  rw [e]
  simp

theorem isRows_gE (e₀ e₁ e₂ e₃ : ℕ) :
    IsRows (rowsGE e₀ e₁ e₂ e₃) (gA 0 ^ e₀ * gA 1 ^ e₁ * gA 2 ^ e₂ * gA 3 ^ e₃) :=
  (((isRows_gAa1.pow e₀).mul (isRows_gAa2.pow e₁)).mul (isRows_gAa3.pow e₂)).mul
    (isRows_gAa4.pow e₃)

theorem q1_conj_gA (j : Fin 4) :
    q 1 * gA j * (q 1)⁻¹ = ex (fun i => Mmat i j) := by
  obtain ⟨-, -, -, -, h0, h1, h2, h3⟩ := Certificates.certificate24216
  fin_cases j
  · exact conj_eq_of_eqRows (isRows_q 1) isRows_gAa1 (isRows_gE 1 1 2 2) h0
  · exact conj_eq_of_eqRows (isRows_q 1) isRows_gAa2 (isRows_gE 0 1 0 0) h1
  · exact conj_eq_of_eqRows (isRows_q 1) isRows_gAa3 (isRows_gE 2 0 3 2) h2
  · exact conj_eq_of_eqRows (isRows_q 1) isRows_gAa4 (isRows_gE 0 3 0 3) h3

theorem q1_conj_ex (R : AaRel) (e : Fin 4 → ZMod 4) :
    q 1 * ex e * (q 1)⁻¹ = ex (fun i => ∑ j, Mmat i j * e j) :=
  ex_conj R Mmat q1_conj_gA e

theorem card_le_16_of_centralizes_q1
    (R : AaRel) {K : Subgroup J} (hK : K ≤ AaJ) (hc : ∀ x ∈ K, q 1 * x = x * q 1) :
    Nat.card K ≤ 16 := by
  choose! f hf using fun x (hx : x ∈ AaJ) => ex_surj R hx
  have hfix : ∀ x : K, (fun i => ∑ j, Mmat i j * f x j) = f x := fun x => by
    apply ex_injective R
    rw [← q1_conj_ex R, hf x (hK x.2)]
    have h := hc x x.2
    have e : q 1 * (x : J) * (q 1)⁻¹ = (x : J) := by rw [h, mul_inv_cancel_right]
    exact e
  let φ : K → {e : Fin 4 → ZMod 4 // (fun i => ∑ j, Mmat i j * e j) = e} := fun x =>
    ⟨f x, hfix x⟩
  have hφ : Function.Injective φ := fun x y h => by
    have h1 : f x = f y := congrArg Subtype.val h
    apply Subtype.ext
    rw [← hf x (hK x.2), ← hf y (hK y.2), h1]
  calc Nat.card K ≤ Nat.card {e : Fin 4 → ZMod 4 // (fun i => ∑ j, Mmat i j * e j) = e} :=
        Nat.card_le_card_of_injective φ hφ
    _ = (Finset.univ.filter fun e : Fin 4 → ZMod 4 => (fun i => ∑ j, Mmat i j * e j) = e).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 16 := card_fix_Mmat

theorem card_le_16_of_centralizes_q1b
    (R : AaRel) {K : Subgroup J} (hK : K ≤ AaJ)
    (hc : ∀ x ∈ K, (q 1 * bAa) * x = x * (q 1 * bAa)) : Nat.card K ≤ 16 := by
  choose! f hf using fun x (hx : x ∈ AaJ) => ex_surj R hx
  have hfix : ∀ x : K, (fun i => ∑ j, Mmat i j * f x j) = fun i => - f x i := fun x => by
    have hx := hK x.2
    have e1 : (q 1 * bAa) * (x : J) * (q 1 * bAa)⁻¹ = (x : J) := by
      have h := hc x x.2
      rw [h, mul_inv_cancel_right]
    have e2 : (q 1 * bAa) * (x : J) * (q 1 * bAa)⁻¹ =
        ex (-(fun i => ∑ j, Mmat i j * f x j)) := by
      have hb := bAa_inv R _ hx
      calc (q 1 * bAa) * (x : J) * (q 1 * bAa)⁻¹ = q 1 * (bAa * x * bAa⁻¹) * (q 1)⁻¹ := by group
        _ = q 1 * (x : J)⁻¹ * (q 1)⁻¹ := by rw [hb]
        _ = (q 1 * (x : J) * (q 1)⁻¹)⁻¹ := by group
        _ = (q 1 * ex (f x) * (q 1)⁻¹)⁻¹ := by rw [hf x hx]
        _ = (ex (fun i => ∑ j, Mmat i j * f x j))⁻¹ := by rw [q1_conj_ex R]
        _ = ex (-(fun i => ∑ j, Mmat i j * f x j)) := (ex_neg R _).symm
    have h3 : ex (-(fun i => ∑ j, Mmat i j * f x j)) = ex (f x) := by rw [← e2, e1, hf x hx]
    have h4 := ex_injective R h3
    funext i
    have h5 := congrFun h4 i
    simp only [Pi.neg_apply] at h5
    rw [← h5, neg_neg]
  let φ : K → {e : Fin 4 → ZMod 4 // (fun i => ∑ j, Mmat i j * e j) = fun i => - e i} := fun x =>
    ⟨f x, hfix x⟩
  have hφ : Function.Injective φ := fun x y h => by
    have h1 : f x = f y := congrArg Subtype.val h
    apply Subtype.ext
    rw [← hf x (hK x.2), ← hf y (hK y.2), h1]
  calc Nat.card K ≤
        Nat.card {e : Fin 4 → ZMod 4 // (fun i => ∑ j, Mmat i j * e j) = fun i => - e i} :=
        Nat.card_le_card_of_injective φ hφ
    _ = (Finset.univ.filter fun e : Fin 4 → ZMod 4 =>
          (fun i => ∑ j, Mmat i j * e j) = fun i => - e i).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 16 := card_neg_Mmat

end Aa

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh

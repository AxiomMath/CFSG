module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OModel
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestEndRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

private def s4Drop (v : OW F) : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F :=
  Sum.elim (fun i : Fin 1 => v (Sum.inl i.succ))
    (Sum.elim (fun i : Fin 1 => v (Sum.inr (Sum.inl i.succ))) fun k : Fin 2 => v (Sum.inr (Sum.inr k)))

private def s4Add (w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F) : OW F :=
  Sum.elim (Fin.cons 0 (fun i : Fin 1 => w (Sum.inl i)) : Fin 2 → F)
    (Sum.elim (Fin.cons 0 (fun i : Fin 1 => w (Sum.inr (Sum.inl i))) : Fin 2 → F)
      (fun k : Fin 2 => w (Sum.inr (Sum.inr k))))

private theorem s4Drop_zero : s4Drop (0 : OW F) = 0 := by
  funext s
  rcases s with i | i | k <;> rfl

private theorem s4Drop_s4Add (w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F) : s4Drop (s4Add w) = w := by
  funext s
  rcases s with i | i | k
  · fin_cases i
    rfl
  · fin_cases i
    rfl
  · rfl

private theorem s4Add_s4Drop {v : OW F} (h0 : v (Sum.inl idx0) = 0)
    (h1 : v (Sum.inr (Sum.inl idx0)) = 0) : s4Add (s4Drop v) = v := by
  funext s
  rcases s with i | i | k
  · fin_cases i
    · exact h0.symm
    · rfl
  · fin_cases i
    · exact h1.symm
    · rfl
  · rfl

private theorem s4Drop_ne_zero {v : OW F} (h0 : v (Sum.inl idx0) = 0)
    (h1 : v (Sum.inr (Sum.inl idx0)) = 0) (hv : v ≠ 0) : s4Drop v ≠ 0 := by
  intro h
  apply hv
  funext s
  rcases s with i | i | k
  · fin_cases i
    · exact h0
    · exact congrFun h (Sum.inl 0)
  · fin_cases i
    · exact h1
    · exact congrFun h (Sum.inr (Sum.inl 0))
  · exact congrFun h (Sum.inr (Sum.inr k))

private theorem s4Add_ne_zero {w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F} (hw : w ≠ 0) : s4Add w ≠ 0 := by
  intro h
  apply hw
  have h2 := congrArg s4Drop h
  rw [s4Drop_s4Add, s4Drop_zero] at h2
  exact h2

private theorem s4Add_fst (w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F) : s4Add w (Sum.inl idx0) = 0 := rfl

private theorem s4Add_snd (w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F) :
    s4Add w (Sum.inr (Sum.inl idx0)) = 0 := rfl

private theorem s4Drop_inl (v : OW F) : s4Drop v (Sum.inl 0) = v (Sum.inl idx1) := rfl

private theorem s4Drop_inr_inl (v : OW F) :
    s4Drop v (Sum.inr (Sum.inl 0)) = v (Sum.inr (Sum.inl idx1)) := rfl

private theorem s4Drop_inr_inr (v : OW F) (k : Fin 2) :
    s4Drop v (Sum.inr (Sum.inr k)) = v (Sum.inr (Sum.inr k)) := rfl

private theorem sum_fin_sub_two (g : Fin (3 - 1) → F) :
    ∑ i : Fin (3 - 1), g i = g idx0 + g idx1 :=
  Fin.sum_univ_two g

private theorem quadMinus_three_apply (v : OW F) :
    CFSG.LieType.Universal.Spin.quadMinus 3 F b c v =
      v (Sum.inl idx0) * v (Sum.inr (Sum.inl idx0)) + v (Sum.inl idx1) * v (Sum.inr (Sum.inl idx1)) +
        v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
        c * v (Sum.inr (Sum.inr 1)) ^ 2 := by
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply, sum_fin_sub_two]

private theorem quadMinus_two_apply (w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F) :
    CFSG.LieType.Universal.Spin.quadMinus (1 + 1) F b c w =
      w (Sum.inl 0) * w (Sum.inr (Sum.inl 0)) + w (Sum.inr (Sum.inr 0)) ^ 2 +
        b * w (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 1)) + c * w (Sum.inr (Sum.inr 1)) ^ 2 := by
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply, Fin.sum_univ_one]

private theorem quadMinus_s4Drop {v : OW F} (h0 : v (Sum.inl idx0) = 0)
    (h1 : v (Sum.inr (Sum.inl idx0)) = 0) :
    CFSG.LieType.Universal.Spin.quadMinus (1 + 1) F b c (s4Drop v) =
      CFSG.LieType.Universal.Spin.quadMinus 3 F b c v := by
  rw [quadMinus_two_apply, quadMinus_three_apply, h0, h1, s4Drop_inl, s4Drop_inr_inl,
    s4Drop_inr_inr, s4Drop_inr_inr]
  ring

private theorem quadMinus_s4Add (w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F) :
    CFSG.LieType.Universal.Spin.quadMinus 3 F b c (s4Add w) =
      CFSG.LieType.Universal.Spin.quadMinus (1 + 1) F b c w := by
  rw [← quadMinus_s4Drop (s4Add_fst w) (s4Add_snd w), s4Drop_s4Add]

private def s4Equiv :
    {v : OW F // v (Sum.inl idx0) = 0 ∧ v (Sum.inr (Sum.inl idx0)) = 0 ∧ v ≠ 0 ∧
      CFSG.LieType.Universal.Spin.quadMinus 3 F b c v = 0} ≃
    {w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F // w ≠ 0 ∧
      CFSG.LieType.Universal.Spin.quadMinus (1 + 1) F b c w = 0} where
  toFun v := ⟨s4Drop v.1, s4Drop_ne_zero v.2.1 v.2.2.1 v.2.2.2.1,
    (quadMinus_s4Drop v.2.1 v.2.2.1).trans v.2.2.2.2⟩
  invFun w := ⟨s4Add w.1, s4Add_fst w.1, s4Add_snd w.1, s4Add_ne_zero w.2.1,
    (quadMinus_s4Add w.1).trans w.2.2⟩
  left_inv v := Subtype.ext (s4Add_s4Drop v.2.1 v.2.2.1)
  right_inv w := Subtype.ext (s4Drop_s4Add w.1)

theorem card_singPerpSet (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card {v : OW F // v (Sum.inl idx0) = 0 ∧ v (Sum.inr (Sum.inl idx0)) = 0 ∧ v ≠ 0 ∧
      quadMinus 3 F b c v = 0} = (Nat.card F ^ 2 + 1) * (Nat.card F - 1) := by
  have hq : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hcard : (Nat.card {v : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F //
      CFSG.LieType.Universal.Spin.quadMinus (1 + 1) F b c v = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ 2 + 1) * ((Nat.card F : ℤ) - 1) := by
    have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus 1 hirr).1
    rw [pow_one] at h
    exact h
  have hsucc : Nat.card {v : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F //
      CFSG.LieType.Universal.Spin.quadMinus (1 + 1) F b c v = 0} =
      Nat.card {w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F // w ≠ 0 ∧
        CFSG.LieType.Universal.Spin.quadMinus (1 + 1) F b c w = 0} + 1 :=
    CFSG.StandardType.OrthRestEnd.card_singular_eq_succ
      (CFSG.LieType.Universal.Spin.quadMinus (1 + 1) F b c)
  have hT : (Nat.card {w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → F // w ≠ 0 ∧
      CFSG.LieType.Universal.Spin.quadMinus (1 + 1) F b c w = 0} : ℤ) =
      ((Nat.card F : ℤ) ^ 2 + 1) * ((Nat.card F : ℤ) - 1) := by
    rw [hsucc] at hcard
    push_cast at hcard
    linarith
  refine (Nat.card_congr s4Equiv).trans ?_
  zify [hq]
  exact hT

theorem not_two_dvd_card_singPerpSet (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    ¬ 2 ∣ Nat.card {v : OW F // v (Sum.inl idx0) = 0 ∧ v (Sum.inr (Sum.inl idx0)) = 0 ∧ v ≠ 0 ∧
      quadMinus 3 F b c v = 0} := by
  rw [card_singPerpSet hirr, hF]
  have hm : Even (2 ^ n : ℕ) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have h1 : Odd ((2 ^ n) ^ 2 + 1 : ℕ) := (hm.pow_of_ne_zero (by norm_num)).add_one
  have h2 : Odd (2 ^ n - 1 : ℕ) := Nat.Even.sub_odd Nat.one_le_two_pow hm odd_one
  intro hdvd
  exact (Nat.not_even_iff_odd.mpr (h1.mul h2)) (even_iff_two_dvd.mpr hdvd)

end CFSG.LocalAnalysis.RankThreeUC

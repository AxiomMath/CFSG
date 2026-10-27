module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQMat

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Assembly CFSG.Open
open CFSG.Timmesfeld.Orders CFSG.Timmesfeld.ClassicalOrders CFSG.Assembly.LowTwoRank

theorem twoPart_two_pow_mul_odd {N r : ℕ} (hr : Odd r) : twoPart (2 ^ N * r) = 2 ^ N := by
  have h2 : ¬ 2 ∣ r := by
    rintro ⟨c, hc⟩
    exact (Nat.not_even_iff_odd.2 hr) ⟨c, by omega⟩
  unfold twoPart
  rw [Nat.factorization_mul (by positivity) hr.pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h2, add_zero, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two]
  simp

theorem twoPart_of_profile {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) : twoPart m = 2 ^ N := by
  obtain ⟨r, hr, rfl⟩ := h.two
  exact twoPart_two_pow_mul_odd hr

section Classical

variable {L : Type} [Field L] [Finite L]

theorem twoPart_card_matrix_group {ι : Type} [Fintype ι] [DecidableEq ι] {e : ℕ} (he : 1 ≤ e)
    (hL : Nat.card L = 2 ^ e) (H : Subgroup (GL ι L)) :
    twoPart (Nat.card H) = twoPart (Nat.card (StatedProj H)) :=
  (twoPart_card_quotient _ (scalars_subgroupOf_odd he hL H)).symm

theorem twoPart_card_statedProj_statedSL {n e : ℕ} (hn : 2 ≤ n)
    (he : 1 ≤ e) (hL : Nat.card L = 2 ^ e) :
    twoPart (Nat.card (StatedProj (StatedSL n L))) = 2 ^ (e * (n * (n - 1) / 2)) := by
  have h : Nat.card (StatedProj (StatedSL n L)) = ordA (n - 1) (2 ^ e) := by
    rw [card_statedProj_statedSL (by omega), hL, ordA, Nat.sub_add_cancel (by omega : 1 ≤ n),
      mul_comm (n - 1) n]
  rw [h, twoPart_of_profile (profile_ordA (n := n - 1) (f := e) (by omega) he)]
  congr 2
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm]

theorem twoPart_card_SL {n e : ℕ} (hn : 2 ≤ n) (he : 1 ≤ e) (hL : Nat.card L = 2 ^ e) :
    twoPart (Nat.card (LargeEvenSLGroup (Fin n) L)) = 2 ^ (e * (n * (n - 1) / 2)) := by
  rw [twoPart_card_matrix_group he hL, ← twoPart_card_statedProj_statedSL hn he hL]
  exact congrArg twoPart (Nat.card_congr (CFSG.StandardType.nonempty_proj_congr
    (CFSG.Open.StatedAPI.statedSL_eq_ker_det n L).symm).some.toEquiv)

theorem twoPart_card_statedProj_statedSU {n g : ℕ} (hn : 3 ≤ n) (hg : 1 ≤ g)
    (hL : Nat.card L = (2 ^ g) ^ 2) :
    twoPart (Nat.card (StatedProj (StatedSU n (2 ^ g) L))) = 2 ^ (g * (n * (n - 1) / 2)) := by
  have h : Nat.card (StatedProj (StatedSU n (2 ^ g) L)) = ordTwistedA (n - 1) (2 ^ g) := by
    rw [card_statedProj_statedSU Nat.prime_two hg hL (by omega), ordTwistedA,
      Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm (n - 1) n]
  rw [h, twoPart_of_profile (profile_ordTwistedA (n := n - 1) (g := g) (by omega) hg)]
  congr 2
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm]

theorem twoPart_card_statedProj_statedSp {n e : ℕ} (he : 1 ≤ e) (hL : Nat.card L = 2 ^ e) :
    twoPart (Nat.card (StatedProj (StatedSp n L))) = 2 ^ (e * (n * n)) := by
  have : CharP L 2 := charP_two_of_card_eq hL
  have hgcd : Nat.gcd 2 (2 ^ e - 1) = 1 :=
    Nat.coprime_two_left.mpr (by simpa using odd_two_pow_pow_sub_one he (n := 1) le_rfl)
  have h : Nat.card (StatedProj (StatedSp n L)) = ordBC n (2 ^ e) := by
    rw [card_statedProj_statedSp_of_charTwo, hL, ordBC, hgcd, Nat.div_one, sq]
  rw [h, twoPart_of_profile (profile_ordBC (n := n) (f := e) he)]

end Classical

end FQ

end CFSG.LocalAnalysis.GLTheoremA

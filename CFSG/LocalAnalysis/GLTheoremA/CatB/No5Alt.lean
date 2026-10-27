module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.No5Arith
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char

public section

namespace CFSG.LocalAnalysis.GLTheoremA.No5

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator

theorem no5_alt {Y : Type} [Group Y] [Finite Y] (hY : IsSimpleGroup Y)
    (hnab : ∃ a b : Y, a * b ≠ b * a) {n : ℕ} (hn : 5 ≤ n) (e : Y ≃* alternatingGroup (Fin n))
    {y : Y} (hy : orderOf y = 5) {J : Subgroup Y} (hJ : GLAPComponent 5 (S8.cx y) J)
    (hcard : Nat.card (PSimple 5 J) = CFSG.Open.orderCo1) : False := by
  have hI : GLAPComponent 5 (fixSubgroup (MulAut.conj y)) J := by
    rw [fixSubgroup_conj_eq_cx]
    exact hJ
  obtain ⟨hI', hP⟩ := chevQ_transport Nat.prime_five e hI
  obtain ⟨eP⟩ := hP
  have hy5 : (MulAut.conj y) ^ 5 = 1 := by
    rw [← map_pow, show y ^ 5 = 1 by rw [← hy]; exact pow_orderOf_eq_one y, map_one]
  have hα5 : (MulAut.congr e (MulAut.conj y)) ^ 5 = 1 := by
    rw [← map_pow, hy5, map_one]
  have hα1 : MulAut.congr e (MulAut.conj y) ≠ 1 := fun h =>
    conj_ne_one_of_orderOf hY hnab hy ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨m, hm5, -, ⟨eA⟩⟩ :=
    kdAltDown_holds n 5 hn Nat.prime_five (by norm_num) _ hα5 hα1 _ hI'
  have hm5' : 5 ≤ m := le_trans (le_max_left 5 5) hm5
  have hc1 : Nat.card (PSimple 5 (J.map e.toMonoidHom)) = m.factorial / 2 := by
    rw [Nat.card_congr eA.toEquiv, YS08.L3Char.card_alt m (by omega)]
  have hc2 : Nat.card (PSimple 5 J) = Nat.card (PSimple 5 (J.map e.toMonoidHom)) :=
    Nat.card_congr eP.toEquiv
  exact factorial_half_ne_co1 hm5' (by rw [← hc1, ← hc2, hcard])

end CFSG.LocalAnalysis.GLTheoremA.No5

module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.Engine
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.E8FiveCopy

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem p_dvd_card_SL_of_orderOf_eq {K : Type} [Field K] [Finite K] {n p : ℕ} (hp : p.Prime)
    (hn : 2 ≤ n) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = n) :
    p ∣ Nat.card SL(n, K) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hqc : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  rw [hqc] at hord
  have hval := padicValNat_card_SL_of_orderOf_eq K hp hn hord
  have hdvd : p ∣ Fintype.card K ^ n - 1 := by
    have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
    exact (dvd_pow_sub_one_iff hq1 hord).2 dvd_rfl
  have hne : Fintype.card K ^ n - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (one_lt_pow₀ Fintype.one_lt_card (by omega))
  have hpos : 0 < padicValNat p (Fintype.card K ^ n - 1) := one_le_padicValNat_of_dvd hne hdvd
  rw [← hval] at hpos
  exact dvd_of_one_le_padicValNat hpos

section Layer


theorem layerDichotomy_adjointE8_five (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 < p) (hordq : orderOf ((Nat.card K : ℕ) : ZMod p) = 5) :
    LayerDichotomy p (adjointGroup .E8 K) := fun x hx =>
  (e8Five_centralizer_layer K hp hp7 hordq hx).imp_right fun ⟨hq, hcard⟩ =>
    ⟨hq, by
      rw [hcard]
      exact fun hc' => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc' dvd_rfl
        (p_dvd_card_SL_of_orderOf_eq hp (by norm_num) hordq))⟩

end Layer

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows

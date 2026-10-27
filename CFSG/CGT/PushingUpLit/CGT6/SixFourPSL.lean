module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourA8
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem eight_sl_not_psl_ge3 {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R)
    {n : ℕ} (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n)
    (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt) (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification) {m k : ℕ} (hm : 3 ≤ m)
    (hf : StatedClassicalModel (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T))
      StatedLieTag.PSL m 2 k) : False := by
  obtain ⟨hn2, -, -, hstd, hcardTh, -⟩ := eight_sl_ident h hn hnat hS h215 hL
  have hdvd := eight_sl_card_dvd h hn hnat hS h215 hL
  have hf' := hf
  obtain ⟨⟨-, hk, -⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := hf'
  have hT := (hstd.of_psl hm K hK e).1
  have hnk : n = k * (m - 1) := by
    have : 2 ^ n = 2 ^ (k * (m - 1)) := hcardTh.symm.trans hT
    exact Nat.pow_right_injective (le_refl 2) this
  by_cases hn3 : n = 3
  · have hmle : m - 1 ≤ 3 := by
      calc m - 1 = 1 * (m - 1) := (one_mul _).symm
        _ ≤ k * (m - 1) := Nat.mul_le_mul_right _ hk
        _ = 3 := by rw [← hnk, hn3]
    have hm4 : m = 4 ∧ k = 1 := by
      have h3 : k * (m - 1) = 3 := by rw [← hnk, hn3]
      have hm' : m = 3 ∨ m = 4 := by omega
      rcases hm' with rfl | rfl
      · exfalso; omega
      · exact ⟨rfl, by omega⟩
    obtain ⟨rfl, rfl⟩ := hm4
    exact eight_sl_not_psl_four_two h hn hnat hS h215 hL hf
  · obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega)
      (by omega)
    have hcardΛ : Nat.card (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) =
        CFSG.Open.ordA (m - 1) (2 ^ k) := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega), hK]
      unfold CFSG.Open.ordA
      have h1 : m - 1 + 1 = m := by omega
      rw [h1, mul_comm (m - 1) m]
    have hr2 : r ∣ Nat.card (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) := by
      refine (hr.dvd.trans ?_).trans hdvd
      have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
      rw [h2]
      exact Dvd.intro_left _ rfl
    rw [hcardΛ] at hr2
    have hprof := CFSG.Timmesfeld.Orders.profile_ordA (n := m - 1) (f := k) (by omega) hk
    have hz := (hprof.prim r (2 * n) hr (by omega)).mp hr2
    have hle := CFSG.Timmesfeld.Orders.zA_le (by omega : 0 < k) hz
    have h1 : k * (2 * (m - 1)) ≤ k * (m - 1 + 1) := by
      calc k * (2 * (m - 1)) = 2 * (k * (m - 1)) := by ring
        _ = 2 * n := by rw [hnk]
        _ ≤ k * (m - 1 + 1) := hle
    have h2 := Nat.le_of_mul_le_mul_left h1 (by omega)
    omega

end CFSG.CGT.PushingUpLit.CGT6

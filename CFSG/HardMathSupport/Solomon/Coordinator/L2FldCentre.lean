module

public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515CovTab
import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (griessHopfMultiplier GriessAllModelsStatement StatedProj StatedSL)
open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover

theorem l2fld_exceptionalOrders_psl2 (p f : ℕ) : exceptionalOrders .PSL 2 p f =
    (if p = 2 ∧ f = 2 then (2, 1) else if p = 3 ∧ f = 2 then (3, 1) else (1, 1)) := by
  unfold exceptionalOrders
  split_ifs <;> simp_all

theorem cov_three_dvd_table_L2 (p f : ℕ)
    (h : 3 ∣ Nat.card (generic .PSL 2 p f × exceptional .PSL 2 p f)) : p = 3 ∧ f = 2 := by
  have hg : genericOrders .PSL 2 p f = (Nat.gcd 2 (p ^ f - 1), 1) := by simp [genericOrders]
  have he := l2fld_exceptionalOrders_psl2 p f
  have hgpos : Nat.gcd 2 (p ^ f - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hexc : (exceptionalOrders .PSL 2 p f).1 ≠ 0 ∧ (exceptionalOrders .PSL 2 p f).2 ≠ 0 := by
    rw [he]
    split_ifs <;> simp
  have hc := lbi_card_gen_exc .PSL 2 p f (by rw [hg]; exact hgpos) (by rw [hg]; simp)
    hexc.1 hexc.2
  rw [hc, hg] at h
  simp only [mul_one] at h
  have hcop : Nat.Coprime 3 (Nat.gcd 2 (p ^ f - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 _) (by norm_num)
  have h' := hcop.dvd_of_dvd_mul_left h
  rw [he] at h'
  split_ifs at h' with h1 h2
  · exfalso; norm_num at h'
  · exact h2
  · exfalso; norm_num at h'

theorem l2CentreThree_of_griess (hG : GriessAllModelsStatement) : L2CentreThree := by
  intro Q _ _ hq h3 hZ F _ _ ⟨e⟩
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hchar, n, hp, hn⟩ := FiniteField.card' F
  have hcard : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  by_cases hsmall : Nat.card F ≤ 3
  · exfalso
    have hs := l2fld_isSolvable_psl2_of_card_le_three hsmall
    have hsQ : Group.IsSolvable (Q ⧸ Subgroup.center Q) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have hsolQ : Group.IsSolvable Q :=
      CFSG.Quasithin.isSolvable_of_ker_le_center (QuotientGroup.mk' (Subgroup.center Q))
        (by rw [QuotientGroup.ker_mk'])
    exact false_of_quasisimple_of_solvable hq hsolQ
  · push Not at hsmall
    have hadm : StatedLieAdmissible .PSL 2 p n :=
      ⟨hp, n.pos, le_rfl, fun h => by
        have := congrArg Prod.snd h; simp at this; omega, fun h => by
        have := congrArg Prod.snd h; simp at this; omega⟩
    have hLie : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .PSL 2 p n :=
      ⟨hadm, Or.inl ⟨hadm, F, inferInstance, inferInstance, hcard, ⟨e⟩⟩⟩
    obtain ⟨-, ⟨eH⟩⟩ := hG _ .PSL 2 p n hLie
    have hgpos : Nat.gcd 2 (p ^ (n : ℕ) - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
    have he := l2fld_exceptionalOrders_psl2 p n
    have : Finite (generic .PSL 2 p n × exceptional .PSL 2 p n) := by
      have h1 : NeZero (genericOrders .PSL 2 p n).1 := ⟨by simp [genericOrders, hgpos]⟩
      have h2 : NeZero (genericOrders .PSL 2 p n).2 := ⟨by simp [genericOrders]⟩
      have h3' : NeZero (exceptionalOrders .PSL 2 p n).1 := ⟨by rw [he]; split_ifs <;> simp⟩
      have h4' : NeZero (exceptionalOrders .PSL 2 p n).2 := ⟨by rw [he]; split_ifs <;> simp⟩
      unfold generic exceptional
      infer_instance
    have hd := cov_three_dvd_card hq h3 hZ eH
    obtain ⟨rfl, hn2⟩ := cov_three_dvd_table_L2 p n hd
    rw [hcard, hn2]
    norm_num

end CFSG.HardMathSupport.Solomon.Coordinator

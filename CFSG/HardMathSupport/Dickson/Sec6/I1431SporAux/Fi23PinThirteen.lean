module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.FixOrder13
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveSylow
public import Certificates.Certificate17403

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
  CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23PinNative
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

set_option maxRecDepth 20000

section Fi23


@[expose] noncomputable def y13Fi : CFSG.Sporadic.Fi23.J := wordG genG y13Letters

@[expose] noncomputable def g13Fi : CFSG.Sporadic.Fi23.J := wordG genG g13Letters

theorem rep_y13Fi : Rep 31671 (wordT 31671 (genTables orb) y13Letters) y13Fi :=
  Rep.wordT (by norm_num) y13Letters fun l _ => rep_gen l

theorem rep_g13Fi : Rep 31671 (wordT 31671 (genTables orb) g13Letters) g13Fi :=
  Rep.wordT (by norm_num) g13Letters fun l _ => rep_gen l

theorem fi23_pin_facts_of {TY TG : Table} {y g : CFSG.Sporadic.Fi23.J} (hY : Rep 31671 TY y) (hG : Rep 31671 TG g)
    (h1 : eqTab (powT 31671 13 TY) (idT 31671) = true) (h2 : eqTab TY (idT 31671) = false)
    (h3 : eqTab (compT 31671 TY TG) (compT 31671 TG (powT 31671 4 TY)) = true)
    (h4 : eqTab (compT 31671 (dTable orb) TY) (compT 31671 TY (dTable orb)) = true)
    (h5 : eqTab (powT 31671 2 (dTable orb)) (idT 31671) = true)
    (h6 : eqTab (dTable orb) (idT 31671) = false) :
    orderOf y = 13 ∧ y * g = g * y ^ 4 ∧ d * y = y * d ∧ orderOf d = 2 := by
  have hn : (31671 : ℕ) < 2 ^ 32 := by norm_num
  have h13 : y ^ 13 = 1 := eq_of_eqTab (hY.powT hn 13) (Rep.idT hn) h1
  have hne : y ≠ 1 := ne_one_of_rep hY h2
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hrel : y * g = g * y ^ 4 := eq_of_eqTab (hY.compT hG) (hG.compT (hY.powT hn 4)) h3
  have hcomm : d * y = y * d := eq_of_eqTab (rep_dTable.compT hY) (hY.compT rep_dTable) h4
  have hd2 : d ^ 2 = 1 := eq_of_eqTab (rep_dTable.powT hn 2) (Rep.idT hn) h5
  have hd1 : d ≠ 1 := ne_one_of_rep rep_dTable h6
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨orderOf_eq_prime h13 hne, hrel, hcomm, orderOf_eq_prime hd2 hd1⟩

theorem fi23_pin_facts :
    orderOf y13Fi = 13 ∧ y13Fi * g13Fi = g13Fi * y13Fi ^ 4 ∧ d * y13Fi = y13Fi * d ∧
      orderOf d = 2 := by
  have h := Certificates.certificate17403
  change fi23Pin13OK orb = true at h
  unfold fi23Pin13OK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact fi23_pin_facts_of rep_y13Fi rep_g13Fi h1 h2 h3 h4 h5 h6

theorem fi23_thirteen_card_J : 13 * Nat.card {h : CFSG.Sporadic.Fi23.J // orderOf h = 13} ≤ Nat.card CFSG.Sporadic.Fi23.J := by
  obtain ⟨ho, hrel, hcomm, hdo⟩ := fi23_pin_facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  have hH : ¬ 13 ^ 2 ∣ Nat.card J := by
    rw [card_J]
    norm_num
  refine thirteen_mul_card_orderOf_le_of_involution hH ho (g := (g13Fi)⁻¹) ?_ hdo hcomm
  calc (g13Fi)⁻¹ * y13Fi * ((g13Fi)⁻¹)⁻¹ = (g13Fi)⁻¹ * (y13Fi * g13Fi) := by group
    _ = (g13Fi)⁻¹ * (g13Fi * y13Fi ^ 4) := by rw [hrel]
    _ = y13Fi ^ 4 := by group

theorem fi23_thirteen_card :
    13 * Nat.card {h : NativeSporadic.Fi23 // orderOf h = 13} ≤ Nat.card NativeSporadic.Fi23 := by
  have h := fi23_thirteen_card_J
  have e1 := @card_orderOf_thirteen_congr NativeSporadic.Fi23 J _ _ fi23EquivJ
  have e2 := Nat.card_congr fi23EquivJ.toEquiv
  calc 13 * Nat.card {h : NativeSporadic.Fi23 // orderOf h = 13} =
        13 * Nat.card {h : J // orderOf h = 13} := by rw [e1]
    _ ≤ Nat.card J := h
    _ = Nat.card NativeSporadic.Fi23 := e2.symm

end Fi23

end CFSG.HardMathSupport.Dickson.Sec6.I1431

module

public import CFSG.Certificates.Kernel.Sp6Two.Sound
public import Certificates.Data.Kernel.Sp62X2K

public section

namespace CFSG.KC.Sp62X2

open CFSG.KD.Sp62 CFSG.KD.Sp6Two CFSG.KD.Sp62X2 CFSG.KC.Sp62 CFSG.KC.Sp6Two CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem x2Test {O0 O2 : Array (List ℕ)} {R : ℕ → ℕ} {o0 n0 hi0 o2 n2 hi2 : ℕ}
    (h0 : O0.size = n0)
    (hr0 : ∀ t < n0, canon6 (O0.getD t []) = true ∧ pk (O0.getD t []) = recX R o0 t)
    (h2 : O2.size = n2)
    (hr2 : ∀ t < n2, canon6 (O2.getD t []) = true ∧ pk (O2.getD t []) = recX R o2 t)
    (h : x2K R o0 n0 hi0 o2 n2 hi2 = true) (hm : n0 ≤ 64 * hi0) :
    (O0.all fun a => O0.all fun b =>
      !commutes6 a b || a == b || found O2 (indexMap O2) (mul6 a b)) = true := by
  rw [Array.all_eq_true]
  intro i hi
  rw [Array.all_eq_true]
  intro j hj
  have ei : O0[i] = O0.getD i [] := by simp [Array.getD, hi]
  have ej : O0[j] = O0.getD j [] := by simp [Array.getD, hj]
  rw [ei, ej]
  have hi' : i < n0 := h0 ▸ hi
  have hj' : j < n0 := h0 ▸ hj
  have ha := hr0 i hi'
  have hb := hr0 j hj'
  have hx := CFSG.KC.G2Three.allBelow_g2 (CFSG.KC.G2Three.allBelow_g2 h hm i hi') hm j hj'
  have mab := mulE ha hb
  have mba := mulE hb ha
  have ec : commutes6 (O0.getD i []) (O0.getD j []) =
      Nat.beq (MULF (recX R o0 i) (recX R o0 j)) (MULF (recX R o0 j) (recX R o0 i)) := by
    unfold commutes6
    rw [beq_pk mab.1 mba.1, mab.2, mba.2]
  have ee : (O0.getD i [] == O0.getD j []) = Nat.beq (recX R o0 i) (recX R o0 j) := by
    rw [beq_pk ha.1 hb.1, ha.2, hb.2]
  rw [ec, ee]
  unfold x2F at hx
  cases hc : Nat.beq (MULF (recX R o0 i) (recX R o0 j)) (MULF (recX R o0 j) (recX R o0 i)) <;>
    cases he : Nat.beq (recX R o0 i) (recX R o0 j) <;>
    simp only [Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or, Bool.or_true]
  rw [hc, he] at hx
  exact found_of_inTab h2 hr2 mab.1 (by rw [mab.2]; exact hx)

end CFSG.KC.Sp62X2

end

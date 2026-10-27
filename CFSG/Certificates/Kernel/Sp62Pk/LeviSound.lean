module

public import CFSG.Certificates.Kernel.Sp62Pk.Sound
public import Certificates.Data.Kernel.Sp62Levi
public import Certificates.Data.FF81Sp6Levi

public section

namespace CFSG.KC.Sp62

open CFSG.KD.Sp62 CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi

theorem any3_eq (f : ℕ → Bool) : (List.range 3).any f = any3 f := by
  have e : List.range 3 = [0, 1, 2] := rfl
  rw [e]
  simp only [List.any_cons, List.any_nil, Bool.or_false, any3]

theorem leviPred_eq (hz : ∀ i : Fin 3, canon6 (zCode i) = true) {y : List ℕ} {Y : ℕ}
    (hy : canon6 y = true ∧ pk y = Y) :
    leviPred y = leviF (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) Y := by
  have key : ∀ (i : Fin 3) (a b : ℕ), (mul6 y (zCode i) == mul6 (vecCode a b 0) y) =
      Nat.beq (MULF Y (pk (zCode i)))
        (MULF (VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) a b 0) Y) := by
    intro i a b
    have v := vecCode_pk hz a b 0
    rw [beq_pk (canon6_mul6 _ _) (canon6_mul6 _ _), pk_mul6 hy.1 (hz i), pk_mul6 v.1 hy.1, hy.2,
      v.2]
  unfold leviPred leviF leviZ
  simp only [any3_eq, key]

end CFSG.KC.Sp62

end

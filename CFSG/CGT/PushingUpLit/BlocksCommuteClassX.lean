module

public import CFSG.CGT.PushingUp.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp

theorem not_commutative_SL2 (F : Type) [Field F] :
    ¬ ∀ A B : Matrix.SpecialLinearGroup (Fin 2) F, A * B = B * A := by
  intro h
  let A : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let B : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have := congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) F =>
    (C : Matrix (Fin 2) (Fin 2) F) 0 0) (h A B)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  simp [A, B, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem prime_eq_three_of_two_mul_eq_factorial {n q : ℕ} (hn : 1 ≤ n) (hq : q.Prime)
    (hcard : 2 * q = (2 * n + 1).factorial) : q = 3 := by
  have h3 : 3 ∣ (2 * n + 1).factorial := Nat.dvd_factorial (by norm_num) (by omega)
  rw [← hcard] at h3
  have h4 : 3 ∣ q := Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 h4).symm

theorem card_top_eq_three_of_inClassX {L : Type} [Group L] [Finite L] (hL : InClassX L)
    (hp : (Nat.card (L ⧸ pCore 2 L)).Prime) : Nat.card (L ⧸ pCore 2 L) = 3 := by
  rcases hL.2 with ⟨n, hn, φ, -⟩ | ⟨n, hn, φ, -⟩
  · have hcard : Nat.card (L ⧸ pCore 2 L) = Nat.card (alternatingGroup (Fin (2 * n + 1))) :=
      Nat.card_congr φ.toEquiv
    rw [hcard] at hp ⊢
    have : Nontrivial (Fin (2 * n + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h2 : 2 * Nat.card (alternatingGroup (Fin (2 * n + 1))) = (2 * n + 1).factorial := by
      rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    exact prime_eq_three_of_two_mul_eq_factorial hn hp h2
  · exfalso
    have hcard : Nat.card (L ⧸ pCore 2 L) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      Nat.card_congr φ.toEquiv
    rw [hcard] at hp
    have : Fact (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))).Prime := ⟨hp⟩
    have hcyc : IsCyclic (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      isCyclic_of_prime_card rfl
    exact not_commutative_SL2 (GaloisField 2 n) fun A B => IsCyclic.commGroup.mul_comm A B

end CFSG.CGT.PushingUpLit

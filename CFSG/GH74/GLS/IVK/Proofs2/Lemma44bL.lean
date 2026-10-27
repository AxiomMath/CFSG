module

public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowSemidihedral
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowWreathed

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma44bL

open Matrix CFSG.DesarguesianPlanes CFSG.BrauerLinearThree CFSG.Wreathed CFSG.Wreathed.BrauerWong
  CFSG.Open

variable {F : Type} [Field F] [Finite F]

theorem exists_GL2_semidihedral (hq : Nat.card F % 4 = 3) {m : ℕ}
    (hm : (Nat.card F + 1).factorization 2 = m) :
    2 ≤ m ∧ ∃ M : Subgroup (GL (Fin 2) F), Nat.card M = 2 ^ (m + 2) ∧
      Nonempty (↥M ≃* SemidihedralGroup (m + 2)) := by
  subst hm
  obtain ⟨hm2, ⟨j, hj⟩, hdvd, -, -, -⟩ := semidihedral_arith hq
  obtain ⟨A, hAord, -, hAconj⟩ := exists_nonsplit_element hq hdvd
  have hAq : A ^ Nat.card F = A ^ (2 ^ (Nat.card F + 1).factorization 2 - 1) := by
    conv_lhs => rw [hj]
    rw [pow_add, pow_mul, ← hAord, pow_orderOf_eq_one, one_pow, one_mul]
  have hconj : diagGL 1 (-1) * A * (diagGL 1 (-1))⁻¹ =
      A ^ (2 ^ (Nat.card F + 1).factorization 2 - 1) := by
    rw [hAconj, hAq]
  have ht : (diagGL 1 (-1) : GL (Fin 2) F) ^ 2 = 1 := by
    rw [diagGL_pow, one_pow, neg_one_sq, diagGL_one_one]
  obtain ⟨hP, e, -, -⟩ := semidihedral_sup_zpowers hm2 hAord ht hconj
  exact ⟨hm2, Subgroup.zpowers A ⊔ Subgroup.zpowers (diagGL 1 (-1)), hP, ⟨e.symm⟩⟩

theorem exists_GL2_wreathed (hq : Nat.card F % 4 = 1) {k : ℕ}
    (hk : (Nat.card F - 1).factorization 2 = k) :
    2 ≤ k ∧ ∃ M : Subgroup (GL (Fin 2) F), Nat.card M = 2 ^ (2 * k + 1) ∧
      Nonempty (↥M ≃* WreathedTwoGroup k) := by
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hk2 : 2 ≤ k := hk ▸ (wreathed_arith hq hq1).1
  obtain ⟨α, hα⟩ := exists_orderOf_eq_two_pow_factorization (F := F)
  rw [hk] at hα
  let f := presentationHom (wreath_diagGL_left_pow hα) (wreath_diagGL_right_pow hα)
    wreath_swapGL_sq (wreath_diagGL_comm α) (wreath_swapGL_conj α)
  have hf : Function.Injective f := presentationHom_diagGL_injective hα
  refine ⟨hk2, f.range, ?_, ⟨(MonoidHom.ofInjective hf).symm⟩⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, card_wreath]
  ring

end Lemma44bL

end CFSG.GH74.GLS.IVK.Proofs2

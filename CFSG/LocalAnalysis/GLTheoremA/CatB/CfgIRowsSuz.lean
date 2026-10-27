module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgITriangular
public import CFSG.RankThree.PartTwo.Census.TripleCoverSuz
public import Certificates.Certificate10141

public section

set_option maxRecDepth 100000

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.RankThree.PartTwo.Sec4.Census CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz
open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz.Native
open CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.SuzFour.Native CFSG.Sporadic.Bridge

attribute [local irreducible] gen0 gen1 gen2 gen3 gen4 gen5 gen6

namespace SuzFour

section Certs


noncomputable def y4X : suzX := wordProd gplX wordY4

noncomputable def n4X : suzX := wordProd gplX wordN4

theorem repN_y4 : RepN nY4 ((y4X : suzX) : Equiv.Perm (Fin 1782)) := repN_wordX wordY4

theorem repN_n4 : RepN nN4 ((n4X : suzX) : Equiv.Perm (Fin 1782)) := repN_wordX wordN4

theorem ne_of_not_beq {a b : ℕ} (h : (!Nat.beq a b) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem cfg4_facts :
    comp nY4 (sqN nY4) = pid ∧ comp nY1 nY4 = comp nY4 nY1 ∧ comp nY2 nY4 = comp nY4 nY2 ∧
      comp nY3 nY4 = comp nY4 nY3 ∧ comp nN4 nY4 = comp (sqN nY4) nN4 ∧
      comp nN4 nY1 = comp nY1 nN4 ∧ comp nN4 nY2 = comp nY2 nN4 ∧
      comp nN4 nY3 = comp nY3 nN4 ∧ ent nY1 0 ≠ 0 ∧ ent nY2 0 ≠ 0 ∧ ent nY3 0 ≠ 0 ∧
      ent nY4 0 ≠ 0 := by
  have h := Certificates.certificate10141
  simp only [cfg4OK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  have k9 : ent nY1 0 ≠ 0 := by
    revert h9; generalize ent nY1 0 = k; intro hk
    first | exact Nat.ne_of_beq_eq_false hk | exact ne_of_not_beq hk
  have k10 : ent nY2 0 ≠ 0 := by
    revert h10; generalize ent nY2 0 = k; intro hk
    first | exact Nat.ne_of_beq_eq_false hk | exact ne_of_not_beq hk
  have k11 : ent nY3 0 ≠ 0 := by
    revert h11; generalize ent nY3 0 = k; intro hk
    first | exact Nat.ne_of_beq_eq_false hk | exact ne_of_not_beq hk
  have k12 : ent nY4 0 ≠ 0 := by
    revert h12; generalize ent nY4 0 = k; intro hk
    first | exact Nat.ne_of_beq_eq_false hk | exact ne_of_not_beq hk
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8, k9, k10, k11, k12⟩

theorem ne_one_of_repN {P : ℕ} {y : suzX} (hy : RepN P (y : Equiv.Perm (Fin 1782)))
    (h : ent P 0 ≠ 0) : y ≠ 1 := by
  rintro rfl
  apply h
  simpa using hy 0

noncomputable def xs : Fin 4 → suzX := ![y1X, y2X, y3X, y4X]

noncomputable def ns : Fin 4 → suzX := ![n1X, n2X, n3X, n4X]

theorem xs_pow : ∀ i, xs i ^ 3 = 1 := by
  intro i
  fin_cases i
  · exact y1X_pow
  · exact y2X_pow
  · exact y3X_pow
  · exact pow_three_of_comp repN_y4 cfg4_facts.1

theorem xs_ne_one : ∀ i, xs i ≠ 1 := by
  intro i
  fin_cases i
  · exact ne_one_of_repN repN_y1 cfg4_facts.2.2.2.2.2.2.2.2.1
  · exact ne_one_of_repN repN_y2 cfg4_facts.2.2.2.2.2.2.2.2.2.1
  · exact ne_one_of_repN repN_y3 cfg4_facts.2.2.2.2.2.2.2.2.2.2.1
  · exact ne_one_of_repN repN_y4 cfg4_facts.2.2.2.2.2.2.2.2.2.2.2

theorem y14_comm : y1X * y4X = y4X * y1X := mul_comm_of_comp repN_y1 repN_y4 cfg4_facts.2.1
theorem y24_comm : y2X * y4X = y4X * y2X := mul_comm_of_comp repN_y2 repN_y4 cfg4_facts.2.2.1
theorem y34_comm : y3X * y4X = y4X * y3X :=
  mul_comm_of_comp repN_y3 repN_y4 cfg4_facts.2.2.2.1

theorem xs_comm : ∀ i j, xs i * xs j = xs j * xs i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [xs, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    first
    | rfl
    | exact y12_comm | exact y12_comm.symm | exact y13_comm | exact y13_comm.symm
    | exact y23_comm | exact y23_comm.symm | exact y14_comm | exact y14_comm.symm
    | exact y24_comm | exact y24_comm.symm | exact y34_comm | exact y34_comm.symm

theorem n4_conj : n4X * y4X * n4X⁻¹ = y4X⁻¹ :=
  conj_eq_inv_of_comp repN_n4 repN_y4 cfg4_facts.2.2.2.2.1 (pow_three_of_comp repN_y4 cfg4_facts.1)

theorem n4_fix {y : suzX} {P : ℕ} (hy : RepN P (y : Equiv.Perm (Fin 1782)))
    (h : comp nN4 P = comp P nN4) : n4X * y * n4X⁻¹ = y := by
  rw [mul_comm_of_comp repN_n4 hy h, mul_inv_cancel_right]

theorem ns_inv : ∀ j, ns j * xs j * (ns j)⁻¹ = (xs j)⁻¹ := by
  intro j
  fin_cases j
  · exact n1_conj
  · exact n2_conj
  · exact n3_conj
  · exact n4_conj

theorem ns_fix : ∀ i j, i < j → ns j * xs i * (ns j)⁻¹ = xs i := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp only [xs, ns, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · exact n2_y1
  · exact n3_y1
  · exact n4_fix repN_y1 cfg4_facts.2.2.2.2.2.1
  · exact n3_y2
  · exact n4_fix repN_y2 cfg4_facts.2.2.2.2.2.2.1
  · exact n4_fix repN_y3 cfg4_facts.2.2.2.2.2.2.2.1

end Certs

end SuzFour

section Certs


theorem cfgIRank_co1_three : CfgIRankRow 3 S8.Row.co1 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  haveI hNat : IsSimpleGroup CFSG.Blueprint.NativeSporadic.Suz :=
    CFSG.Sporadic.Suz.isSimpleGroup_Suz
  haveI : IsSimpleGroup TauCeti.SporadicName.Suz.Group :=
    @MulEquiv.isSimpleGroup _ _ _ _ hNat b.symm
  obtain ⟨eX⟩ := nonempty_mulEquiv_suzX
  refine Triangular.cfgIRankRow_of_triangular' (M := suzX) ?_ rfl SuzFour.xs SuzFour.ns
    SuzFour.xs_pow SuzFour.xs_ne_one SuzFour.xs_comm SuzFour.ns_inv SuzFour.ns_fix
  intro i hi
  have hi' : i = TauCeti.CFSGIndex.sporadic .Suz := hi
  subst hi'
  exact ⟨eX⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

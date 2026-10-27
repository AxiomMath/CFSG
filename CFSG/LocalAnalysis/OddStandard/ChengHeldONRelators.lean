module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldDefs
public import CFSG.Sporadic.Recognition.PresentedWords
public import Certificates.Data.ChengHeldONRels

public section

namespace CFSG.OddStandard.ChengHeld.ONSylow

open CFSG.Sporadic.Recognition.PresentedWords

theorem one_of_eq_mul_inv {G : Type*} [Group G] {a b c : G} (h : b = c) (e : a = b * c⁻¹) :
    a = 1 := by
  rw [e, h, mul_inv_cancel]

theorem wprod_onRels {G : Type*} [Group G] {t pi tau mu lam ze xi z : G}
    (hf : Frame4 0 t pi tau mu lam ze xi) (hz2 : z * z = 1)
    (hz : Kind.unitary.Act 0 t pi tau mu lam ze xi z) :
    ∀ w ∈ onRels, wprod ![t, pi, tau, mu, lam, ze, xi, z] w = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := hf
  simp only [Kind.Act, ite_true] at hz
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hz
  simp only [cj, cm, pow_succ, pow_zero, one_mul, mul_zero] at *
  simp only [onRels, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  simp only [wprod, List.map, List.prod_cons, List.prod_nil, mul_one, ite_true,
    Bool.false_eq_true, ite_false, Matrix.cons_val]
  refine ⟨one_of_eq_mul_inv h1 (by group), one_of_eq_mul_inv h2 (by group),
    one_of_eq_mul_inv h3 (by group), one_of_eq_mul_inv h4 (by group),
    one_of_eq_mul_inv h5 (by group), one_of_eq_mul_inv h6 (by group),
    one_of_eq_mul_inv h7 (by group), one_of_eq_mul_inv h8 (by group),
    one_of_eq_mul_inv h9 (by group), one_of_eq_mul_inv h10 (by group),
    one_of_eq_mul_inv h11 (by group), one_of_eq_mul_inv h12 (by group),
    one_of_eq_mul_inv h13 (by group), one_of_eq_mul_inv h14 (by group),
    one_of_eq_mul_inv h15 (by group), one_of_eq_mul_inv h16 (by group),
    one_of_eq_mul_inv h17 (by group), one_of_eq_mul_inv h18 (by group),
    one_of_eq_mul_inv h19 (by group), one_of_eq_mul_inv h20 (by group),
    one_of_eq_mul_inv h21 (by group), one_of_eq_mul_inv h22 (by group),
    one_of_eq_mul_inv h23 (by group), one_of_eq_mul_inv h24 (by group),
    one_of_eq_mul_inv hz2 (by group), one_of_eq_mul_inv a1 (by group),
    one_of_eq_mul_inv a2 (by group), one_of_eq_mul_inv a3 (by group),
    one_of_eq_mul_inv a4 (by group), one_of_eq_mul_inv a5 (by group),
    one_of_eq_mul_inv a6 (by group), one_of_eq_mul_inv a7 (by group)⟩

end CFSG.OddStandard.ChengHeld.ONSylow

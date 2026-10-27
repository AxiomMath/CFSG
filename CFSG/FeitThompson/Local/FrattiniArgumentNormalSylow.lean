module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy

open Pointwise Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] {p : ℕ} {R P : Subgroup X}

theorem conj_smul_eq_map_conj (x : X) (P : Subgroup X) :
    MulAut.conj x • P = P.map (MulAut.conj x) := by
  rw [pointwise_smul_def]; rfl

theorem mem_normalizer_iff_conj_smul_eq {x : X} :
    x ∈ normalizer (P : Set X) ↔ MulAut.conj x • P = P := by
  rw [conj_smul_eq_map_conj, mem_normalizer_iff_map_conj_eq]

theorem mem_normalizer_iff_conj_inv_smul_eq {x : X} :
    x ∈ normalizer (P : Set X) ↔ MulAut.conj x⁻¹ • P = P := by
  rw [← mem_normalizer_iff_conj_smul_eq (P := P) (x := x⁻¹), Subgroup.inv_mem_iff]

theorem map_subtype_conj_smul (r : R) (K : Subgroup R) :
    (MulAut.conj r • K).map R.subtype = MulAut.conj (r : X) • K.map R.subtype := by
  simp only [conj_smul_eq_map_conj, map_map]
  congr 1

theorem conj_smul_le_of_normal [R.Normal] (x : X) (hPR : P ≤ R) : MulAut.conj x • P ≤ R := by
  rw [conj_smul_eq_map_conj]
  rintro y ⟨a, ha, rfl⟩
  exact ‹R.Normal›.conj_mem a (hPR ha) x

theorem natCard_subgroupOf_of_le (h : P ≤ R) : Nat.card (P.subgroupOf R) = Nat.card P :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

variable [Fact p.Prime] [R.Normal]

theorem exists_mem_normalizer_mul_mem [Finite X] (hPR : P ≤ R)
    (hP : Nat.card P = p ^ (Nat.card R).factorization p) (x : X) :
    ∃ n ∈ normalizer (P : Set X), ∃ r ∈ R, x = n * r := by
  set Q := MulAut.conj x⁻¹ • P with hQ
  have hQR : Q ≤ R := conj_smul_le_of_normal _ hPR
  have hQcard : Nat.card Q = p ^ (Nat.card R).factorization p := by
    rw [hQ, natCard_conj_smul, hP]
  obtain ⟨r, hr⟩ := exists_conj_smul_eq (G := R) (p := p)
    (P := Q.subgroupOf R) (Q := P.subgroupOf R)
    (by rw [natCard_subgroupOf_of_le hQR, hQcard])
    (by rw [natCard_subgroupOf_of_le hPR, hP])
  have key : MulAut.conj (r : X) • Q = P := by
    have := congrArg (fun K : Subgroup R => K.map R.subtype) hr
    simpa [map_subtype_conj_smul, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQR,
      inf_eq_left.2 hPR] using this
  have hmem : ((r : X) * x⁻¹) ∈ normalizer (P : Set X) := by
    rw [mem_normalizer_iff_conj_smul_eq, map_mul, mul_smul]
    exact key
  exact ⟨((r : X) * x⁻¹)⁻¹, Subgroup.inv_mem _ hmem, (r : X), r.2, by group⟩

theorem normalizer_sup_eq_top_of_normal [Finite X] (hPR : P ≤ R)
    (hP : Nat.card P = p ^ (Nat.card R).factorization p) :
    normalizer (P : Set X) ⊔ R = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨n, hn, r, hr, rfl⟩ := exists_mem_normalizer_mul_mem hPR hP x
  exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hr)

theorem sup_normalizer_eq_top_of_normal [Finite X] (hPR : P ≤ R)
    (hP : Nat.card P = p ^ (Nat.card R).factorization p) :
    R ⊔ normalizer (P : Set X) = ⊤ := by
  rw [sup_comm]; exact normalizer_sup_eq_top_of_normal hPR hP

theorem coe_normalizer_mul_coe_eq_univ [Finite X] (hPR : P ≤ R)
    (hP : Nat.card P = p ^ (Nat.card R).factorization p) :
    ((normalizer (P : Set X) : Subgroup X) : Set X) * (R : Set X) = Set.univ := by
  rw [← Subgroup.mul_normal (normalizer (P : Set X)) R,
    normalizer_sup_eq_top_of_normal hPR hP, Subgroup.coe_top]

theorem coe_mul_coe_normalizer_eq_univ [Finite X] (hPR : P ≤ R)
    (hP : Nat.card P = p ^ (Nat.card R).factorization p) :
    (R : Set X) * (normalizer (P : Set X) : Set X) = Set.univ := by
  rw [← Subgroup.normal_mul R (normalizer (P : Set X)),
    sup_normalizer_eq_top_of_normal hPR hP, Subgroup.coe_top]

theorem exists_mem_mul_mem_normalizer [Finite X] (hPR : P ≤ R)
    (hP : Nat.card P = p ^ (Nat.card R).factorization p) (x : X) :
    ∃ r ∈ R, ∃ n ∈ normalizer (P : Set X), x = r * n := by
  have hx : x ∈ (R : Set X) * (normalizer (P : Set X) : Set X) := by
    rw [coe_mul_coe_normalizer_eq_univ hPR hP]; trivial
  obtain ⟨r, hr, n, hn, hrn⟩ := hx
  exact ⟨r, hr, n, hn, hrn.symm⟩

end

end CFSG.FeitThompson

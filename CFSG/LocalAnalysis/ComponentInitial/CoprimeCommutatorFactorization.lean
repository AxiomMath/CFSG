module

public import CFSG.GroupTheory.SolvableHallNodes
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable (A : Type*) {Q : Type*} [Group A] [Group Q] [MulDistribMulAction A Q]

@[expose] def actionCommutator (H : Subgroup Q) : Subgroup Q :=
  closure {x | ∃ h ∈ H, ∃ a : A, x = h⁻¹ * (a • h)}

variable {A}

theorem gen_mem_actionCommutator {H : Subgroup Q} {h : Q} (hh : h ∈ H) (a : A) :
    h⁻¹ * (a • h) ∈ actionCommutator A H :=
  subset_closure ⟨h, hh, a, rfl⟩

theorem actionCommutator_top_normal : (actionCommutator A (⊤ : Subgroup Q)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : actionCommutator A (⊤ : Subgroup Q) ≤
      (actionCommutator A (⊤ : Subgroup Q)).comap (MulAut.conj g).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro _ ⟨q, -, a, rfl⟩
    change g * (q⁻¹ * (a • q)) * g⁻¹ ∈ actionCommutator A ⊤
    have h : g * (q⁻¹ * (a • q)) * g⁻¹ =
        ((q * g⁻¹)⁻¹ * (a • (q * g⁻¹))) * (g⁻¹⁻¹ * (a • g⁻¹))⁻¹ := by
      simp only [smul_mul', smul_inv']
      group
    rw [h]
    exact mul_mem (gen_mem_actionCommutator (mem_top _) a)
      (inv_mem (gen_mem_actionCommutator (mem_top _) a))
  exact hle hn

theorem smul_mem_actionCommutator_top {x : Q} (hx : x ∈ actionCommutator A (⊤ : Subgroup Q))
    (a : A) : a • x ∈ actionCommutator A (⊤ : Subgroup Q) := by
  have hle : actionCommutator A (⊤ : Subgroup Q) ≤
      (actionCommutator A (⊤ : Subgroup Q)).comap (MulDistribMulAction.toMonoidHom Q a) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨q, -, b, rfl⟩
    change a • (q⁻¹ * (b • q)) ∈ actionCommutator A ⊤
    have h : a • (q⁻¹ * (b • q)) = (a • q)⁻¹ * ((a * b * a⁻¹) • (a • q)) := by
      rw [smul_mul', smul_inv', ← mul_smul, ← mul_smul, inv_mul_cancel_right]
    rw [h]
    exact gen_mem_actionCommutator (mem_top _) _
  exact hle hx

theorem coprime_pgroup_commutator_factorization {p : ℕ} (hp : p.Prime) [Finite Q] [Finite A]
    (hQ : IsPGroup p Q) (hA : ¬ p ∣ Nat.card A) :
    (∀ q : Q, ∃ d ∈ actionCommutator A (⊤ : Subgroup Q),
      ∃ c ∈ CFSG.fixedPointSubgroup A Q, q = d * c) ∧
    actionCommutator A (actionCommutator A (⊤ : Subgroup Q)) =
      actionCommutator A (⊤ : Subgroup Q) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set D := actionCommutator A (⊤ : Subgroup Q) with hD
  have hDn : D.Normal := actionCommutator_top_normal
  have hDinv : CFSG.IsInvariant A Q D := ⟨fun a g => ⟨fun hg =>
    smul_mem_actionCommutator_top hg a, fun hg => by
      have := smul_mem_actionCommutator_top hg a⁻¹
      rwa [inv_smul_smul] at this⟩⟩
  have hDp : IsPGroup p D := hQ.to_subgroup D
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hDp
  have hcop : Nat.Coprime (Nat.card A) (Nat.card D) := by
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hA)))
  have hDsolv : Group.IsSolvable D := by
    have := IsPGroup.isNilpotent hDp
    infer_instance
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting D hDinv hDsolv hcop
  have hfac : ∀ q : Q, ∃ d ∈ D, ∃ c ∈ CFSG.fixedPointSubgroup A Q, q = d * c := by
    intro q
    let : MulDistribMulAction A (Q ⧸ D) :=
      CFSG.quotientMulDistribMulAction (A := A) (G := Q) D hDinv
    let : MulAction.QuotientAction A D := CFSG.quotientAction_of_isInvariant (A := A) D hDinv
    have hq : (q : Q ⧸ D) ∈ CFSG.fixedPointSubgroup A (Q ⧸ D) := by
      intro a
      rw [MulAction.Quotient.smul_coe (H := D) a q, QuotientGroup.eq]
      have h := gen_mem_actionCommutator (A := A) (mem_top q) a⁻¹
      have h' : (a • q)⁻¹ * q = a • (q⁻¹ * (a⁻¹ • q)) := by
        rw [smul_mul', smul_inv', smul_inv_smul]
      rw [h']
      exact smul_mem_actionCommutator_top h a
    rw [hlift] at hq
    obtain ⟨c, hc, hcq⟩ := hq
    have hcq' : c⁻¹ * q ∈ D := QuotientGroup.eq.1 hcq
    refine ⟨q * c⁻¹, ?_, c, hc, by rw [inv_mul_cancel_right]⟩
    have := hDn.conj_mem _ hcq' c
    rwa [mul_inv_cancel_left] at this
  refine ⟨hfac, le_antisymm ?_ ?_⟩
  · refine (closure_le _).2 ?_
    rintro _ ⟨d, -, a, rfl⟩
    exact gen_mem_actionCommutator (mem_top d) a
  · refine (closure_le _).2 ?_
    rintro _ ⟨q, -, a, rfl⟩
    obtain ⟨d, hd, c, hc, rfl⟩ := hfac q
    have hac : a • c = c := hc a
    have hdc : c⁻¹ * d * c ∈ D := by simpa using hDn.conj_mem d hd c⁻¹
    have h : (d * c)⁻¹ * (a • (d * c)) = (c⁻¹ * d * c)⁻¹ * (a • (c⁻¹ * d * c)) := by
      simp only [smul_mul', smul_inv', hac]
      group
    rw [h]
    exact gen_mem_actionCommutator hdc a

end CFSG.LocalAnalysis.ComponentInitial

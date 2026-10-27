module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization

public section

namespace CFSG.GroupTheory.SteinbergBK

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem minimal_coprime_pgroup_action_class_two {p : ℕ} [Fact p.Prime] {U Q : Type*} [Group U]
    [Group Q] [Finite U] [Finite Q] [MulDistribMulAction U Q] (hQ : IsPGroup p Q)
    (X : Subgroup U) [hXn : X.Normal] (hX : ¬ p ∣ Nat.card X)
    (hnc : ∃ x ∈ X, ∃ q : Q, x • q ≠ q)
    (hmin : ∀ R : Subgroup Q, R ≠ ⊤ → (∀ u : U, ∀ r ∈ R, u • r ∈ R) →
      ∀ x ∈ X, ∀ r ∈ R, x • r = r) :
    closure {g | ∃ q : Q, ∃ x ∈ X, g = q⁻¹ * (x • q)} = ⊤ ∧ commutator Q ≤ center Q := by
  set D := closure {g | ∃ q : Q, ∃ x ∈ X, g = q⁻¹ * (x • q)} with hDdef
  have hDinv : ∀ u : U, ∀ d ∈ D, u • d ∈ D := by
    intro u d hd
    have hle : D ≤ D.comap (MulDistribMulAction.toMonoidHom Q u) := by
      refine (closure_le _).mpr ?_
      rintro _ ⟨q, x, hx, rfl⟩
      change u • (q⁻¹ * (x • q)) ∈ D
      have h : u • (q⁻¹ * (x • q)) = (u • q)⁻¹ * ((u * x * u⁻¹) • (u • q)) := by
        rw [smul_mul', smul_inv', ← mul_smul, ← mul_smul, inv_mul_cancel_right]
      rw [h]
      exact subset_closure ⟨u • q, u * x * u⁻¹, hXn.conj_mem x hx u, rfl⟩
    exact hle hd
  let _ : MulDistribMulAction X Q := MulDistribMulAction.compHom Q X.subtype
  have hDact : actionCommutator X (⊤ : Subgroup Q) = D := by
    rw [hDdef, actionCommutator]
    congr 1
    ext g
    constructor
    · rintro ⟨q, -, x, rfl⟩
      exact ⟨q, x, x.2, rfl⟩
    · rintro ⟨q, x, hx, rfl⟩
      exact ⟨q, mem_top q, ⟨x, hx⟩, rfl⟩
  have hXp : ¬ p ∣ Nat.card X := hX
  have hfac := (coprime_pgroup_commutator_factorization (A := X) Fact.out hQ hXp).2
  rw [hDact] at hfac
  have hDtop : D = ⊤ := by
    by_contra hne
    have hcent := hmin D hne hDinv
    have hbot : actionCommutator X D = ⊥ := by
      rw [eq_bot_iff, actionCommutator]
      refine (closure_le _).mpr ?_
      rintro _ ⟨d, hd, x, rfl⟩
      change d⁻¹ * ((x : U) • d) ∈ (⊥ : Subgroup Q)
      rw [hcent x x.2 d hd, inv_mul_cancel]
      exact one_mem _
    rw [hbot] at hfac
    obtain ⟨x, hx, q, hxq⟩ := hnc
    have hmem : q⁻¹ * (x • q) ∈ D := subset_closure ⟨q, x, hx, rfl⟩
    rw [← hfac, mem_bot, inv_mul_eq_one] at hmem
    exact hxq hmem.symm
  refine ⟨hDtop, ?_⟩
  by_cases hQt : Subsingleton Q
  · intro c _
    rw [Subsingleton.elim c 1]
    exact one_mem _
  rw [not_subsingleton_iff_nontrivial] at hQt
  have : Group.IsSolvable Q := by
    have := hQ.isNilpotent
    infer_instance
  have hQ'ne : commutator Q ≠ ⊤ := (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Q)).ne
  have hQ'inv : ∀ u : U, ∀ r ∈ commutator Q, u • r ∈ commutator Q := by
    intro u r hr
    have hle : commutator Q ≤ (commutator Q).comap (MulDistribMulAction.toMonoidHom Q u) := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      change u • ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆
      rw [commutatorElement_def, smul_mul', smul_mul', smul_mul', smul_inv', smul_inv',
        ← commutatorElement_def]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    exact hle hr
  have hcent := hmin (commutator Q) hQ'ne hQ'inv
  intro c hc
  rw [mem_center_iff]
  have hle : D ≤ centralizer {c} := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨q, x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have hqc : q * c * q⁻¹ ∈ commutator Q := (commutator_normal ⊤ ⊤).conj_mem c hc q
    have h1 := hcent x hx _ hqc
    rw [smul_mul', smul_mul', smul_inv', hcent x hx c hc] at h1
    calc q⁻¹ * (x • q) * c = q⁻¹ * ((x • q) * c * (x • q)⁻¹) * (x • q) := by group
      _ = q⁻¹ * (q * c * q⁻¹) * (x • q) := by rw [h1]
      _ = c * (q⁻¹ * (x • q)) := by group
  intro g
  have hg : g ∈ centralizer {c} := hle (hDtop ▸ mem_top g)
  rw [mem_centralizer_singleton_iff] at hg
  exact hg

end CFSG.GroupTheory.SteinbergBK

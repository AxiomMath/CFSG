module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Tactic.Abel

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open scoped BigOperators

variable {U V : Type*} [Group U] [AddCommGroup V] [DistribMulAction U V]

@[expose] def coprimeCommutator (A : Subgroup U) (V : Type*) [AddCommGroup V]
    [DistribMulAction U V] : AddSubgroup V :=
  AddSubgroup.closure {x | ∃ a ∈ A, ∃ v : V, x = a • v - v}

@[expose] def coprimeFixed (A : Subgroup U) (V : Type*) [AddCommGroup V]
    [DistribMulAction U V] : AddSubgroup V where
  carrier := {v | ∀ a ∈ A, a • v = v}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun hv hw a ha => by rw [smul_add, hv a ha, hw a ha]
  neg_mem' := fun hv a ha => by rw [smul_neg, hv a ha]

theorem mem_coprimeFixed {A : Subgroup U} {v : V} : v ∈ coprimeFixed A V ↔ ∀ a ∈ A, a • v = v :=
  Iff.rfl

theorem nsmul_injective_of_coprime [Finite V] {m : ℕ} (hm : Nat.Coprime m (Nat.card V)) :
    Function.Injective fun v : V => m • v := by
  intro v w h
  have h' : m • (v - w) = 0 := by simp only [smul_sub] at *; rw [h, sub_self]
  have hdvd : addOrderOf (v - w) ∣ m := addOrderOf_dvd_of_nsmul_eq_zero h'
  have hdvd' : addOrderOf (v - w) ∣ Nat.card V := addOrderOf_dvd_natCard (v - w)
  have h1 : addOrderOf (v - w) = 1 := Nat.eq_one_of_dvd_coprimes hm hdvd hdvd'
  rw [AddMonoid.addOrderOf_eq_one_iff, sub_eq_zero] at h1
  exact h1

theorem abelian_coprime_fixed_commutator_decomposition [Finite V] (A : Subgroup U) [Finite A]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card V)) :
    IsCompl (coprimeCommutator A V) (coprimeFixed A V) ∧
      (A.Normal → ∀ u : U, (∀ x ∈ coprimeCommutator A V, u • x ∈ coprimeCommutator A V) ∧
        ∀ x ∈ coprimeFixed A V, u • x ∈ coprimeFixed A V) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  set m := Nat.card A with hm
  have hmcard : m = Fintype.card A := Nat.card_eq_fintype_card
  let σ : V →+ V :=
    { toFun := fun v => ∑ a : A, (a : U) • v
      map_zero' := by simp
      map_add' := fun v w => by simp [smul_add, Finset.sum_add_distrib] }
  have hσ : ∀ v, σ v = ∑ a : A, (a : U) • v := fun _ => rfl
  have hσfix : ∀ v, σ v ∈ coprimeFixed A V := by
    intro v b hb
    rw [hσ, Finset.smul_sum]
    exact (Fintype.sum_equiv (Equiv.mulLeft (⟨b, hb⟩ : A)) _ _ fun a => by
      simp [mul_smul])
  have hσD : ∀ x ∈ coprimeCommutator A V, σ x = 0 := by
    intro x hx
    refine AddSubgroup.closure_induction (p := fun x _ => σ x = 0) ?_ (map_zero σ)
      (fun x y _ _ hx hy => by rw [map_add, hx, hy, add_zero])
      (fun x _ hx => by rw [map_neg, hx, neg_zero]) hx
    rintro _ ⟨a, ha, v, rfl⟩
    rw [map_sub, sub_eq_zero, hσ, hσ]
    exact Fintype.sum_equiv (Equiv.mulRight (⟨a, ha⟩ : A)) _ _ fun b => by simp [mul_smul]
  have hσC : ∀ v ∈ coprimeFixed A V, σ v = m • v := by
    intro v hv
    rw [hσ, Finset.sum_congr rfl fun (a : A) _ => hv (a : U) a.2, Finset.sum_const,
      Finset.card_univ, hmcard]
  have hinj := nsmul_injective_of_coprime (V := V) hcop
  have hsurj : Function.Surjective fun v : V => m • v := Finite.surjective_of_injective hinj
  refine ⟨⟨?_, ?_⟩, fun hAn u => ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
  ·
    rw [disjoint_iff, eq_bot_iff]
    intro v hv
    obtain ⟨hvD, hvC⟩ := AddSubgroup.mem_inf.1 hv
    have h0 : m • v = m • (0 : V) := by rw [← hσC v hvC, hσD v hvD, smul_zero]
    exact (AddSubgroup.mem_bot).2 (hinj h0)
  ·
    rw [codisjoint_iff, eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := hsurj w
    have hdec : m • v = ∑ a : A, (v - (a : U) • v) + σ v := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← hmcard, hσ]
      abel
    change m • v ∈ _
    rw [hdec]
    refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (AddSubgroup.sum_mem _ fun a _ => ?_))
      (AddSubgroup.mem_sup_right (hσfix v))
    refine AddSubgroup.subset_closure ⟨a⁻¹, inv_mem a.2, (a : U) • v, ?_⟩
    rw [← mul_smul, inv_mul_cancel, one_smul]
  ·
    refine AddSubgroup.closure_induction (p := fun x _ => u • x ∈ coprimeCommutator A V) ?_
      (by rw [smul_zero]; exact AddSubgroup.zero_mem _)
      (fun x y _ _ hx hy => by rw [smul_add]; exact AddSubgroup.add_mem _ hx hy)
      (fun x _ hx => by rw [smul_neg]; exact AddSubgroup.neg_mem _ hx) hx
    rintro _ ⟨a, ha, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨u * a * u⁻¹, hAn.conj_mem a ha u, u • v, ?_⟩
    rw [smul_sub, ← mul_smul, ← mul_smul, inv_mul_cancel_right]
  ·
    intro a ha
    have h := hx (u⁻¹ * a * u) (by simpa using hAn.conj_mem a ha u⁻¹)
    calc a • u • x = u • ((u⁻¹ * a * u) • x) := by simp [mul_smul]
      _ = u • x := by rw [h]

end CFSG.LocalAnalysis.ComponentInitial

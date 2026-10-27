module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCData
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG Subgroup
open scoped MatrixGroups commutatorElement

theorem isQuasisimple_SL2_of_card {k : Type*} [Field k] (h4 : ∃ s : Finset k, s.card = 4) :
    CFSG.IsQuasisimple SL(2, k) := by
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := k) (n := 2) le_rfl (Or.inr h4)
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := k) (n := 2) le_rfl
    (Or.inr h4)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator SL(2, k) ≤ center SL(2, k) := by
    rw [commutator_def, commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (center SL(2, k))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [Group.isPerfect_def.mp hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne (SL(2, k) ⧸ center SL(2, k))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (mem_top _)))

theorem exists_finset_four {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    (hperf : Group.IsPerfect SL(2, k)) : ∃ s : Finset k, s.card = 4 := by
  have : Fintype k := Fintype.ofFinite k
  have hodd : Nat.card k % 2 = 1 := by
    obtain ⟨n, hp, hn⟩ := FiniteField.card k (ringChar k)
    rw [Nat.card_eq_fintype_card, hn]
    have hp2 : ringChar k % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hp with h | h
      · exact absurd h hk
      · exact h
    rw [Nat.pow_mod, hp2, one_pow]
    rfl
  have h1 : 1 < Nat.card k := Finite.one_lt_card
  have h3 : Nat.card k ≠ 3 := by
    intro h3
    have hsolv := C.isSolvable_SL_two_of_card_three h3
    have : Nontrivial SL(2, k) := by
      refine ⟨⟨1, -1, fun h => ?_⟩⟩
      have h00 := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
      simp at h00
      apply Ring.two_ne_zero hk
      linear_combination h00
    exact Group.IsPerfect.not_isSolvable (G := SL(2, k)) hsolv
  have h4 : 4 ≤ (Finset.univ : Finset k).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
  exact ⟨s, hs⟩

variable {X : Type} [Group X] [Finite X]

theorem map_pPrimeCore_le {Q : Subgroup X} (hQ : Q.IsSubnormal) :
    (pPrimeCore 2 Q).map Q.subtype ≤ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val ≠ 2} hQ
  rw [← pPrimeCore_eq_piCore, ← pPrimeCore_eq_piCore] at h
  rw [h]
  exact inf_le_right

theorem eq_top_of_normal {Q : Subgroup X} (hQ : IsPComponent 2 Q) {k : Type} [Field k]
    [Finite k] (hk : ringChar k ≠ 2) (e : Q ⧸ pPrimeCore 2 Q ≃* SL(2, k)) {N : Subgroup Q}
    (hN : N.Normal) {g : Q} (hg : g ∈ N) (hgc : e (QuotientGroup.mk g) ∉ center SL(2, k)) :
    N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect Q := CatalogueBAlternating.pComponent_perfect hQ
  have hSLperf : Group.IsPerfect SL(2, k) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 Q)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hqs := isQuasisimple_SL2_of_card (exists_finset_four hk hSLperf)
  set N' := (N.map (QuotientGroup.mk' (pPrimeCore 2 Q))).map e.toMonoidHom with hN'def
  have hN' : N'.Normal := (hN.map _ (QuotientGroup.mk'_surjective _)).map _ e.surjective
  have hgN' : e (QuotientGroup.mk g) ∈ N' := ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hqs hN' with h | h
  swap
  · exact absurd (h hgN') hgc
  have hsup : ∀ x : Q, ∃ n ∈ N, n⁻¹ * x ∈ pPrimeCore 2 Q := by
    intro x
    have hx : e (QuotientGroup.mk x) ∈ N' := h ▸ mem_top _
    obtain ⟨_, ⟨n, hn, rfl⟩, hnx⟩ := hx
    refine ⟨n, hn, ?_⟩
    have e1 : (QuotientGroup.mk n : Q ⧸ pPrimeCore 2 Q) = QuotientGroup.mk x := e.injective hnx
    exact QuotientGroup.eq.mp e1
  obtain ⟨K, hK, hQsub, hQK, hmin⟩ := hQ
  have hOle := map_pPrimeCore_le hQsub
  by_contra hNtop
  refine hmin (N.map Q.subtype) (lt_of_le_of_ne (map_subtype_le N) fun heq => hNtop ?_)
    (hN.isSubnormal.trans' hQsub) ?_
  · rw [eq_top_iff]
    intro x _
    have hx : (x : X) ∈ N.map Q.subtype := by rw [heq]; exact x.2
    obtain ⟨n, hn, hnx⟩ := hx
    have : n = x := Subtype.ext hnx
    rw [← this]
    exact hn
  · rw [← hQK]
    refine le_antisymm (map_mono (map_subtype_le N)) ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn, hnx⟩ := hsup ⟨x, hx⟩
    have hO : ((n⁻¹ * ⟨x, hx⟩ : Q) : X) ∈ pPrimeCore 2 X := hOle ⟨_, hnx, rfl⟩
    refine ⟨n, ⟨n, hn, rfl⟩, ?_⟩
    rw [← QuotientGroup.eq_one_iff] at hO
    have e2 : ((n⁻¹ * ⟨x, hx⟩ : Q) : X) = (n : X)⁻¹ * x := rfl
    rw [e2] at hO
    change (QuotientGroup.mk (n : X) : X ⧸ pPrimeCore 2 X) = QuotientGroup.mk x
    rw [QuotientGroup.eq]
    rwa [QuotientGroup.eq_one_iff] at hO

end CFSG.ComponentClassification.Burgoyne.DX

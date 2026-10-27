module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017Alt7Orb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017

open Equiv Equiv.Perm Finset

theorem card_order_five_alt7 {A : Type} [Group A] [Finite A] (e : A ≃* ↥(alternatingGroup (Fin 7))) :
    Nat.card {h : A // orderOf h = 5} = 504 := by
  classical
  have key : ∀ g : ↥(alternatingGroup (Fin 7)),
      orderOf g = 5 ↔ (g : Perm (Fin 7)).cycleType = {5} := by
    intro g
    rw [← Subgroup.orderOf_coe]
    constructor
    · intro h5
      apply cycleType_eq_five h5
      have := Finset.card_le_univ (g : Perm (Fin 7)).support
      simp only [Fintype.card_fin] at this
      omega
    · intro hc
      exact orderOf_eq_five_of_cycleType hc
  let F : {h : A // orderOf h = 5} → {σ : Perm (Fin 7) // σ.cycleType = {5}} := fun h =>
    ⟨((e h.1 : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)), (key _).1 (by
      rw [MulEquiv.orderOf_eq]; exact h.2)⟩
  have hF : Function.Bijective F := by
    constructor
    · intro h1 h2 heq
      have h12 : ((e h1.1 : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) =
          ((e h2.1 : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) :=
        congrArg (fun x : {σ : Perm (Fin 7) // σ.cycleType = {5}} => x.1) heq
      exact Subtype.ext (e.injective (Subtype.ext h12))
    · rintro ⟨σ, hσ⟩
      have hmem : σ ∈ alternatingGroup (Fin 7) := by
        rw [Equiv.Perm.mem_alternatingGroup, sign_of_cycleType, hσ]
        decide
      set g : ↥(alternatingGroup (Fin 7)) := ⟨σ, hmem⟩ with hg
      have hord : orderOf (e.symm g) = 5 := by
        rw [MulEquiv.orderOf_eq]
        exact (key g).2 hσ
      refine ⟨⟨e.symm g, hord⟩, ?_⟩
      apply Subtype.ext
      simp [F, hg]
  rw [Nat.card_congr (Equiv.ofBijective F hF), Nat.card_eq_fintype_card, Fintype.card_subtype,
    Equiv.Perm.card_of_cycleType_singleton (by norm_num) (by simp)]
  rfl

theorem even_card_of_fixedPointFree_involution {α : Type*} [Fintype α] (f : α → α)
    (hf : ∀ x, f (f x) = x) (hfix : ∀ x, f x ≠ x) : Even (Fintype.card α) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F' : Function.End α := f
  have hpow : F' ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    funext x
    exact hf x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hpow
  have hempty : Fintype.card (Function.fixedPoints F') = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun x => hfix x.1 x.2⟩
  rw [hempty] at hmod
  exact even_iff_two_dvd.2 ((Nat.modEq_zero_iff_dvd).1 hmod)

theorem i2017_exists_fixed_alt7 {n : ℕ} {s : Finset (Fin n)} (hs : #s = 8)
    {H : Subgroup ↥(alternatingGroup (Fin n))}
    (hHs : ∀ h ∈ H, ∀ i ∉ s, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) i = i)
    (hH : Nonempty (↥H ≃* ↥(alternatingGroup (Fin 7)))) :
    ∃ i ∈ s, ∀ h ∈ H, ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) i = i := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨e⟩ := hH
  obtain ⟨ω, hω⟩ : s.Nonempty := by
    rw [← Finset.card_pos, hs]
    norm_num
  set N5 : Finset ↥H := Finset.univ.filter (fun h => orderOf h = 5) with hN5
  have hN5card : #N5 = 504 := by
    rw [hN5, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, card_order_five_alt7 e]
  have hmem5 : ∀ h ∈ N5, orderOf h = 5 := fun h hh => (Finset.mem_filter.1 hh).2
  have hfix5 : ∀ h ∈ N5, #(s.filter (fun j => ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) j = j)) = 3 := by
    intro h hh
    have h5 := hmem5 h hh
    have hord : orderOf (((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n))) = 5 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact h5
    have hsupp : ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)).support ⊆ s := by
      intro i hi
      by_contra his
      exact (Equiv.Perm.mem_support.1 hi) (hHs h.1 h.2 i his)
    have hcard : ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)).support.card < 10 := by
      have := Finset.card_le_card hsupp
      omega
    exact card_fixed_of_cycleType_five hsupp (cycleType_eq_five hord hcard) hs
  have hdouble : ∑ h ∈ N5, #(s.filter (fun j => ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) j = j)) =
      ∑ j ∈ s, #(N5.filter (fun h : ↥H => ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) j = j)) := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hLHS : ∑ h ∈ N5, #(s.filter (fun j => ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) j = j)) =
      1512 := by
    rw [Finset.sum_congr rfl hfix5, Finset.sum_const, hN5card, smul_eq_mul]
  set c : ℕ := #(N5.filter (fun h : ↥H => ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) ω = ω)) with hc
  have hconst : ∀ j ∈ s,
      #(N5.filter (fun h : ↥H => ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) j = j)) = c := by
    intro j hj
    obtain ⟨g, hg, hgj⟩ := transitive_of_no_fixed hs hHs ⟨e⟩ hcon ω hω j hj
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥H, ((γ : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) ω = j :=
      ⟨⟨g, hg⟩, hgj⟩
    have hconj : ∀ z x : ↥H, orderOf (z * x * z⁻¹) = orderOf x := fun z x => by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    have hmemN5 : ∀ x : ↥H, x ∈ N5 ↔ orderOf x = 5 := fun x => by
      rw [hN5, Finset.mem_filter]
      simp
    have hmemN : ∀ z x : ↥H, x ∈ N5 → z * x * z⁻¹ ∈ N5 := fun z x hx => by
      rw [hmemN5, hconj]
      exact (hmemN5 x).1 hx
    rw [hc]
    apply Finset.card_nbij' (fun y : ↥H => γ⁻¹ * y * γ) (fun x : ↥H => γ * x * γ⁻¹)
    · intro y hy
      have hy' := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨?_, ?_⟩)
      · have := hmemN γ⁻¹ y hy'.1
        simpa using this
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
        rw [hγ, hy'.2, ← hγ]
        simp
    · intro x hx
      have hx' := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hmemN γ x hx'.1, ?_⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
      rw [← hγ]
      simp [hx'.2]
    · intro y _
      group
    · intro x _
      group
  have hsumc : ∑ j ∈ s, #(N5.filter (fun h : ↥H => ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) j = j))
      = 8 * c := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hs, smul_eq_mul]
  have hc189 : c = 189 := by omega
  set T : Finset ↥H := N5.filter (fun h : ↥H => ((h : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) ω = ω)
    with hT
  have hmemN5' : ∀ x : ↥H, x ∈ N5 ↔ orderOf x = 5 := fun x => by
    rw [hN5, Finset.mem_filter]
    simp
  have hinvT : ∀ x ∈ T, x⁻¹ ∈ T := by
    intro x hx
    obtain ⟨hxN, hxω⟩ := Finset.mem_filter.1 hx
    refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · rw [hmemN5', orderOf_inv]
      exact (hmemN5' x).1 hxN
    · simp only [Subgroup.coe_inv, Equiv.Perm.inv_eq_iff_eq]
      exact hxω.symm
  have hpar : Even (Fintype.card {x // x ∈ T}) := by
    refine even_card_of_fixedPointFree_involution
      (fun x : {x // x ∈ T} => (⟨x.1⁻¹, hinvT x.1 x.2⟩ : {x // x ∈ T})) ?_ ?_
    · intro x
      exact Subtype.ext (inv_inv x.1)
    · intro x hx
      have hx' : x.1⁻¹ = x.1 := congrArg Subtype.val hx
      have hsq : x.1 * x.1 = 1 := inv_eq_iff_mul_eq_one.1 hx'
      have hdvd : orderOf x.1 ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
      have h5 : orderOf x.1 = 5 := (hmemN5' x.1).1 (Finset.mem_filter.1 x.2).1
      rw [h5] at hdvd
      norm_num at hdvd
  have hcardT : Fintype.card {x // x ∈ T} = c := by
    rw [Fintype.card_coe]
  rw [hcardT, hc189] at hpar
  exact absurd hpar (by decide)

end CFSG.LocalAnalysis.GLTheoremA.I2017

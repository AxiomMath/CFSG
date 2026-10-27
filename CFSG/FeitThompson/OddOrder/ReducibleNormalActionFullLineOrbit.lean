module

import CFSG.FeitThompson.OddOrder.CliffordConjugateDirectSumBasis
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RepresentationTheory.Irreducible

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Representation Pointwise

variable {k X V : Type*} [Field k] [Group X] [AddCommGroup V] [Module k V]
  {ρ : Representation k X V}

theorem exists_simple_invtSubmodule_finrank_le [FiniteDimensional k V] {A : Subgroup X}
    {W : Submodule k V} (hW : W ∈ Representation.invtSubmodule (ρ.comp A.subtype)) (hW0 : W ≠ ⊥) :
    ∃ S : Submodule k V, S ≠ ⊥ ∧ S ∈ Representation.invtSubmodule (ρ.comp A.subtype) ∧
      finrank k S ≤ finrank k W ∧
      ∀ T ∈ Representation.invtSubmodule (ρ.comp A.subtype), T ≤ S → T = ⊥ ∨ T = S := by
  classical
  set 𝒮 : Set ℕ := {n | ∃ S : Submodule k V, S ≠ ⊥ ∧
      S ∈ Representation.invtSubmodule (ρ.comp A.subtype) ∧ finrank k S = n} with h𝒮
  have hne : finrank k W ∈ 𝒮 := ⟨W, hW0, hW, rfl⟩
  obtain ⟨S, hS0, hSinvt, hSrank⟩ := Nat.sInf_mem ⟨_, hne⟩
  refine ⟨S, hS0, hSinvt, ?_, ?_⟩
  · rw [hSrank]; exact Nat.sInf_le hne
  · intro T hT hTle
    rcases eq_or_ne T ⊥ with h | h
    · exact Or.inl h
    · refine Or.inr (Submodule.eq_of_le_of_finrank_le hTle ?_)
      rw [hSrank]
      exact Nat.sInf_le ⟨T, h, hT, rfl⟩

theorem map_rho_eq_self_of_mem_invtSubmodule [FiniteDimensional k V] {A : Subgroup X}
    {L : Submodule k V} (hL : L ∈ Representation.invtSubmodule (ρ.comp A.subtype))
    {a : X} (ha : a ∈ A) : L.map (ρ a) = L :=
  Submodule.eq_of_le_of_finrank_le ((mem_invtSubmodule_comp_subtype_iff ρ A).1 hL a ha)
    (le_of_eq (finrank_map_rho ρ a L).symm)

theorem exists_fin_map_rho_eq [FiniteDimensional k V] {A : Subgroup X} [A.Normal] {b : X} {q : ℕ}
    (hq : 0 < q) (hbq : b ^ q = 1) (hX : A ⊔ Subgroup.zpowers b = ⊤)
    {L : Submodule k V} (hL : L ∈ Representation.invtSubmodule (ρ.comp A.subtype)) (y : X) :
    ∃ j : Fin q, L.map (ρ y) = L.map (ρ (b ^ (j : ℕ))) := by
  have hy : y ∈ ((Subgroup.zpowers b : Subgroup X) : Set X) * ((A : Subgroup X) : Set X) := by
    rw [← Subgroup.mul_normal, sup_comm, hX]
    trivial
  rw [Set.mem_mul] at hy
  obtain ⟨u, hu, v, hv, huv⟩ := hy
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hu
  have hstep : L.map (ρ y) = L.map (ρ (b ^ m)) := by
    rw [← huv, ← hm, ← map_rho_map_rho ρ v (b ^ m) L,
      map_rho_eq_self_of_mem_invtSubmodule hL hv]
  refine ⟨⟨(m % (q : ℤ)).toNat, ?_⟩, ?_⟩
  · have h1 : 0 ≤ m % (q : ℤ) := Int.emod_nonneg m (by exact_mod_cast hq.ne')
    have h2 : m % (q : ℤ) < q := Int.emod_lt_of_pos m (by exact_mod_cast hq)
    omega
  · rw [hstep, zpow_eq_zpow_emod' m hbq]
    congr 1
    have h1 : 0 ≤ m % (q : ℤ) := Int.emod_nonneg m (by exact_mod_cast hq.ne')
    rw [← zpow_natCast b ((m % (q : ℤ)).toNat), Int.toNat_of_nonneg h1]

theorem exists_line_isInternal_zpow_of_reducible [FiniteDimensional k V] {q : ℕ} (hq : q.Prime)
    (hV : finrank k V = q) (hρ : ρ.IsIrreducible) {A : Subgroup X} [A.Normal] {b : X}
    (hb : orderOf b = q) (hX : A ⊔ Subgroup.zpowers b = ⊤)
    (hred : ∃ W : Submodule k V, W ∈ Representation.invtSubmodule (ρ.comp A.subtype) ∧
      W ≠ ⊥ ∧ W ≠ ⊤) :
    ∃ L : Submodule k V, L ∈ Representation.invtSubmodule (ρ.comp A.subtype) ∧ finrank k L = 1 ∧
      DirectSum.IsInternal (fun i : Fin q => L.map (ρ (b ^ (i : ℕ)))) ∧
      Function.Injective fun i : Fin q => L.map (ρ (b ^ (i : ℕ))) := by
  classical
  obtain ⟨W, hWinvt, hW0, hWtop⟩ := hred
  obtain ⟨L, hL0, hLinvt, hLW, hLsimple⟩ := exists_simple_invtSubmodule_finrank_le hWinvt hW0
  have hLlt : finrank k L < q := lt_of_le_of_lt hLW (by rw [← hV]; exact Submodule.finrank_lt hWtop)
  obtain ⟨t, x, hint, hrank⟩ := exists_conjugates_isInternal hρ hL0 hLinvt hLsimple
  have hL1 : finrank k L = 1 := by
    have hdvd : finrank k L ∣ q := ⟨t, by rw [← hV, hrank]; ring⟩
    rcases hq.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact h
    · omega
  have ht : t = q := by
    rw [hV, hL1, mul_one] at hrank
    omega
  set f : Fin q → Submodule k V := fun i => L.map (ρ (b ^ (i : ℕ))) with hf
  set e : Fin q ≃ Fin t := finCongr ht.symm with he
  set g : Fin q → Submodule k V := fun i => L.map (ρ (x (e i))) with hg
  have hgindep : iSupIndep g := hint.submodule_iSupIndep.comp e.injective
  have hgtop : ⨆ i, g i = ⊤ := by
    rw [hg, Equiv.iSup_comp (g := fun j => L.map (ρ (x j))) e]
    exact hint.submodule_iSup_eq_top
  have hginj : Function.Injective g := hgindep.injective fun i => map_rho_ne_bot ρ _ hL0
  have hbq : b ^ q = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hcover : ∀ i : Fin q, ∃ j : Fin q, f j = g i := by
    intro i
    obtain ⟨j, hj⟩ := exists_fin_map_rho_eq hq.pos hbq hX hLinvt (x (e i))
    exact ⟨j, hj.symm⟩
  choose ψ hψ using hcover
  have hψinj : Function.Injective ψ := by
    intro i i' h
    exact hginj (by rw [← hψ i, ← hψ i', h])
  have hψbij : Function.Bijective ψ := Finite.injective_iff_bijective.1 hψinj
  have hftop : ⨆ j, f j = ⊤ := by
    rw [← Equiv.iSup_comp (g := f) (Equiv.ofBijective ψ hψbij)]
    simpa [Equiv.ofBijective, hψ] using hgtop
  have hfindep : iSupIndep f := by
    refine iSupIndep.comp' (f := ψ) ?_ hψbij.2
    have hcomp : f ∘ ψ = g := funext hψ
    rw [hcomp]; exact hgindep
  exact ⟨L, hLinvt, hL1,
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hfindep hftop,
    hfindep.injective fun j => map_rho_ne_bot ρ _ hL0⟩

end CFSG.FeitThompson

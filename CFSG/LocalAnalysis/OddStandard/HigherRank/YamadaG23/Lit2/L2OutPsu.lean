module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OutPsuFix
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem l2out_psu_fixed {S : Type} [Group S] {p f : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hf : 1 ≤ f) (hq : 4 ≤ p ^ f) (hL : CFSG.Blueprint.LieModel S .PSU 4 p f) (α : MulAut S)
    (hα : α ^ 2 = 1) :
    ∃ Q : Subgroup S, Group.IsPerfect Q ∧ Even (Nat.card Q) ∧ ∀ s ∈ Q, α s = s := by
  classical
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) even_two
  obtain ⟨K, _, _, hcard, ⟨e₀⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (S ≃*
        Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 4 (p ^ f) K)) := by
    rcases hL with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hc.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  let e₁ : hypPSU h 2 0 ≃*
      Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 4 (p ^ f) K) :=
    hypPSUEquivStatedProj h hR₀ (by norm_num)
  let e : S ≃* hypPSU h 2 0 := e₀.trans e₁.symm
  let α' : MulAut (hypPSU h 2 0) := e.symm.trans (α.trans e)
  have haa : ∀ x : S, α (α x) = x := fun x => by
    rw [← MulAut.mul_apply, ← sq, hα]
    rfl
  have key : ∀ y, α' (e y) = e (α y) := by
    intro y
    simp only [α', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have key' : ∀ y, α (e.symm y) = e.symm (α' y) := by
    intro y
    refine e.injective ?_
    rw [e.apply_symm_apply]
    have h := key (e.symm y)
    rw [e.apply_symm_apply] at h
    exact h.symm
  have hα' : α' ^ 2 = 1 := by
    ext s
    obtain ⟨x, rfl⟩ := e.surjective s
    rw [sq, MulAut.mul_apply, key, key, haa]
    rfl
  obtain ⟨k, _, _, _, hk, ρ, heven, hfix⟩ :=
    l2out_exists_fixed_even_sl2_card (r := 2) (ε := 0) h hp2 (by norm_num) (by norm_num)
      (by norm_num) α' hα'
  have h4 : ∃ s : Finset k, s.card = 4 := by
    have := Fintype.ofFinite k
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset k)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  haveI := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  haveI : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  refine ⟨ρ.range.map e.symm.toMonoidHom, Group.IsPerfect.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact heven
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    change α (e.symm t) = e.symm t
    rw [key' t, hfix t ht]

end CFSG.OddStandard.HigherRank.YamadaG23

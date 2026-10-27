module

public import CFSG.ClassicalInvolution.Asc77.AscR10D3b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Uniform
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped MatrixGroups commutatorElement



section Linear

theorem stdDich3_psl {n : ℕ} (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL n 3 1) :
    StdDich3 .PSL n := by
  intro R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [GaloisField.card 3 1 (by norm_num)]; decide
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  obtain ⟨i₁, hi₁⟩ : R₁ ∈ longRootSet (K := GaloisField 3 1) hn :=
    fundamentalSubgroups_psl_subset hn (longestFundamental_subset .PSL _ hR₁)
  obtain ⟨i₂, hi₂⟩ : R₂ ∈ longRootSet (K := GaloisField 3 1) hn :=
    fundamentalSubgroups_psl_subset hn (longestFundamental_subset .PSL _ hR₂)
  have e₁ : c₁ = i₁ := (hi₁.isClassicalSL2 h2).eq_of_orderOf_eq_two hodd hc₁ ho₁
  have e₂ : c₂ = i₂ := (hi₂.isClassicalSL2 h2).eq_of_orderOf_eq_two hodd hc₂ ho₂
  subst e₁ e₂
  by_cases hn3 : 3 ≤ m + 1
  · by_cases hne : c₁ = c₂
    · exact Or.inl (by rw [hi₁.eq_longRootGroup h2, hi₂.eq_longRootGroup h2, hne])
    · rcases commute_or_linearBlockStandardPair h2 hn3 hi₁ hi₂ hc hne with h | ⟨-, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨_, h⟩))
  · obtain rfl : m = 1 := by omega
    have k₁ := longRootSet_two_subset (F := GaloisField 3 1) hn ⟨_, hi₁⟩
    have k₂ := longRootSet_two_subset (F := GaloisField 3 1) hn ⟨_, hi₂⟩
    exact Or.inl ((Set.mem_singleton_iff.mp k₁).trans (Set.mem_singleton_iff.mp k₂).symm)

end Linear


section Unitary

private theorem map_equiv_symm_map' {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    (R : Subgroup G) : (R.map φ.toMonoidHom).map φ.symm.toMonoidHom = R := by
  rw [Subgroup.map_map]
  have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem stdDich3_psu {n : ℕ} (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU n 3 1) :
    StdDich3 .PSU n := by
  intro R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hn : 2 ≤ n := by omega
  have hF : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := card_galoisField_two_mul 3 1 le_rfl
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  obtain ⟨i₁, hi₁⟩ : R₁.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField 3 2) (p := 3)
      (f := 1) hn := (hφ R₁).mp (longestFundamental_subset .PSU _ hR₁)
  obtain ⟨i₂, hi₂⟩ : R₂.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField 3 2) (p := 3)
      (f := 1) hn := (hφ R₂).mp (longestFundamental_subset .PSU _ hR₂)
  have e₁ : φ c₁ = i₁ := hi₁.eq_of_orderOf_eq_two hF hp2 ⟨c₁, hc₁, rfl⟩
    (by rw [MulEquiv.orderOf_eq]; exact ho₁)
  have e₂ : φ c₂ = i₂ := hi₂.eq_of_orderOf_eq_two hF hp2 ⟨c₂, hc₂, rfl⟩
    (by rw [MulEquiv.orderOf_eq]; exact ho₂)
  have hcφ : Commute i₁ i₂ := by
    show i₁ * i₂ = i₂ * i₁
    rw [← e₁, ← e₂, ← map_mul, ← map_mul, hc]
  by_cases hne : i₁ = i₂
  · left
    have h12 : R₁.map φ.toMonoidHom = R₂.map φ.toMonoidHom := by
      rw [hi₁.eq_longRootGroupSU (two_ne_zero_of_charP_ne_two hp2),
        hi₂.eq_longRootGroupSU (two_ne_zero_of_charP_ne_two hp2), hne]
    exact Subgroup.map_injective φ.injective h12
  · rcases commute_or_unitaryBlockStandardPair hF hp2 hn3 hi₁ hi₂ hcφ hne with h | ⟨-, h⟩
    · refine Or.inr (Or.inl fun x hx y hy => φ.injective ?_)
      rw [map_mul, map_mul]
      exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    · have h' := unitaryBlockStandardPair_map h φ.symm.toMonoidHom φ.symm.injective
      rw [map_equiv_symm_map', map_equiv_symm_map'] at h'
      exact Or.inr (Or.inr (Or.inr ⟨_, h'⟩))

end Unitary

section Symplectic

open CFSG.ClassicalInvolution.Models.SymplecticPairs (IsHyperbolicPlane planeGroup IsLongRootSp2
  exists_isLongRootSp2_iff)

theorem stdDich3_psp {n : ℕ} (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSp n 3 1) :
    StdDich3 .PSp n := by
  intro R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [GaloisField.card 3 1 (by norm_num)]; decide
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hmem : ∀ R ∈ longestFundamental (Generic.modelUniv .PSp n 3 1 Nat.prime_three).D,
      ∃ P, IsHyperbolicPlane P ∧ R = planeGroup P := fun R hR => by
    have := longestFundamental_subset .PSp _ hR
    rw [fundamentalSubgroups_psp_eq hadm] at this
    exact this
  obtain ⟨P₁, hP₁, rfl⟩ := hmem R₁ hR₁
  obtain ⟨P₂, hP₂, rfl⟩ := hmem R₂ hR₂
  obtain ⟨i₁, hi₁⟩ := (exists_isLongRootSp2_iff h2 _).mpr ⟨P₁, hP₁, rfl⟩
  obtain ⟨i₂, hi₂⟩ := (exists_isLongRootSp2_iff h2 _).mpr ⟨P₂, hP₂, rfl⟩
  have e₁ : c₁ = i₁ := hi₁.eq_of_orderOf_eq_two h2 hc₁ ho₁
  have e₂ : c₂ = i₂ := hi₂.eq_of_orderOf_eq_two h2 hc₂ ho₂
  subst e₁ e₂
  by_cases hne : c₁ = c₂
  · exact Or.inl (by rw [hi₁.eq_longRootGroup h2, hi₂.eq_longRootGroup h2, hne])
  · exact Or.inr (Or.inl (hi₁.commute_of_commute h2 hi₂ hc hne))

end Symplectic

end CFSG.ClassicalInvolution.Asc77.T3CII

module

public import CFSG.LargeExtraspecial.AS35QDefs
public import CFSG.LargeExtraspecial.AS35VStand
public import CFSG.LargeExtraspecial.AS35VCard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35V

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem pbarFacts_of_asc512 (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (hg : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) :
    PbarFacts S (S.ρ ⟨_, htM⟩) (S.PbarAsc g) := by
  obtain ⟨hmem, hext, hcard, hcent, hnorm, hcomm, hfix⟩ := hP G S hS g hg htM
  exact ⟨(S.fiveOne_two hS.sixFour hS.weak hg htM).1, map_le_range _ _, hmem, hext, hcard, hcent,
    hnorm, hcomm, hfix⟩

theorem pbarSupply_of_asc512 (hP : S14.Asc512PbarStmt) (h58 : S14.Asc512FiveEightStmt)
    (hS : S.SixHyp) : PbarSupply S := by
  rintro σ ⟨t, htD, ht, rfl⟩
  obtain ⟨g, rfl, -⟩ := htD.1
  exact ⟨S.PbarAsc g, pbarFacts_of_asc512 hP hS htD ht, h58 G S hS g htD ht⟩

end AS35V

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem fiveEleven_one (hP : S14.Asc512PbarStmt) (h58 : S14.Asc512FiveEightStmt)
    (hS : S.SixHyp) {g : G} (hg : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M)
    {X : Subgroup S.O} (hXM : X ≤ S.Mbar) (hX3 : IsPGroup 3 X)
    (hPX : ∀ p ∈ S.PbarAsc g, ∀ x ∈ X, p * x * p⁻¹ ∈ X)
    (htX : ∃ x ∈ X, S.ρ ⟨_, htM⟩ * x ≠ x * S.ρ ⟨_, htM⟩) :
    S.width = 3 ∧ Nat.card X = 27 ∧ (∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a) ∧
      Nat.card (X ⊓ centralizer ({S.ρ ⟨_, htM⟩} : Set S.O) : Subgroup S.O) = 3 := by
  have hPf := AS35V.pbarFacts_of_asc512 hP hS hg htM
  obtain ⟨hw, hC⟩ := hPf.fiveEleven (h58 G S hS g hg htM) hXM hX3 hPX htX
  obtain ⟨h27, hnab⟩ := hPf.fiveEleven_card (h58 G S hS g hg htM) hXM hX3 hPX htX
  exact ⟨le_antisymm hw hS.three_le_width, h27, hnab, hC⟩

end Setting

namespace S14

theorem asc512DichotomyStmt_of (hP : Asc512PbarStmt) (h58 : Asc512FiveEightStmt) :
    Asc512DichotomyStmt := by
  intro G _ _ S hS
  have hsup := AS35V.pbarSupply_of_asc512 hP h58 hS
  have hRI := rootInvolutionComponentsInput
  rcases AS35V.fitting_le_center_or hS hsup with hF | ⟨hw, X, hXM, hMX, hX3, t, htD, ht, x,
      hx, hne⟩
  · exact Or.inl ⟨fun m hm x hx => AS35V.conj_mem_closure_DbarAsc hm hx,
      AS35V.standing_conj hS hRI hsup, AS35V.standing_fstar_card hS hsup, hF⟩
  · exact Or.inr ⟨hw, X, hXM, hMX, hX3, t, htD, ht, x, hx, hne⟩

end S14

end CFSG.LargeExtraspecial

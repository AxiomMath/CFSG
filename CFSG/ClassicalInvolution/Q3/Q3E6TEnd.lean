module

public import CFSG.ClassicalInvolution.Q3.Q3E6TBase
public import CFSG.ClassicalInvolution.Q3.Q3TWCollCert
public import CFSG.ClassicalInvolution.Q3.Q3URChain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TW CFSG.ClassicalInvolution.Phan

set_option linter.unusedSectionVars false

section Obstruction

variable {G : Type} [Group G] [Finite G]

@[expose] def UEndObstruction3 (K : Subgroup G) (z : G) : Prop :=
  ∃ (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) (β : Subgroup G), β ∈ conjClass3 K ∧
    (∃ wβ : G, IsClassicalMember3 β wβ) ∧ ¬ Commutes K β ∧
    (∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K β) ∧
    ¬ Commutes β (nd.j 0) ∧
    (∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W β (nd.j 0)) ∧
    Commutes β (nd.j 4) ∧ (∀ a, 1 ≤ a → a ≤ 2 → Commutes β (nd.j a)) ∧
    ¬ Commutes β (nd.j 3)

variable [IsSimpleGroup G]

theorem phanChain3U_five_or_obstruction (h3 : OddThreeFreeInput) {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 1 (CompData.model .PSU 6) (conjClass3 K) z) :
    PhanChain3U K 5 ∨ UEndObstruction3 K z := by
  classical
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨hex, hP1⟩ := hR.setup
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictU (by norm_num : 2 ≤ 5) hR.inClass hK hR.cls hshape
  let c : UCtx3 5 (conjClass3 K) K z :=
    { hm := by norm_num, hΩ := hR.inClass, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1,
      hO3 := h3 G K z hR, d := d, hlift := Or.inl (by norm_num) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  by_cases hend : ∀ β : Subgroup G, β ∈ conjClass3 K → ∀ wβ : G, IsClassicalMember3 β wβ →
      ¬ Commutes K β → (∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K β) →
      ¬ Commutes β (nd.j 0) →
      (∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W β (nd.j 0)) →
      Commutes β (nd.j (5 - 1)) → (∀ a, 1 ≤ a → a ≤ 5 - 3 → Commutes β (nd.j a)) →
      Commutes β (nd.j (5 - 2))
  · exact Or.inl (c.phanChain3U_of_end nd (by norm_num) noCover_su4_three hend)
  · push Not at hend
    obtain ⟨β, hβ, wβ, hwβ, hnK, hpK, hn0, hp0, hlast, hmid, hnot⟩ := hend
    exact Or.inr ⟨c, nd, β, hβ, ⟨wβ, hwβ⟩, hnK, hpK, hn0, hp0, hlast, hmid, hnot⟩

end Obstruction

@[expose] def EndObstructionData3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .PSU 6) (conjClass3 K) z →
      UEndObstruction3 K z → HasTE6Data K z

theorem endDichotomy3UCT_of_obstruction (h3 : OddThreeFreeInput) (hobs : EndObstructionData3) :
    EndDichotomy3UCT := by
  intro G _ _ _ hnab K z hR hshape
  rcases phanChain3U_five_or_obstruction h3 hR hshape with hA | hE
  · exact Or.inl hA
  · exact Or.inr (hobs G hnab K z hR hshape hE)

theorem piece3SU6_of_obstruction (h3 : OddThreeFreeInput) (hP : Phan3Rec)
    (hC : TD4Collapse) (hobs : EndObstructionData3) : Piece3SU6 :=
  piece3SU6_of_inputs_ct h3 hP hC (endDichotomy3UCT_of_obstruction h3 hobs)

theorem piece3SU6_of_obstruction_proved (h3 : OddThreeFreeInput) (hP : Phan3Rec)
    (hobs : EndObstructionData3) : Piece3SU6 :=
  piece3SU6_of_obstruction h3 hP td4Collapse_proved hobs

end CFSG.ClassicalInvolution.Q3.Q3E6T

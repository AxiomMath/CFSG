module

public import CFSG.ClassicalInvolution.Q3.Q3E6TChain
public import CFSG.ClassicalInvolution.Q3.Q3URRows

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TW

set_option linter.unusedSectionVars false


@[expose] def HasTE6Data {G : Type} [Group G] (K : Subgroup G) (z : G) : Prop :=
  ∃ V : Fin 3 → Subgroup G, IsTE6Base 3 1 le_rfl (conjClass3 K) K z V ∧
    TE6Partner 3 1 (conjClass3 K) V

section Recognition

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem routeD3_twistedE6_of_base (hnab : ∃ x y : G, x * y ≠ y * x) (hC : TD4Collapse)
    {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : RouteD.DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember3 K z) {V : Fin 3 → Subgroup G}
    (hV : IsTE6Base 3 1 le_rfl Ω K z V) (hpartner : TE6Partner 3 1 Ω V) :
    CFSG.Blueprint.OddLieType G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨β, hβ, h01, h1, h2⟩ := hpartner
  exact routeD3_twistedE6_of_chain hnab hC hΩ hK hsingle hconn hz
    (U := ![β, V 0, V 1, V 2]) (hV.isTE6Chain h01 h1 h2) hβ hV.cover

theorem piece3SU6E6_of_te6Data (hC : TD4Collapse) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (K : Subgroup G) (z : G)
    (hR : RouteD3Setup K z) (hdata : HasTE6Data K z) : CFSG.Blueprint.OddLieType G := by
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨V, hV, hp⟩ := hdata
  exact routeD3_twistedE6_of_base hnab hC hR.inClass hK hsingle hconn hR.cls hV hp

end Recognition

@[expose] def EndDichotomy3UCT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .PSU 6) (conjClass3 K) z →
      PhanChain3U K 5 ∨ HasTE6Data K z

theorem piece3SU6_of_inputs_ct (h3 : OddThreeFreeInput) (hP : Phan3Rec) (hC : TD4Collapse)
    (hd : EndDichotomy3UCT) : Piece3SU6 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  rcases hd G hnab K z hR hshape with hA | hE
  · exact Or.inl (oddLieType_of_phanChain3U h3 hP (m := 5) (by norm_num) hnab hR hshape hA)
  · exact Or.inl (piece3SU6E6_of_te6Data hC G hnab K z hR hE)

end CFSG.ClassicalInvolution.Q3.Q3E6T

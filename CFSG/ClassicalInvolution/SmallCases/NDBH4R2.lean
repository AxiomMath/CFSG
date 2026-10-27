module

public import CFSG.ClassicalInvolution.SmallCases.NDBH4R1
public import CFSG.ClassicalInvolution.SmallCases.NDBH3T1
public import CFSG.ClassicalInvolution.Asc77.WP3TWXExotic

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

namespace NDBH4

theorem false_of_g2d4_twin {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hT : HasTwin p f K z) {a : ℕ} {tY : StatedLieTag} {nY : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ 2)
    (htY : tY = .G2 ∨ tY = .trialityD4) (hshape : LocalShapeT p f a tY nY (𝒞 K) z) : False := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · have h5 := S.five
      subst h
      simp at h5
    · exact h
  have hΩ : InClass p f (𝒞 K) := S.inClass
  have hconn : DConnected (𝒞 K) :=
    dConnected_of_omegaConnected (BootRank3.omegaConnected_of_routeD S.conn)
  have hdata : BootData p f (𝒞 K) :=
    G2D4Models.bootData_of_localShapeT_g2d4 S.odd hΩ S.p1 ha1 htY hshape
  have htrans : ∀ L ∈ 𝒞 K, ∀ T ∈ 𝒞 K, ∃ g : G, T = conjSub g L := by
    intro L hL T hT
    obtain ⟨g₁, hg₁⟩ := single_class K L hL
    obtain ⟨g₂, hg₂⟩ := single_class K T hT
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    rw [hg₁, hg₂, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hE := TWR.exotic_ctx S.odd hf hΩ S.cls S.p1 ha htY hshape
  have hnt : ¬ IndepTriple p f (𝒞 K) := TWR.not_indepTriple_of_exotic S.odd hf hΩ S.exact htrans hE
  have hBS : Asc77.BSC.BootSetting p f K z :=
    ⟨hnab, S.odd, S.five, S.cls, S.below, hconn, hdata, hnt⟩
  obtain ⟨D, -, i₁, ht, -, -⟩ := hshape
  have key : ∀ S₁ S₂ : Set (Subgroup G), S₁ = S₂ →
      (∃ D : LieSystemData p f (↥(⨆ L ∈ S₁, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₁, L))
        (oddQuotientFamily (restrictFamily S₁ (⨆ L ∈ S₁, L))),
          ∃ i, D.tag i = .G2 ∨ D.tag i = .trialityD4) →
      ∃ D : LieSystemData p f (↥(⨆ L ∈ S₂, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₂, L))
        (oddQuotientFamily (restrictFamily S₂ (⨆ L ∈ S₂, L))),
          ∃ i, D.tag i = .G2 ∨ D.tag i = .trialityD4 := by
    intro S₁ S₂ h
    subst h
    exact id
  have hS : centralizingMembers (exactFamily (𝒞 K) z) {z} = centralizingMembers (𝒞 K) {z} :=
    (centMembers_exactFamily (𝒞 K) z).trans
      (exactFamily_eq_centMembers_of_exact S.exact hΩ.classical)
  obtain ⟨D', i', hi'⟩ : ∃ D' : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, ∃ i,
      D'.tag i = .G2 ∨ D'.tag i = .trialityD4 :=
    key _ _ hS.symm ⟨D, i₁, by rw [ht]; exact htY⟩
  exact bootNoG2D4Twin_proved G K z hBS hT D' i' hi'

end NDBH4

theorem rowExoticG2D4Small_of (hR : G2D4SingleNoTwin p f) :
    RowPiece p f ShapeExoticG2D4Small := by
  intro a t n hs G _ _ _ hnab K z S hshape
  exfalso
  have ha1 : 1 ≤ a := hs.1.1.1
  have ha2 : a ≤ 2 := hs.2
  have htY : t = .G2 ∨ t = .trialityD4 := hs.1.2
  by_cases hT : HasTwin p f K z
  · exact NDBH4.false_of_g2d4_twin hnab S hT ha1 ha2 htY hshape
  · rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha
    · exact hR G hnab K z S hT t n htY hshape
    · exact NDBH4.false_of_g2d4_noTwin S hT htY ha hshape

end CFSG.ClassicalInvolution.NDB

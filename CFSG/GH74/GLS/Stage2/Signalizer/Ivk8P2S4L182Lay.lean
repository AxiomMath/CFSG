module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Basic
public import CFSG.GH74.GLS.Stage2.Local.P34Perf
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSecG
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31Two
public import CFSG.GH74.Uniqueness.SU.SU0GH
public import CFSG.LocalAnalysis.ComponentInitial.PerfectNormalizerLayer
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Closed
public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41
public import CFSG.GH74.KGH
public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Comps

variable {G : Type} [Group G] [Finite G]

theorem comps_le_two (hL : Lemma31Narrow) {z : G} {k : Kind} {S : Subgroup G}
    (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hH : H ≠ ⊤) (hz : z ∈ H)
    {K₁ K₂ K₃ : Subgroup ↥H} (h₁ : IsComponent K₁) (h₂ : IsComponent K₂) (h₃ : IsComponent K₃) :
    K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h12, h13, h23⟩ := hcon
  have hB : SecOfG G z ↥H (⟨z, hz⟩ : ↥H) :=
    ⟨H, ⊥, inferInstance, hz, hH, by simp, QuotientGroup.quotientBot, rfl⟩
  exact sec31_two hL hctx hB h₁ h₂ h₃ h12 h13 h23

theorem card_components_le_four {Y : Type} [Group Y] [Finite Y]
    (hc : ∀ K₁ K₂ K₃ : Subgroup Y, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃) :
    Nat.card {K : Subgroup Y // IsComponent K} ≤ 4 := by
  classical
  have : Fintype {K : Subgroup Y // IsComponent K} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  by_contra hlt
  push Not at hlt
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    (Fintype.two_lt_card_iff (α := {K : Subgroup Y // IsComponent K})).1 (by omega)
  rcases hc a.1 b.1 c.1 a.2 b.2 c.2 with h | h | h
  · exact hab (Subtype.ext h)
  · exact hac (Subtype.ext h)
  · exact hbc (Subtype.ext h)

end Comps

section Outer

variable {G : Type} [Group G] [Finite G]

theorem outer_solvable_of_isComponent (hSch : P34.GHSchreier) (hK : KGH G) {M : Subgroup G}
    (hM : M ≠ ⊤) {K : Subgroup ↥M} (hKc : IsComponent K) :
    Group.IsSolvable (ComponentClassification.OuterAutomorphisms.Outer (↥K ⧸ center ↥K)) := by
  have hGH : Uniqueness.SU.SU0.GHGroup ↥M := Uniqueness.SU.SU0.GHGroup.of_kgh hK hM
  have hs : IsSimpleGroup (↥K ⧸ center ↥K) := hKc.1.2.1
  have hn : ∃ a b : ↥K ⧸ center ↥K, a * b ≠ b * a := hKc.1.2.2
  have hl : GHList (↥K ⧸ center ↥K) :=
    hGH.ghList_of_surjection (A := K) (QuotientGroup.mk' (center ↥K))
      (QuotientGroup.mk'_surjective _) hs hn
  exact hSch _ hs hn hl

end Outer

section Layer

variable {G : Type} [Group G] [Finite G]

theorem le_Em_of_perfect (hL : Lemma31Narrow) (hSch : P34.GHSchreier) {z : G} {k : Kind}
    {S M : Subgroup G} (hctx : Stage2Ctx G z k S) (hM : M ≠ ⊤) (hzM : z ∈ M) {X : Subgroup G}
    (hXM : X ≤ M) (hX : ⁅X, X⁆ = X) (hXF : ∀ x ∈ X, ∀ y ∈ Fm M, x * y * x⁻¹ = y) :
    X ≤ Em M := by
  let A : Subgroup ↥M := X.subgroupOf M
  have hAX : A.map M.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXM
  have hA : ⁅A, A⁆ = A := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, hAX, hX]
  have hAperf : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.2 hA
  have hcomps : ∀ K₁ K₂ K₃ : Subgroup ↥M, IsComponent K₁ → IsComponent K₂ → IsComponent K₃ →
      K₁ = K₂ ∨ K₁ = K₃ ∨ K₂ = K₃ := fun K₁ K₂ K₃ h₁ h₂ h₃ => comps_le_two hL hctx hM hzM h₁ h₂ h₃
  have hcard := card_components_le_four hcomps
  have hnorm : ∀ K : Subgroup ↥M, IsComponent K → A ≤ normalizer (K : Set ↥M) := by
    intro K hK a ha
    have h1 := P34.perfect_normalizes_component hcard hA hK
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => h1 a ha x hx, fun hx => by
      have := h1 a⁻¹ (A.inv_mem ha) _ hx
      simpa [mul_assoc] using this⟩
  have hAF : ⁅A, fittingSubgroup ↥M⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha y hy
    have hax : (a : G) ∈ X := ha
    have hyF : (y : G) ∈ Fm M := ⟨y, hy, rfl⟩
    have h2 := hXF (a : G) hax (y : G) hyF
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  have hAE : A ≤ layer ↥M :=
    CFSG.LocalAnalysis.ComponentInitial.unique_perfect_component_normalizer_enters_layer hAperf
      hAF hnorm fun K hK => outer_solvable_of_isComponent hSch hctx.std.kgh hM hK
  intro x hx
  exact ⟨⟨x, hXM hx⟩, hAE hx, rfl⟩

end Layer

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L182

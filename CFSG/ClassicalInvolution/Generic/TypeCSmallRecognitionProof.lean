module

public import CFSG.ClassicalInvolution.Generic.TypeCSmallRecognition
public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetup
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeChain
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def C3ShortNodeA2 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .PSp 2 (conjClass K) z →
      ∃ (Fr : Frame p f 2 (conjClass K) K z) (T₀ T₁ : Subgroup G),
        IsShortNodeAt Fr 0 1 T₀ ∧ IsShortNodeAt Fr 1 2 T₁ ∧
        ∃ W, LinearBlockStandardPair (GaloisField p f) W T₀ T₁

theorem cSetupW_of_routeDSetup {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) (hS : LocalShapeT p f 1 .PSp 2 (conjClass K) z) :
    CSetupW p f 2 (conjClass K) K z := by
  have hcard : Nat.card (GaloisField p f) = p ^ f := natCard_galoisField_of_five_le S.five
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hcard]
    exact ((Fact.out : p.Prime).odd_of_ne_two S.odd).pow
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  refine ⟨S.odd, S.five, le_rfl, S.inClass, S.exact, mem_conjClass_self K, S.cls,
    single_class K, localShapeC_of_T hS, ?_⟩
  intro L hL y hy
  obtain ⟨g, hg⟩ := single_class K L hL
  have hy' : y = g * z * g⁻¹ :=
    Gaps.unique_involution_of_isClassicalMember h2 (S.exact L hL) hy (hg ▸ S.cls.conj g)
  rw [hy']
  exact Gaps.localOddCentral_conj S.inClass.conjInvariant g z S.p1

theorem shapePiece_psp2_of_shortNodes (h : C3ShortNodeA2 p f) : ShapePiece p f 1 .PSp 2 := by
  intro G _ _ _ hnab K z S hS
  have cs := cSetupW_of_routeDSetup S hS
  obtain ⟨Fr, hFr⟩ := h G hnab K z S hS
  obtain ⟨D, -, -⟩ := routeD_typeC_two_of_shortNodes cs S.conn Fr hFr
  exact ⟨D⟩

theorem psp6Recognition_of_shortNodes (h : C3ShortNodeA2 p f) : PSp6Recognition p f := by
  intro G _ _ _ hnab K z S hS
  exact Or.inl
    (oddLieType_of_lieSystem S.odd hnab (shapePiece_psp2_of_shortNodes h G hnab K z S hS))

end CFSG.ClassicalInvolution.Generic.CoreAssembly

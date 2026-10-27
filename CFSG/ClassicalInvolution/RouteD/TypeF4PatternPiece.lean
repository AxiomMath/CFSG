module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternFinal
public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternTwin
import CFSG.ClassicalInvolution.RouteD.NoG2D4Shared
public import CFSG.ClassicalInvolution.RouteD.TypeCMain

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f : ℕ} [Fact p.Prime]

@[expose] def Sp3F4Side (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .PSp 3 (conjClass K) z → F4Linked p f (conjClass K) K z →
      LieSystem p f G (conjClass K)

@[expose] def Sp3C4Side (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .PSp 3 (conjClass K) z → ¬ F4Linked p f (conjClass K) K z →
      LieSystem p f G (conjClass K)

theorem pieceSp3_of_sides (h₁ : Sp3F4Side p f) (h₂ : Sp3C4Side p f) : PieceSp3 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  by_cases hl : F4Linked p f (conjClass K) K z
  · exact h₁ G hnab K z S hS hl
  · exact h₂ G hnab K z S hS hl

@[expose] def Sp3TwinP1 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .PSp 3 (conjClass K) z → TwinProductP1 p f (conjClass K) K z

theorem sp3F4Side_of_inputs (hP1 : Sp3TwinP1 p f) (hTable : F4PerpTableR p f)
    (hTwin : TwinPartnerFactTwin p f .POmegaOdd 4 f) : Sp3F4Side p f := by
  intro G _ _ _ hnab K z S hS hlink
  have hP1x := hP1 G hnab K z S hS
  obtain ⟨d⟩ := LocalShapeC.nonempty_dict S.inClass (mem_conjClass_self K) S.cls
    (localShapeC_of_T hS)
  obtain ⟨D, -, -⟩ := routeD_typeF4_of_twin_inputs S.odd S.five S.inClass S.exact
    (mem_conjClass_self K) (single_class K) S.conn S.cls (localShapeC_of_T hS) S.p1 S.ih hP1x
    (twinProductNoExotic_of_sharedInvolution (G2D4.g2d4SharedInvolution p) S.odd S.five S.inClass
      S.exact (mem_conjClass_self K) S.cls S.p1 d hP1x)
    hlink hTable hTwin
  exact ⟨D⟩

@[expose] def Sp3C4Layers (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .PSp 3 (conjClass K) z → ¬ F4Linked p f (conjClass K) K z →
      ∀ Fr : Frame p f 3 (conjClass K) K z, LayersCommute Fr

theorem cSetup_of_routeDSetup {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hS : LocalShapeT p f 1 .PSp 3 (conjClass K) z) : CSetup p f 3 (conjClass K) K z :=
  { odd := S.odd, five := S.five, three := le_rfl, inClass := S.inClass, exact := S.exact,
    mem := mem_conjClass_self K, cls := S.cls, single := single_class K,
    centerTriv := center_eq_bot hnab, shape := localShapeC_of_T hS,
    p1cl := Balance.localOddCentral_of_classicalMember S.odd (pos_of_five_le S.five) S.inClass
      ⟨K, mem_conjClass_self K, single_class K⟩ (mem_conjClass_self K) S.cls S.p1,
    ih := S.ih }

theorem sp3C4Side_of_layers (h : Sp3C4Layers p f) : Sp3C4Side p f := by
  intro G _ _ _ hnab K z S hS hlink
  obtain ⟨D, -, -⟩ := routeD_typeC_of_layers (cSetup_of_routeDSetup hnab S hS) S.conn
    (h G hnab K z S hS hlink)
  exact ⟨D⟩

end CFSG.ClassicalInvolution.Generic.CoreAssembly

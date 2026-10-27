module

public import CFSG.GH74.Generic.BProg.B2.GenLocG2
public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyG4
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyC2

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

namespace TA7

@[expose] def PuL4m (H : Type) [Group H] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 < p ^ f ∧
    ((p ^ f % 4 = 3 ∧ LieModel H .PSL 4 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel H .PSU 4 p f))

@[expose] def RefinePuL4 : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H : Subgroup N) (t : N) (L : Subgroup N),
    ShapeInCent H t L → SectionalTwoRankLE N 4 → PuL4 ↥H → PuL4m ↥H

@[expose] def RefinePuG2 : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H : Subgroup N) (t : N) (L : Subgroup N),
    ShapeInCent H t L → PuG2 ↥H → PuG2Odd ↥H

end TA7

@[expose] def PuTargetG4 (H : Type) [Group H] : Prop :=
  PuL5 H ∨ TA7.PuL4m H ∨ PuL3sq H ∨ PuG2Odd H

@[expose] def ListedHG (J : Type) [Group J] : Prop := PuTargetG4 J

@[expose] def ListedCompG (J : Type) [Group J] : Prop := ListedHG J ∨ ListedK J ∨ ListedRankOne J

@[expose] def ListedWeakSigMinG5 : Prop :=
  (∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → ListedCompG J → WeakSig2NormG4 J) ∧
    (∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → ListedPair J → WeakSig2TwoG4 J)

structure ListedWeakSigMinFamG5 : Prop where
  l5 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → PuL5 J → WeakSig2NormG4 J
  l4 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → TA7.PuL4m J → WeakSig2NormG4 J
  l3sq : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → PuL3sq J → WeakSig2NormG4 J
  g2 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → PuG2Odd J → WeakSig2NormG4 J
  s1 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape1 J → WeakSig2NormG4 J
  s3 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape3 J → WeakSig2NormG4 J
  s4 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape4 J → WeakSig2NormG4 J
  s5 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → QShape5 J → WeakSig2NormG4 J
  l2 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → ListedRankOne J → WeakSig2NormG4 J
  p3 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsSimpleGroup J → QShape3 J →
    WeakSig2TwoG4 J
  p4 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsSimpleGroup J → QShape4 J →
    WeakSig2TwoG4 J
  p5 : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsSimpleGroup J → QShape5 J →
    WeakSig2TwoG4 J

theorem ListedWeakSigMinG5.of_fam (h : ListedWeakSigMinFamG5) : ListedWeakSigMinG5 := by
  refine ⟨fun J _ _ hq hL => ?_, fun J _ _ hq hp => ?_⟩
  · rcases hL with (h5 | h4 | h3 | hg) | (h1 | h3 | h4 | h5) | h2
    · exact h.l5 J hq h5
    · exact h.l4 J hq h4
    · exact h.l3sq J hq h3
    · exact h.g2 J hq hg
    · exact h.s1 J hq h1
    · exact h.s3 J hq h3
    · exact h.s4 J hq h4
    · exact h.s5 J hq h5
    · exact h.l2 J hq h2
  · obtain ⟨hs, h3 | h4 | h5⟩ := hp
    · exact h.p3 J hq hs h3
    · exact h.p4 J hq hs h4
    · exact h.p5 J hq hs h5

theorem puTargetG4_of_c2 (hL4m : TA7.RefinePuL4) (hG2 : TA7.RefinePuG2)
    {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}
    (hB : B_B2_g4) (hPump : PumpupTableU) (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1Core x K M Q H) (hF : barIn M H = generalizedFitting (Mbar M))
    (hsimple : IsSimpleGroup ↥(barIn M H)) : PuTargetG4 ↥(barIn M H) := by
  obtain ⟨hxM, hSh⟩ := Thm2AssemblyC2.shapeInCent_of_simple hB hs h1 hF hsimple
  rcases hPump (Mbar M) (barIn M H) _ (barIn M K) hSh
      (Thm2AssemblyC2.ghList_of_simple hs h1 hF hsimple) with h5 | h4 | h3 | hg
  · exact Or.inl h5
  · exact Or.inr (Or.inl
      (hL4m (Mbar M) (barIn M H) _ (barIn M K) hSh (sectionalTwoRankLE_Mbar hs) h4))
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (hG2 (Mbar M) (barIn M H) _ (barIn M K) hSh hg)))

end CFSG.GH74.Generic.BProg.B2

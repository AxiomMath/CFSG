module

public import CFSG.ClassicalInvolution.Q3.TL3C11R
public import CFSG.ClassicalInvolution.Q3.TL4OddBasic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Balance.Bootstrap (ShareFour)

section Frames

variable {Y : Type} [Group Y]

@[expose] def FramesAtEdges (Ω : Set (Subgroup Y)) (K : Subgroup Y) (t : Y)
    (𝒯 : Set (Subgroup Y)) : Prop :=
  ∀ J ∈ omegaNbr Ω K, ∀ u : Y, IsUniqueInvolution J u →
    ∃ B ∈ 𝒯, Subgroup.closure ({t, u} : Set Y) ≤ B

@[expose] def FramesHyp51 (𝒯 : Set (Subgroup Y)) : Prop :=
  ∀ B ∈ 𝒯, Hyp51 B

@[expose] def FramesConnected (𝒯 : Set (Subgroup Y)) : Prop :=
  (∀ B ∈ 𝒯, ∀ g : Y, B.map (MulAut.conj g).toMonoidHom ∈ 𝒯) ∧
    ∀ B ∈ 𝒯, ∀ B' ∈ 𝒯,
      Relation.ReflTransGen (fun X X' => X ∈ 𝒯 ∧ X' ∈ 𝒯 ∧ ShareFour X X') B B'

end Frames

section Sec

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def SecMovedOddFree (R : Subgroup Y) (u : Y) (x : SecQ R u) : Prop :=
  ∀ L : Subgroup (SecQ R u), CFSG.IsComponent L → x ∈ Subgroup.normalizer (L : Set (SecQ R u)) →
    (∃ y ∈ L, x * y ≠ y * x) → Q3NM.AutOddFreeOn ↥L (IsInducedAut L x)

end Sec

section Cit3

@[expose] def TightAlphaLeafR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
        IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥

@[expose] def TightMaxSecR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      ∀ J : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J →
      ∀ u : Y, IsUniqueInvolution J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
        (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
        SecMovedOddFree R u
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

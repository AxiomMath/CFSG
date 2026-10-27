module

public import CFSG.ClassicalInvolution.Q3.TL4InductDefs
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Gen

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def Thm6SimpleLe (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup ↥(genFittingFStar Y)], Nat.card Y ≤ n →
    (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightEdgeless R → GoodThreeElement R t ∨ Thm6Exit Y

@[expose] def ExitIdent (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup ↥(genFittingFStar Y)],
    (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) → P ↥(genFittingFStar Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t → Thm6Exit Y

section Cit3


@[expose] def SmallSimpleLeaf6 (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup ↥(genFittingFStar Y)],
    CIT3Below (Nat.card Y) → (∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a) →
    TwoSubgroupsFourGenerated ↥(genFittingFStar Y) → P ↥(genFittingFStar Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → GoodThreeElement R t ∨ Thm6Exit Y

structure SmallLeaves6 : Prop where
  m11 : SmallSimpleLeaf6 TA3.SmallM11
  m12 : SmallSimpleLeaf6 TA3.SmallM12
  l2 : SmallSimpleLeaf6 TA3.SmallL2
  l3 : SmallSimpleLeaf6 TA3.SmallL3
  u3 : SmallSimpleLeaf6 TA3.SmallU3
  g2 : SmallSimpleLeaf6 TA3.SmallG2
  d4 : SmallSimpleLeaf6 TA3.SmallD4
  psp4 : SmallSimpleLeaf6 TA3.SmallPSp4
  twistedG2 : SmallSimpleLeaf6 TA3.SmallTwistedG2
  l4 : SmallSimpleLeaf6 TA3.SmallL4
  u4 : SmallSimpleLeaf6 TA3.SmallU4
  l5 : SmallSimpleLeaf6 TA3.SmallL5
  u5 : SmallSimpleLeaf6 TA3.SmallU5

theorem SmallSimpleLeaf6.of_exitIdent {P : ∀ (F : Type) [Group F], Prop} (h : ExitIdent P) :
    SmallSimpleLeaf6 P :=
  fun Y _ _ _ _ hnab _ hP R S t hd hc _ => Or.inr (h Y hnab hP R S t hd hc)

theorem SmallSimpleLeaf6.of_noQ8Datum {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → TA3.NoQ8Datum F) : SmallSimpleLeaf6 P := by
  intro Y _ _ _ _ hnab hG hPF R S t hd hc _
  exfalso
  have := genFittingFStar_normal Y
  exact h _ hPF Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) hG R S t hd hc.1

theorem SmallSimpleLeaf6.mono {P Q : ∀ (F : Type) [Group F], Prop}
    (hPQ : ∀ (F : Type) [Group F], P F → Q F) (h : SmallSimpleLeaf6 Q) : SmallSimpleLeaf6 P :=
  fun Y _ _ _ hA hnab hG hPF => h Y hA hnab hG (hPQ _ hPF)

theorem SmallSimpleLeaf6.of_or {P Q : ∀ (F : Type) [Group F], Prop} (hP : SmallSimpleLeaf6 P)
    (hQ : SmallSimpleLeaf6 Q) : SmallSimpleLeaf6 fun F _ => P F ∨ Q F :=
  fun Y _ _ _ hA hnab hG hPQ => hPQ.elim (hP Y hA hnab hG) (hQ Y hA hnab hG)

theorem SmallSimpleLeaf6.of_split {P Q₃ Q : ∀ (F : Type) [Group F], Prop}
    (hsplit : ∀ (F : Type) [Group F], P F → Q₃ F ∨ Q F) (h₃ : SmallSimpleLeaf6 Q₃)
    (h : SmallSimpleLeaf6 Q) : SmallSimpleLeaf6 P :=
  SmallSimpleLeaf6.mono hsplit (SmallSimpleLeaf6.of_or h₃ h)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

@[expose] def NoPSignalizer (p : ℕ) {Y : Type*} [Group Y] (D : Subgroup Y) : Prop :=
  ∀ T : Subgroup Y, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set Y) → T = ⊥

@[expose] def LinesTrans {Y : Type*} [Group Y] (D : Subgroup Y) (z : Y) : Prop :=
  ∀ y ∈ D, y ≠ 1 → ∃ h ∈ normalizer (D : Set Y),
    zpowers y = (zpowers z).map (MulAut.conj h).toMonoidHom

@[expose] def AutCommInner (K : Type*) [Group K] : Prop :=
  ∀ γ α : MulAut K, γ * α * γ⁻¹ * α⁻¹ ∈ (MulAut.conj : K →* MulAut K).range

structure I294Cfg (p : ℕ) {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (z g : Y) (D : Subgroup Y) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  simple : IsSimpleGroup L
  nonab : ∃ a b : L, a * b ≠ b * a
  catalog : IsCatalogGroup L
  cent : centralizer (L : Set Y) = ⊥
  rank : CFSG.Open.pRank p (⊤ : Subgroup Y) = 3
  elem : IsElemAbelian p D
  card : Nat.card D = p ^ 2
  mem : z ∈ D
  ne_one : z ≠ 1
  sylow : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set Y))
  diag : IsPlaneDiagonal p D z g
  sylowLine : ∃ x ∈ D, x ≠ 1 ∧
    CFSG.ABGLocalTools.IsSylowOf p D (centralizer ({x} : Set Y))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

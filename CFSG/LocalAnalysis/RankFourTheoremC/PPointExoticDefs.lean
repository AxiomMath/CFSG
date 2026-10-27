module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTypes

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding Subgroup

inductive ExoticFive (p : ℕ) : TauCeti.CFSGIndex → Prop
  | alt (h : 5 ≤ 2 * p) (hp : p = 5) : ExoticFive p (.alternating (2 * p) h)
  | suzuki {d : TauCeti.ValidLieTypeIndex} (hp : p = 5) (hd : d.1 = .suzuki 2) :
      ExoticFive p (.lie d)
  | tits {d : TauCeti.ValidLieTypeIndex} (hp : p = 5) (hd : d.1 = .tits) : ExoticFive p (.lie d)
  | mcl (hp : p = 5) : ExoticFive p (.sporadic .McL)
  | jFour (hp : p = 11) : ExoticFive p (.sporadic .J4)

@[expose] def AutRankTwoAt (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) →
    ∀ B : Subgroup (MulAut K), IsElemAbelian p B → Nat.card B ≤ p ^ 2

@[expose] def SignalizerAutAt (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) → ∀ B Y : Subgroup (MulAut K),
    IsElemAbelian p B → Nat.card B = p ^ 2 → p.Coprime (Nat.card Y) →
    B ≤ normalizer (Y : Set (MulAut K)) →
    (B ≤ (MulAut.conj : K →* MulAut K).range ∨ GL83OuterType24 p i) →
    B ≤ centralizer (Y : Set (MulAut K))

theorem signalizerAutAt_of_gl83 (h : GL83SignalizerAut) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {i : TauCeti.CFSGIndex} (hi : GL83Type24 p i) : SignalizerAutAt p i :=
  fun K _ _ e B Y hB hBc hY hBY hin => h K p i hp hp2 hi e B Y hB hBc hY hBY hin

theorem PPointType.cases_five {p : ℕ} (hp5 : 5 ≤ p) {i : TauCeti.CFSGIndex}
    (h : PPointType p i) :
    (∃ (d : TauCeti.ValidLieTypeIndex) (n : ℕ), 2 ≤ n ∧ i = .lie d ∧ IsLinTwoIndex p n d) ∨
      (∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ IsUnitaryIndex p d ∧
        d.1.fieldExponent = 1) ∨ ExoticFive p i := by
  cases h with
  | linTwo hn hd => exact Or.inl ⟨_, _, hn, rfl, hd⟩
  | altTwoP h hp =>
    rcases hp with rfl | rfl
    · omega
    · exact Or.inr (Or.inr (.alt h rfl))
  | unitary hd hn => exact Or.inr (Or.inl ⟨_, rfl, hd, hn⟩)
  | linTwoEight hp _ => omega
  | mEleven hp => omega
  | linThreeFour hp _ => omega
  | suzuki hp hd => exact Or.inr (Or.inr (.suzuki hp hd))
  | tits hp hd => exact Or.inr (Or.inr (.tits hp hd))
  | mcl hp => exact Or.inr (Or.inr (.mcl hp))
  | jFour hp => exact Or.inr (Or.inr (.jFour hp))

end CFSG.LocalAnalysis.RankFourTheoremC

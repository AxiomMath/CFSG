module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSqTorusFree
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.Main
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding

@[expose] def IdxPlus (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .twistedA _ q | .twistedD _ q => q.p = 2 ∧ q.card ≠ 2 ∧ p ∣ q.card + 1
  | _ => False

@[expose] def AltPlusCell : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y) (p : ℕ) (x : Y), CompParabE L J →
    (p = 5 ∨ p = 7) → PerfectSectionsAltSq p J → x ∈ L → x ^ p = 1 →
    x ∉ Subgroup.centralizer (L : Set Y) → (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
    IsLieOf (IdxPlus p) (↥L ⧸ Subgroup.center ↥L) →
    (∃ E : Subgroup Y, E ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3) → False

theorem isLieOfTorus_split_or_plus {P : TauCeti.LieTypeIndex → Prop}
    (hP : P = IdxA ∨ P = IdxTwistedA ∨ P = IdxB ∨ P = IdxD ∨ P = IdxTwistedD ∨ P = IdxG2)
    {p : ℕ} (hp : p.Prime) {X : Type} [Group X] (h : IsLieOfTorus P p X) :
    IsLieOf (IdxSplit p) X ∨ IsLieOf (IdxPlus p) X := by
  obtain ⟨⟨d, hv⟩, hPd, hnt, ⟨e⟩⟩ := h
  cases d with
  | A r q =>
    have hq : q.p = 2 := by
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [IdxA, IdxTwistedA, IdxB, IdxD,
        IdxTwistedD, IdxG2]
    have hs : p ∣ q.card - 1 := by
      simp only [IndexTorusFree, not_or, not_not] at hnt
      exact hnt.2
    exact Or.inl ⟨⟨_, hv⟩, ⟨hq, hs⟩, ⟨e⟩⟩
  | B r q =>
    have hq : q.p = 2 := by
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [IdxA, IdxTwistedA, IdxB, IdxD,
        IdxTwistedD, IdxG2]
    have hs : p ∣ q.card - 1 := by
      simp only [IndexTorusFree, not_or, not_not] at hnt
      exact hnt.2
    exact Or.inl ⟨⟨_, hv⟩, ⟨hq, hs⟩, ⟨e⟩⟩
  | D r q =>
    have hq : q.p = 2 := by
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [IdxA, IdxTwistedA, IdxB, IdxD,
        IdxTwistedD, IdxG2]
    have hs : p ∣ q.card - 1 := by
      simp only [IndexTorusFree, not_or, not_not] at hnt
      exact hnt.2
    exact Or.inl ⟨⟨_, hv⟩, ⟨hq, hs⟩, ⟨e⟩⟩
  | G2 q =>
    have hq : q.p = 2 := by
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [IdxA, IdxTwistedA, IdxB, IdxD,
        IdxTwistedD, IdxG2]
    have hs : p ∣ q.card - 1 := by
      simp only [IndexTorusFree, not_or, not_not] at hnt
      exact hnt.2
    exact Or.inl ⟨⟨_, hv⟩, ⟨hq, hs⟩, ⟨e⟩⟩
  | twistedA r q =>
    have hq : q.p = 2 := by
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [IdxA, IdxTwistedA, IdxB, IdxD,
        IdxTwistedD, IdxG2]
    simp only [IndexTorusFree, not_or, not_not] at hnt
    obtain ⟨hne, hdvd⟩ := hnt
    have hfac : q.card ^ 2 - 1 = (q.card + 1) * (q.card - 1) := by
      rw [← Nat.sq_sub_sq q.card 1, one_pow]
    rw [hfac] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
    · exact Or.inr ⟨⟨_, hv⟩, ⟨hq, hne, h1⟩, ⟨e⟩⟩
    · exact Or.inl ⟨⟨_, hv⟩, ⟨hq, h1⟩, ⟨e⟩⟩
  | twistedD r q =>
    have hq : q.p = 2 := by
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [IdxA, IdxTwistedA, IdxB, IdxD,
        IdxTwistedD, IdxG2]
    simp only [IndexTorusFree, not_or, not_not] at hnt
    obtain ⟨hne, hdvd⟩ := hnt
    have hfac : q.card ^ 2 - 1 = (q.card + 1) * (q.card - 1) := by
      rw [← Nat.sq_sub_sq q.card 1, one_pow]
    rw [hfac] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
    · exact Or.inr ⟨⟨_, hv⟩, ⟨hq, hne, h1⟩, ⟨e⟩⟩
    · exact Or.inl ⟨⟨_, hv⟩, ⟨hq, h1⟩, ⟨e⟩⟩
  | _ => exact (by
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hPd.elim)

theorem kFactBlockToralAlt_of_plus (hGA : CFSG.Open.GriessAllModelsStatement)
    (hPlus : AltPlusCell) : KFactBlockToralAlt := by
  intro Y _ _ L J hL hcl hpar hJL hnb p hp hAlt x hxL hxp hxC hfix hE
  have hCP : CompParabE L J := ⟨hL, hcl, hpar, hJL, hnb⟩
  have hp' : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp5 : 5 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have hfam : ∀ {P : TauCeti.LieTypeIndex → Prop},
      (P = IdxA ∨ P = IdxTwistedA ∨ P = IdxB ∨ P = IdxD ∨ P = IdxTwistedD ∨ P = IdxG2) →
      IsLieOf P (↥L ⧸ Subgroup.center ↥L) → False := by
    intro P hP hX
    rcases isLieOf_split (p := p) hX with hTF | hT
    · rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
      · exact no_pow_three_of_altSq_torusFree_classical hGA (Or.inl rfl) hCP hp' hp5 hTF hAlt
          hfix hE
      · exact no_pow_three_of_altSq_torusFree_classical hGA (Or.inr (Or.inl rfl)) hCP hp' hp5 hTF
          hAlt hfix hE
      · exact no_pow_three_of_altSq_torusFree_classical hGA (Or.inr (Or.inr (Or.inl rfl))) hCP hp'
          hp5 hTF hAlt hfix hE
      · exact no_pow_three_of_altSq_torusFree_classical hGA
          (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hCP hp' hp5 hTF hAlt hfix hE
      · exact no_pow_three_of_altSq_torusFree_classical hGA
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hCP hp' hp5 hTF hAlt hfix hE
      · exact no_pow_three_of_altSq_torusFree_g2 hGA hCP hp' hp5 hTF hAlt hfix hE
    · rcases isLieOfTorus_split_or_plus hP hp' hT with hs | hpl
      · exact false_of_altSq_split hCP hp hAlt hs
      · exact hPlus Y L J p x hCP hp hAlt hxL hxp hxC hfix hpl hE
  rcases isClassicalTwoOrG2_family_cases hcl with hA | h2A | hB | hD | h2D | hG2 | hS
  · exact hfam (Or.inl rfl) hA
  · exact hfam (Or.inr (Or.inl rfl)) h2A
  · exact hfam (Or.inr (Or.inr (Or.inl rfl))) hB
  · exact hfam (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hD
  · exact hfam (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h2D
  · exact hfam (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hG2
  · obtain ⟨E, hEle, -, hEc⟩ := hE
    exact no_pow_three_of_small hGA hCP hp' hp5 hS (hEle.trans inf_le_left) hEc

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus

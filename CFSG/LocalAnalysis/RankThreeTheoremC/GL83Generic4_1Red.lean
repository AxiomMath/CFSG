module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericQuasisimple3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericListPrune3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1Alt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

@[expose] def GenericRedAt (G : Type) [Group G] [Finite G]
    (L : ℕ → ∀ (Q : Type) [Group Q], Prop) : Prop :=
  GenericAt G fun p _ M x => 5 ≤ p → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J → L p Q →
      ¬ Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) →
      ∃ _ : Fact p.Prime, Nonempty (Q ≃* PSL(2, GaloisField p 2))

theorem GenericRedAt.mono {G : Type} [Group G] [Finite G] {L L' : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hLL : ∀ (p : ℕ) (Q : Type) [Group Q], L' p Q → L p Q) (h : GenericRedAt G L) :
    GenericRedAt G L' := by
  intro p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hL hFi
  exact h p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker
    (hLL p Q hL) hFi

theorem GenericRedAt.union {G : Type} [Group G] [Finite G]
    {L₁ L₂ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (h₁ : GenericRedAt G L₁) (h₂ : GenericRedAt G L₂) :
    GenericRedAt G fun p Q _ => L₁ p Q ∨ L₂ p Q := by
  intro p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hL hFi
  rcases hL with hL | hL
  · exact h₁ p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hL hFi
  · exact h₂ p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hL hFi

theorem genericRedAt_psl (G : Type) [Group G] [Finite G] :
    GenericRedAt G fun p Q _ => ∃ _ : Fact p.Prime, Nonempty (Q ≃* PSL(2, GaloisField p 2)) := by
  intro p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hL hFi
  exact hL

@[expose] def GL83GenericListExclusionRedE3 (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedAt G fun p Q _ => IsRankTwoSEGroupE3 p Q ∨ (p = 5 ∧ IsoLie Q (.suzuki 2))

theorem GL83GenericListExclusionRed.of_e3 {G : Type} [Group G] [Finite G]
    (he : CFSG.Open.evenRank G = 3) (h : GL83GenericListExclusionRedE3 G) :
    GL83GenericListExclusionRed G := by
  intro p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hlist hFi
  refine h p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker ?_ hFi
  rcases hlist with hSE | hSz
  · refine Or.inl ?_
    rcases hSE with ⟨hf, ⟨f⟩⟩ | ⟨q, hq1, hq2, hl⟩ | ⟨h5', ⟨f⟩⟩ | ⟨h3, -⟩ | ⟨h5', h'⟩ |
      ⟨h11, ⟨f⟩⟩
    · exact Or.inl ⟨hf, ⟨f⟩⟩
    · exact Or.inr (Or.inl ⟨q, hq1, hq2, hl⟩)
    · by_cases hp5 : p = 5
      · subst hp5
        exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨f⟩⟩))
      · exfalso
        have hprime : p.Prime := sigmaA_prime p hp
        have h6 : p ≠ 6 := by
          rintro rfl
          exact absurd hprime (by decide)
        exact false_of_section_alternating he (n := 2 * p) (by omega) (H := J)
          (f.toMonoidHom.comp ψ) (f.surjective.comp hψ)
    · exact absurd h3 (by omega)
    · rcases h' with hl | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
      · exact Or.inr (Or.inr (Or.inl ⟨h5', Or.inr (Or.inl hl)⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h5', Or.inr (Or.inr ⟨f⟩)⟩))
      · exact (hFi ⟨f⟩).elim
    · exact Or.inr (Or.inr (Or.inr ⟨h11, ⟨f⟩⟩))
  · exact Or.inr hSz

@[expose] def GL83GenericListExclusionRedU3 (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedAt G fun p Q _ =>
    ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoLie Q (.twistedA 2 q)

@[expose] def GL83GenericListExclusionRedSpor (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedAt G fun p Q _ =>
    (p = 5 ∧ (Nonempty (Q ≃* alternatingGroup (Fin 10)) ∨ IsoLie Q .tits ∨
      Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group))) ∨
    (p = 11 ∧ Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4).Group)) ∨
    (p = 5 ∧ IsoLie Q (.suzuki 2))

theorem GL83GenericListExclusionRedE3.of_split {G : Type} [Group G] [Finite G]
    (hU : GL83GenericListExclusionRedU3 G) (hS : GL83GenericListExclusionRedSpor G) :
    GL83GenericListExclusionRedE3 G := by
  refine GenericRedAt.mono (fun p Q _ hL => ?_) ((genericRedAt_psl G).union (hU.union hS))
  rcases hL with hE | hSz
  · rcases hE with hpsl | hu | ⟨h5, h⟩ | ⟨h11, h⟩
    · exact Or.inl hpsl
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr (Or.inl ⟨h5, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h11, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hSz)))

end CFSG.LocalAnalysis.RankThreeTheoremC

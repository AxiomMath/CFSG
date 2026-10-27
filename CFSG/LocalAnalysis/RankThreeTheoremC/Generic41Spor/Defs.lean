module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1Red

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def IsTitsType (p : ℕ) (Q : Type) [Group Q] : Prop := p = 5 ∧ IsoLie Q .tits

@[expose] def IsMcLType (p : ℕ) (Q : Type) [Group Q] : Prop :=
  p = 5 ∧ Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group)

@[expose] def IsJ4Type (p : ℕ) (Q : Type) [Group Q] : Prop :=
  p = 11 ∧ Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4).Group)

@[expose] def IsA10Type (p : ℕ) (Q : Type) [Group Q] : Prop :=
  p = 5 ∧ Nonempty (Q ≃* alternatingGroup (Fin 10))

@[expose] def IsSz32Type (p : ℕ) (Q : Type) [Group Q] : Prop := p = 5 ∧ IsoLie Q (.suzuki 2)

@[expose] def IsExoticType (p : ℕ) (Q : Type) [Group Q] : Prop :=
  (p = 5 ∧ (Nonempty (Q ≃* alternatingGroup (Fin 10)) ∨ IsoLie Q .tits ∨
      Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group))) ∨
    (p = 11 ∧ Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4).Group)) ∨
    (p = 5 ∧ IsoLie Q (.suzuki 2))

theorem isExoticType_iff {p : ℕ} {Q : Type} [Group Q] :
    IsExoticType p Q ↔ IsA10Type p Q ∨ IsTitsType p Q ∨ IsMcLType p Q ∨ IsJ4Type p Q ∨
      IsSz32Type p Q := by
  unfold IsExoticType IsA10Type IsTitsType IsMcLType IsJ4Type IsSz32Type
  constructor
  · rintro (⟨h, h1 | h1 | h1⟩ | h | h)
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr (Or.inl ⟨h, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro (⟨h, h1⟩ | ⟨h, h1⟩ | ⟨h, h1⟩ | h | h)
    · exact Or.inl ⟨h, Or.inl h1⟩
    · exact Or.inl ⟨h, Or.inr (Or.inl h1)⟩
    · exact Or.inl ⟨h, Or.inr (Or.inr h1)⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

variable {G : Type} [Group G] [Finite G]

structure ExoticNormal (p : ℕ) (M : Subgroup G) (x : G) (J : Subgroup G) : Prop where
  le_centralizer : J ≤ centralizer ({x} : Set G)
  centralizer_le : centralizer ({x} : Set G) ≤ normalizer (J : Set G)
  perfect : Group.IsPerfect J
  not_le : ¬ J ≤ M
  lt_core : rankThreePrimeCore p J < J
  minimal : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
    N = rankThreePrimeCore p J ∨ N = J
  iso : ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
    ψ.ker = (rankThreePrimeCore p J).subgroupOf J ∧ IsExoticType p Q

@[expose] def NoExoticPoint (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → LargerPrimesUnique G p →
      ∀ x : G, IsGenericPoint p P M x → 5 ≤ p → ∀ J : Subgroup G, ExoticNormal p M x J → False

theorem genericListSpor_of_noExoticPoint (h : NoExoticPoint G) :
    GL83GenericListExclusionRedSpor G := by
  intro p hp P M hM hfail hIH x hgen h5 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hL hFi
  exact (h p hp P M hM hfail hIH x hgen h5 J ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance,
    ψ, hψ, hker, hL⟩).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

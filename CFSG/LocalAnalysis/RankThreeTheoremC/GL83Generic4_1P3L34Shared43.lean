module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Residues

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83GenericPrimeThreeLemma43 (G : Type) [Group G] [Finite G] : Prop :=
  GenericAt G fun p P M x => p = 3 → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J →
      ((Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group) ∧
          M11Prop34 p P x) ∨ (IsRankThreeL34 Q ∧ L34Prop34 p P J x)) →
      L34PointLemma43 p P M x

theorem GL83GenericPrimeThreeLemma43.toM11 (h : GL83GenericPrimeThreeLemma43 G) :
    GL83GenericPrimeThreeM11Lemma43 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34
  exact h p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker
    (Or.inl ⟨hQ, h34⟩)

theorem GL83GenericPrimeThreeLemma43.toL34 (h : GL83GenericPrimeThreeLemma43 G) :
    GL83GenericPrimeThreeL34Lemma43 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34
  exact h p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker
    (Or.inr ⟨hQ, h34⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Shared43

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def M11Prop34S (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (J : Subgroup G)
    (x : G) : Prop :=
  M11Prop34 p P x ∧
  IsElemAbelian p (((P : Subgroup G) ⊓ J) ⊔ zpowers x) ∧
  Nat.card (((P : Subgroup G) ⊓ J) ⊔ zpowers x : Subgroup G) = p ^ 3 ∧
  (∀ y ∈ (P : Subgroup G), y ^ p = 1 → y ∈ ((P : Subgroup G) ⊓ J) ⊔ zpowers x)

@[expose] def GenericM11AtJ (G : Type) [Group G] [Finite G]
    (Φ : ∀ p : ℕ, Sylow p G → Subgroup G → G → Subgroup G → Prop) : Prop :=
  GenericAt G fun p P M x => p = 3 → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J →
      Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group) →
      Φ p P M x J

@[expose] def GL83GenericPrimeThreeM11Shape (G : Type) [Group G] [Finite G] : Prop :=
  GenericM11AtJ G fun p P _ x J => M11Prop34 p P x → M11Prop34S p P J x

@[expose] def GL83GenericPrimeThreeM11Lemma43S (G : Type) [Group G] [Finite G] : Prop :=
  GenericM11AtJ G fun p P M x J => M11Prop34S p P J x → M11Lemma43 p P M x

@[expose] def GL83GenericPrimeThreeLemma43S (G : Type) [Group G] [Finite G] : Prop :=
  GenericAt G fun p P M x => p = 3 → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J →
      ((Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group) ∧
          M11Prop34S p P J x) ∨ (IsRankThreeL34 Q ∧ L34Prop34 p P J x)) →
      L34PointLemma43 p P M x

theorem GL83GenericPrimeThreeLemma43S.of_parts (h₁ : GL83GenericPrimeThreeM11Lemma43S G)
    (h₂ : GL83GenericPrimeThreeL34Lemma43 G) : GL83GenericPrimeThreeLemma43S G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  rcases hQ with ⟨hQ, h34⟩ | ⟨hQ, h34⟩
  · exact h₁ p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ h34
  · exact h₂ p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ h34

theorem GL83GenericPrimeThreeLemma43.of_S (hshape : GL83GenericPrimeThreeM11Shape G)
    (h : GL83GenericPrimeThreeLemma43S G) : GL83GenericPrimeThreeLemma43 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  refine h p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker ?_
  rcases hQ with ⟨hQ, h34⟩ | ⟨hQ, h34⟩
  · exact Or.inl ⟨hQ, hshape p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q ψ
      hψ hker hQ h34⟩
  · exact Or.inr ⟨hQ, h34⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

module

public import CFSG.CGT.PushingUpLit.EightOneWindowJS

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.QuasithinUnique.Setup.Campbell CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement

section Anchored

variable {G : Type} [Group G]

@[expose] def AnchoredWitness (X D N : Subgroup G) : Prop :=
  N ∈ maximalTwoLocalsContaining ((X ⊔ D : Subgroup G) : Set G) ∧
    ¬ (X.subgroupOf N).IsSubnormal ∧
    ((X ≤ Subgroup.normalizer ((jIn D : Subgroup G) : Set G) ∧
        (X.subgroupOf (Subgroup.normalizer ((jIn D : Subgroup G) : Set G))).IsSubnormal) ∨
      ∃ S : Subgroup G, IsSylowOf 2 S (Subgroup.normalizer (X : Set G)) ∧ S ≤ N)

namespace AnchoredWitness

variable {X D N : Subgroup G}

theorem isMaximalTwoLocal (h : AnchoredWitness X D N) : IsMaximalTwoLocal N :=
  h.1.1

theorem xd_le (h : AnchoredWitness X D N) : X ⊔ D ≤ N :=
  fun _ hg => h.1.2 hg

theorem not_isSubnormal (h : AnchoredWitness X D N) : ¬ (X.subgroupOf N).IsSubnormal :=
  h.2.1

end AnchoredWitness

end Anchored

namespace EightOneWindow

section Family

variable {G : Type} [Group G]

@[expose] def WindowFamily (X : Subgroup G) : Set (Subgroup G) :=
  {D | IsPGroup 2 D ∧ oTwoIn X ≤ D ∧ D ≤ centralizerModCore X ∧
    ∃ N : Subgroup G, N ∈ maximalTwoLocalsContaining ((X ⊔ D : Subgroup G) : Set G) ∧
      ¬ (X.subgroupOf N).IsSubnormal}

theorem ne_bot_of_mem_windowFamily [Finite G] {X D : Subgroup G} (hX : InClassX ↥X)
    (hD : D ∈ WindowFamily X) : D ≠ ⊥ := by
  obtain ⟨-, hOD, -, -⟩ := hD
  intro h
  rw [h] at hOD
  exact ThreeFromEight.oTwoIn_ne_bot_of_isShortGroup hX.1 (le_bot_iff.mp hOD)

end Family

section Steps

variable {G : Type} [Group G] [Finite G]

theorem dichotomy {X D : Subgroup G} (hX : InClassXG X) (hD : D ∈ WindowFamily X)
    (hmax : ∀ D' ∈ WindowFamily X, D ≤ D' → D' ≤ D) :
    (X.subgroupOf (Subgroup.normalizer (D : Set G))).IsSubnormal ∧
      (IsSylowOf 2 D (centralizerModCore X) ∨
        (X.subgroupOf (Subgroup.normalizer ((jIn D : Subgroup G) : Set G))).IsSubnormal) := by
  have hD1 : D ≠ ⊥ := ne_bot_of_mem_windowFamily hX.1 hD
  obtain ⟨hD2, hOD, hDC, -⟩ := hD
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := le_normalizer_of_le_centralizerModCore hOD hDC
  obtain ⟨D₁, hD₁, hDD₁⟩ := Nine.exists_isSylowOf_ge hD2 hDC
  by_cases heq : D = D₁
  · subst heq
    exact ⟨(hX.2 D hD₁).1.2, Or.inl hD₁⟩
  · obtain ⟨x, hxD₁, hxN, hxD⟩ := exists_mem_normalizer_not_mem hD₁.2.1 hDD₁ heq
    have hDD' : D ≤ Subgroup.normalizer (D : Set G) ⊓ D₁ := le_inf Subgroup.le_normalizer hDD₁
    have hD'2 : IsPGroup 2 (Subgroup.normalizer (D : Set G) ⊓ D₁ : Subgroup G) :=
      hD₁.2.1.to_le inf_le_right
    have hD'C : Subgroup.normalizer (D : Set G) ⊓ D₁ ≤ centralizerModCore X :=
      inf_le_right.trans hD₁.1
    have hnotD' : Subgroup.normalizer (D : Set G) ⊓ D₁ ∉ WindowFamily X := fun hD' =>
      hxD (hmax _ hD' hDD' ⟨hxN, hxD₁⟩)
    have hall : ∀ N : Subgroup G, N ∈ maximalTwoLocalsContaining
        ((X ⊔ (Subgroup.normalizer (D : Set G) ⊓ D₁) : Subgroup G) : Set G) →
        (X.subgroupOf N).IsSubnormal := by
      intro N hN
      by_contra hns
      exact hnotD' ⟨hD'2, hOD.trans hDD', hD'C, N, hN, hns⟩
    obtain ⟨N, hKN, hNmax⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
      (isPLocal_normalizer_of_isPGroup (isPGroup_jIn hD2) (jIn_ne_bot hD2 hD1))
    have hND : Subgroup.normalizer (D : Set G) ≤ N := (normalizer_le_normalizer_jIn D).trans hKN
    have hXN : X ⊔ (Subgroup.normalizer (D : Set G) ⊓ D₁) ≤ N :=
      sup_le (hXD.trans hND) (inf_le_left.trans hND)
    have hsub := hall N ⟨hNmax, fun g hg => hXN hg⟩
    exact ⟨isSubnormal_subgroupOf_mono hXD hND hsub, Or.inr
      (isSubnormal_subgroupOf_mono (hXD.trans (normalizer_le_normalizer_jIn D)) hKN hsub)⟩

theorem isSylowOf_inf {X D N : Subgroup G} (hD : D ∈ WindowFamily X)
    (hmax : ∀ D' ∈ WindowFamily X, D ≤ D' → D' ≤ D)
    (hN : N ∈ maximalTwoLocalsContaining ((X ⊔ D : Subgroup G) : Set G))
    (hnot : ¬ (X.subgroupOf N).IsSubnormal) : IsSylowOf 2 D (centralizerModCore X ⊓ N) := by
  obtain ⟨hD2, hOD, hDC, -⟩ := hD
  have hXDN : X ⊔ D ≤ N := fun g hg => hN.2 hg
  have hXN : X ≤ N := le_sup_left.trans hXDN
  have hDle : D ≤ centralizerModCore X ⊓ N := le_inf hDC (le_sup_right.trans hXDN)
  obtain ⟨D₂, hD₂, hDD₂⟩ := Nine.exists_isSylowOf_ge hD2 hDle
  by_cases heq : D = D₂
  · rw [heq]
    exact hD₂
  · obtain ⟨x, hxD₂, hxN, hxD⟩ := exists_mem_normalizer_not_mem hD₂.2.1 hDD₂ heq
    have hDD'' : D ≤ Subgroup.normalizer (D : Set G) ⊓ D₂ := le_inf Subgroup.le_normalizer hDD₂
    have hle : Subgroup.normalizer (D : Set G) ⊓ D₂ ≤ centralizerModCore X ⊓ N :=
      inf_le_right.trans hD₂.1
    have hmem : Subgroup.normalizer (D : Set G) ⊓ D₂ ∈ WindowFamily X :=
      ⟨hD₂.2.1.to_le inf_le_right, hOD.trans hDD'', hle.trans inf_le_left, N,
        ⟨hN.1, fun g hg => (sup_le hXN (hle.trans inf_le_right)) hg⟩, hnot⟩
    exact absurd (hmax _ hmem hDD'' ⟨hxN, hxD₂⟩) hxD

theorem exists_anchored {X D : Subgroup G} (hX : InClassXG X) (hD : D ∈ WindowFamily X)
    (hmax : ∀ D' ∈ WindowFamily X, D ≤ D' → D' ≤ D) : ∃ N, AnchoredWitness X D N := by
  have hD1 : D ≠ ⊥ := ne_bot_of_mem_windowFamily hX.1 hD
  have hdich := dichotomy hX hD hmax
  obtain ⟨hD2, hOD, hDC, N₀, hN₀, hnot₀⟩ := hD
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := le_normalizer_of_le_centralizerModCore hOD hDC
  by_cases hJ : (X.subgroupOf (Subgroup.normalizer ((jIn D : Subgroup G) : Set G))).IsSubnormal
  · exact ⟨N₀, hN₀, hnot₀, Or.inl ⟨hXD.trans (normalizer_le_normalizer_jIn D), hJ⟩⟩
  · have hsyl : IsSylowOf 2 D (centralizerModCore X) := hdich.2.resolve_right hJ
    obtain ⟨S, hS, hDS, hSD⟩ := exists_isSylowOf_normalizer_between hsyl
    obtain ⟨N, hKN, hNmax⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
      (isPLocal_normalizer_of_isPGroup (isPGroup_jIn hD2) (jIn_ne_bot hD2 hD1))
    have hSK : S ≤ Subgroup.normalizer ((jIn D : Subgroup G) : Set G) :=
      hSD.trans (normalizer_le_normalizer_jIn D)
    have hXK : X ≤ Subgroup.normalizer ((jIn D : Subgroup G) : Set G) :=
      hXD.trans (normalizer_le_normalizer_jIn D)
    have hXDN : X ⊔ D ≤ N := sup_le (hXK.trans hKN) ((hDS.trans hSK).trans hKN)
    exact ⟨N, ⟨hNmax, fun g hg => hXDN hg⟩,
      fun hsub => hJ (isSubnormal_subgroupOf_mono hXK hKN hsub), Or.inr ⟨S, hS, hSK.trans hKN⟩⟩

theorem inClassXGIn_of_anchored {X D N : Subgroup G} (hX : InClassXG X) (hD : D ∈ WindowFamily X)
    (hmax : ∀ D' ∈ WindowFamily X, D ≤ D' → D' ≤ D) (hN : AnchoredWitness X D N) :
    InClassXGIn N X := by
  obtain ⟨hNmem, hnot, hanch⟩ := hN
  have hdich := dichotomy hX hD hmax
  have hDsyl : IsSylowOf 2 D (centralizerModCore X ⊓ N) := isSylowOf_inf hD hmax hNmem hnot
  obtain ⟨-, hOD, hDC, -⟩ := hD
  have hXDN : X ⊔ D ≤ N := fun g hg => hNmem.2 hg
  have hXN : X ≤ N := le_sup_left.trans hXDN
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := le_normalizer_of_le_centralizerModCore hOD hDC
  have hXJ : X ≤ Subgroup.normalizer ((jIn D : Subgroup G) : Set G) :=
    hXD.trans (normalizer_le_normalizer_jIn D)
  refine inClassXGIn_of_sylow hXN hX.1 hDsyl
    ⟨hXD, isSubnormal_subgroupOf_mono (le_inf hXD hXN) inf_le_left hdich.1⟩ ?_
  by_cases hJ : (X.subgroupOf (Subgroup.normalizer ((jIn D : Subgroup G) : Set G))).IsSubnormal
  · exact Or.inr ⟨hXJ, isSubnormal_subgroupOf_mono (le_inf hXJ hXN) inf_le_left hJ⟩
  · left
    have hsyl : IsSylowOf 2 D (centralizerModCore X) := hdich.2.resolve_right hJ
    rcases hanch with ⟨-, hJ'⟩ | ⟨S, hS, hSN⟩
    · exact absurd hJ' hJ
    · have hX1 : X = ⁅jIn (Subgroup.normalizer (X : Set G)), X⁆ :=
        ((hX.2 D hsyl).2).resolve_right fun h => hJ h.2
      have hXS : X = ⁅jIn S, X⁆ := commutator_jIn_of_isSylowOf hX.1 hS hX1
      have hSK : IsSylowOf 2 S (Subgroup.normalizer (X : Set G) ⊓ N) :=
        isSylowOf_of_le_of_le hS (le_inf hS.1 hSN) inf_le_left
      have hJS : jIn S ≤ jIn (Subgroup.normalizer (X : Set G) ⊓ N) :=
        jIn_mono_of_pRank_eq hSK.1 (pRank_eq_of_isSylowOf hSK)
      refine le_antisymm (hXS.le.trans (Subgroup.commutator_mono hJS le_rfl)) ?_
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp ((jIn_le _).trans inf_le_left)

end Steps

end EightOneWindow

section Window

variable {G : Type} [Group G] [Finite G]

open EightOneWindow

theorem exists_window (_hchar : CFSG.Assembly.IsCharTwoType G) {X : Subgroup G}
    (hX : InClassXG X) {N₀ : Subgroup G} (hN₀ : N₀ ∈ maximalTwoLocalsContaining (X : Set G))
    (hnot : ¬ (X.subgroupOf N₀).IsSubnormal) :
    ∃ D : Subgroup G, IsPGroup 2 D ∧ oTwoIn X ≤ D ∧ D ≤ centralizerModCore X ∧
      (∃ N, AnchoredWitness X D N) ∧ (∀ N, AnchoredWitness X D N → InClassXGIn N X) := by
  have h0 : oTwoIn X ∈ WindowFamily X := by
    refine ⟨ThreeFromEight.isPGroup_oTwoIn X, le_rfl, oTwoIn_le_centralizerModCore X, N₀, ?_,
      hnot⟩
    rw [sup_eq_left.mpr (oTwoIn_le X)]
    exact hN₀
  obtain ⟨D, hD, hmax⟩ : ∃ D ∈ WindowFamily X, ∀ D' ∈ WindowFamily X, D ≤ D' → D' ≤ D := by
    obtain ⟨D, hD⟩ := (Set.toFinite (WindowFamily X)).exists_maximal ⟨oTwoIn X, h0⟩
    exact ⟨D, hD.1, fun D' hD' hle => hD.2 hD' hle⟩
  obtain ⟨hD2, hOD, hDC, -⟩ := id hD
  exact ⟨D, hD2, hOD, hDC, exists_anchored hX hD hmax,
    fun N hN => inClassXGIn_of_anchored hX hD hmax hN⟩

end Window

end CFSG.CGT.PushingUpLit

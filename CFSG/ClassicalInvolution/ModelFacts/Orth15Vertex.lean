module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameVertex

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

namespace FrameVertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem movedComponent_eq' (hΩ : ConjInvariant Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hbc : b ≠ c) {M : Subgroup G} (hM : M ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b) (D : LieDecomposition (exactImages Ω c) (exactJoin Ω c)) :
    ∃ j₀ : D.ι, modOdd c (exactCore c M) ≤ D.Q j₀ ∧
      ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L → L = D.Q j₀ := by
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB hbB
  have hbmem := oddQuotMk_mem_exactImage (p := p) (f := f) hbC hc2 hM hMb
  have hMfam : exactCore c M ∈ exactFamily Ω c := exactCore_mem_exactFamily hM
  obtain ⟨j₀, hj₀⟩ := D.exists_le (modOdd c (exactCore c M))
    ⟨exactCore c M, ⟨hMfam, exactCore_le_centralizer c M⟩, rfl⟩
  have hbJ : oddQuotMk c ⟨b, hbC⟩ ∈ exactJoin Ω c := modOdd_le_exactJoin hMfam hbmem
  refine ⟨j₀, hj₀, fun L hL hmov => ?_⟩
  have hbBar : oddQuotMk c ⟨b, hbC⟩ ∈ modOdd c B := oddQuotMk_mem_modOdd hbB hbC
  have hnot : oddQuotMk c ⟨b, hbC⟩ ∉ modOdd c (Subgroup.zpowers c) :=
    Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbB hb1 hbc hbC
  obtain ⟨y, hyL, hy⟩ := hmov _ hbBar hnot
  have := exactJoin_normal (c := c) hΩ
  rcases D.eq_or_commutes_of_isComponentOf ((CFSG.isComponent_iff_open L).mp hL) with
    ⟨i, rfl⟩ | hcomm
  · by_cases hi : i = j₀
    · rw [hi]
    · exact absurd (D.commute i j₀ hi y hyL _ (hj₀ hbmem)).symm hy
  · exact absurd (hcomm y hyL _ hbJ).symm hy

theorem hyp51At_of_witness_alpha (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hbc : b ≠ c) {M : Subgroup G} (hM : M ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b)
    (hα : ∀ (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card),
      modOdd c (exactCore c M) ≤
          (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
        MovedByAll B c (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
          alphaOf (inducedImage (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range
            (modOdd c B)) = ⊥) :
    Hyp51At B c := by
  refine ⟨uniq_of_witness hp2 hq hΩ hcls hBelow hc2 hnc hB hcB hc1 hbB hb1 hbc hM hMb, ?_⟩
  intro L hL hmov
  have hne : (tqMembers Ω c).Nonempty := ⟨M, hM⟩
  obtain ⟨Dsys⟩ := lieSystemAt_exactFamily hΩ hcls hc2 hBelow hnc hne
  obtain ⟨D', hD'Q, -⟩ := lieDecomposition_exactFamily_comp hp2
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hq hΩ hcls hc2 hne Dsys
  obtain ⟨j₀, hMj₀, hj₀⟩ := movedComponent_eq' hΩ hc2 hB hcB hc1 hbB hb1 hbc hM hMb D'
  obtain ⟨j, hj⟩ := hD'Q j₀
  have hLeq : L = (secComponentHom (normalizesLayer_exactFamily hΩ) Dsys j).range :=
    (hj₀ L hL hmov).trans hj.symm
  subst hLeq
  exact hα Dsys j (hMj₀.trans hj.symm.le) hmov

end FrameVertex

end CFSG.ClassicalInvolution.Asc77

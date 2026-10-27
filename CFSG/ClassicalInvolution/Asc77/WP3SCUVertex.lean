module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameVertex
public import CFSG.ClassicalInvolution.Asc77.WP3SCUAlpha

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.StrongBalance CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

namespace FrameVertex

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem hyp51At_of_system_diag (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hBelow : CITBelowU p f (Nat.card G))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hcB : c ∈ B) (hc1 : c ≠ 1)
    {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c) {M : Subgroup G}
    (hM : M ∈ tqMembers Ω c) (hMb : IsClassicalMember p f M b)
    (hD : ∃ D : LocalLieSystemAt p f (exactFamily Ω c) c, ∀ j : Fin D.card,
      MovedByAll B c (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
        (D.tag j = .PSL ∨ D.tag j = .PSU) ∧
          ToralActionDiag 2 (D.tag j) (D.rank j) p (D.exp j) Fact.out
            (secComponentHom (normalizesLayer_exactFamily hΩ) D j) (modOdd c B)) :
    Hyp51At B c := by
  refine ⟨uniq_of_witness hp2 hq hΩ hcls hBelow hc2 hnc hB hcB hc1 hbB hb1 hbc hM hMb, ?_⟩
  intro L hL hmov
  have hne : (tqMembers Ω c).Nonempty := ⟨M, hM⟩
  obtain ⟨Dsys, hDsys⟩ := hD
  obtain ⟨D', hD'Q, -⟩ := lieDecomposition_exactFamily_comp hp2
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hq hΩ hcls hc2 hne Dsys
  obtain ⟨j₀, hj₀⟩ := movedComponent_eq hΩ hc2 hB hcB hc1 hbB hb1 hbc hM hMb D'
  obtain ⟨j, hj⟩ := hD'Q j₀
  have hLeq : L = (secComponentHom (normalizesLayer_exactFamily hΩ) Dsys j).range :=
    (hj₀ L hL hmov).trans hj.symm
  have hBN := modOdd_le_normalizer hp2 hq hΩ hcls hBelow hc2 hnc hB hcB hc1 hbB hb1 hbc hM hMb hL
    hmov
  subst hLeq
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ) Dsys j with hψ
  obtain ⟨htag, hdiag⟩ := hDsys j hmov
  have hker := secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ) Dsys j
  have hperf : Group.IsPerfect (compModel Dsys j).K :=
    Group.isPerfect_def.2 (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _
      (Dsys.isFundTag j) (Dsys.admissible j)).1.1
  have hexp : Dsys.exp j = f := by
    rcases Dsys.exp_eq j with h | ⟨h, -⟩
    · exact h
    · rcases htag with h' | h' <;> rw [h'] at h <;> cases h
  have h5 : 5 ≤ p ^ Dsys.exp j := by rw [hexp]; exact hq
  have hmemZ := fun x => Lemma52Proof.mem_modOdd_zpowers_iff hB hcB hc1 x
  have hself : Lemma52Proof.oddQuotSelf c ∈ modOdd c (Subgroup.zpowers c) :=
    (hmemZ _).mpr (Or.inr rfl)
  have hZcard : Nat.card (modOdd c (Subgroup.zpowers c)) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨Lemma52Proof.oddQuotSelf c, hself⟩, fun h =>
      Lemma52Proof.oddQuotSelf_ne_one hB hcB hc1 (congrArg Subtype.val h).symm, ?_⟩
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (hmemZ z).mp z.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hZB : modOdd c (Subgroup.zpowers c) ≤ modOdd c B := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
    exact ⟨k, Subgroup.zpowers_le.mpr hcB hk, rfl⟩
  have hZ : ∀ z ∈ modOdd c (Subgroup.zpowers c), ∀ y ∈ ψ.range, z * y = y * z := by
    intro z hz y _
    rcases (hmemZ z).mp hz with rfl | rfl
    · simp
    · exact (Lemma52Proof.oddQuotSelf_central c y).symm
  have hZ' : ∀ b' ∈ modOdd c B, (∀ y ∈ ψ.range, b' * y = y * b') →
      b' ∈ modOdd c (Subgroup.zpowers c) := by
    intro b' hb' hcomm
    by_contra hnot
    obtain ⟨y, hy, hne'⟩ := hmov b' hb' hnot
    exact hne' (hcomm y hy)
  exact alphaOf_inducedImage_eq_bot_of_toralDiag htag (Dsys.admissible j) hp2 h5 ψ hker
    (Lemma52Proof.modOdd_sq hB) (Lemma52Proof.card_modOdd_eq_eight hB hB8 hcB) hBN hZcard hZB hZ
    hZ' hdiag

end Vertex

end FrameVertex

end CFSG.ClassicalInvolution.Asc77

module

public import CFSG.GH74.Uniqueness.SU.SU4L183
public import CFSG.GH74.Uniqueness.SU.SU10Stmts

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

open Subgroup

theorem exists_setup18Core {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    (hrank : 3 ≤ Open.pRank 2 (S : Subgroup G)) :
    ∃ U : Subgroup G, SU4.Setup18Core S U ∧ U ≤ (S : Subgroup G) ∧ Nat.card U = 4 := by
  obtain ⟨U, hUS, hUn, hUe, hUc⟩ := SU1.exists_normal_fourGroup_of_pRank_ge_three S.isPGroup' hrank
  exact ⟨U, ⟨hsimple, hnonab, hrank, ⟨hUS, hUe, by rw [hUc]; norm_num⟩, hUn⟩, hUS, hUc⟩

theorem exists_setup18 {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hkgh : KGH G) (S : Sylow 2 G)
    (hrank : 3 ≤ Open.pRank 2 (S : Subgroup G)) :
    ∃ U : Subgroup G, SU4.Setup18 S U ∧ U ≤ (S : Subgroup G) ∧ Nat.card U = 4 := by
  obtain ⟨U, hcore, hUS, hUc⟩ := exists_setup18Core hsimple hnonab S hrank
  exact ⟨U, ⟨hcore, hkgh⟩, hUS, hUc⟩

theorem exists_hyp184Core {G : Type} [Group G] [Finite G] {S : Sylow 2 G}
    {U : Subgroup G} (hsetup : SU4.Setup18Core S U) (hgamma : gammaElem (S : Subgroup G) ≠ ⊤) :
    ∃ M, SU4.Hyp184Core S U M := by
  have h183 : SU4.Lemma183CoreStmt := SU4.lemma183_core
  by_cases hdis : ∃ E : Subgroup G, SU4.IsFour ⊤ E ∧ E ∉ SU4.compSet ⊤ U
  · obtain ⟨ha, -, -, hd⟩ := h183 G S U hsetup
    have hne : SU4.stabComp U ≠ ⊤ := by
      intro htop
      obtain ⟨g, hg⟩ := hd hdis
      exact hg (SU4.mem_stabComp.mp (by rw [htop]; exact Subgroup.mem_top g))
    obtain ⟨M, hMc, hMle⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (SU4.stabComp U)).resolve_left hne
    refine ⟨M,
      { toSetup18Core := hsetup
        gamma_ne_top := hgamma
        maximal := hMc
        gamma_le := ?_
        disconn_le := ?_ }⟩
    · intro g hg
      exact hMle (SU4.mem_stabComp.mpr (ha g hg))
    · intro _ g hg
      exact hMle (SU4.mem_stabComp.mpr hg)
  · obtain ⟨M, hMc, hMle⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (gammaElem (S : Subgroup G))).resolve_left hgamma
    exact ⟨M,
      { toSetup18Core := hsetup
        gamma_ne_top := hgamma
        maximal := hMc
        gamma_le := hMle
        disconn_le := fun h => absurd h hdis }⟩

theorem exists_hyp184 (_h183 : SU4.Lemma183Stmt) {G : Type} [Group G] [Finite G] {S : Sylow 2 G}
    {U : Subgroup G} (hsetup : SU4.Setup18 S U) (hgamma : gammaElem (S : Subgroup G) ≠ ⊤) :
    ∃ M, SU4.Hyp184 S U M := by
  obtain ⟨M, hcore⟩ := exists_hyp184Core (G := G) (S := S) (U := U) hsetup.toSetup18Core hgamma
  exact ⟨M, { toHyp184Core := hcore, kgh := hsetup.kgh }⟩

theorem exists_central_involution_sylow {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    {U : Subgroup G} (hUS : U ≤ (S : Subgroup G)) (hUc : Nat.card U = 4) :
    ∃ z : G, orderOf z = 2 ∧ ∀ s ∈ (S : Subgroup G), s * z = z * s := by
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro h
    have hU1 : U = ⊥ := le_bot_iff.mp (hUS.trans_eq h)
    rw [hU1, Subgroup.card_bot] at hUc
    omega
  obtain ⟨z, -, hz2, hz1, hzc⟩ := SU4.exists_central_involution S.isPGroup' hSne
  exact ⟨z, orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1, hzc⟩

theorem hyp21_of {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M : Subgroup G}
    (h : SU4.Hyp184 S U M) (hΓ : SU4.Concl184a S M) (hno : SU4.Concl184b M) {z : G}
    (hz : orderOf z = 2) (hzc : ∀ s ∈ (S : Subgroup G), s * z = z * s) : SU10.Hyp21 S M z :=
  { simple := h.simple, nonab := h.nonab, kgh := h.kgh, rank := h.rank,
    gamma_ne_top := h.gamma_ne_top, maximal := h.maximal, gamma_le := hΓ, no_isolated := hno,
    z_invol := hz, z_center := hzc }

end CFSG.GH74.Uniqueness.SU.SU14

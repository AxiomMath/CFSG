module

public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient

theorem isCyclic_of_pRank_le_one {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hΓ : IsPGroup p Γ) (h : CFSG.pRank p Γ ≤ 1) : IsCyclic Γ := by
  by_contra hnc
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p Γ) := ⟨hΓ⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hE : CFSG.Open.IsElemAbelian p S :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p S).1 hSel
  have h2 := CFSG.SectionRank.le_pRank hp.one_lt le_top hE hScard
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  omega

theorem pRank_le_one_of_sylow_cyclic {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Sylow p X, IsCyclic ↥(P : Subgroup X)) : CFSG.pRank p X ≤ 1 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E _ hE
  have hpE : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hEP⟩ := hpE.exists_le_sylow
  have hcycP : IsCyclic ↥(P : Subgroup X) := h P
  have hcyc : IsCyclic ↥E := by
    have : IsCyclic ↥(E.subgroupOf (P : Subgroup X)) := Subgroup.isCyclic _
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEP).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEP).surjective
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hE.2 g g.2)
  have hdvd : Nat.card E ∣ p := hord ▸ orderOf_dvd_of_pow_eq_one hgp
  rw [pow_one]
  exact Nat.le_of_dvd hp.pos hdvd

theorem isCyclic_sylow_of_pRank_le_one {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : CFSG.pRank p H ≤ 1) (P : Sylow p H) : IsCyclic ↥(P : Subgroup H) := by
  refine isCyclic_of_pRank_le_one hp hp2 P.isPGroup' ?_
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  have := CFSG.SectionRank.pRank_mono hp.one_lt (le_top : (P : Subgroup H) ≤ ⊤)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  omega

theorem pRank_le_one_of_surjective {H Q : Type*} [Group H] [Finite H] [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hH : CFSG.pRank p H ≤ 1) (f : H →* Q)
    (hf : Function.Surjective f) : CFSG.pRank p Q ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine pRank_le_one_of_sylow_cyclic hp fun P => ?_
  obtain ⟨P', rfl⟩ := Sylow.mapSurjective_surjective hf p P
  have := isCyclic_sylow_of_pRank_le_one hp hp2 hH P'
  rw [Sylow.coe_mapSurjective]
  refine isCyclic_of_surjective
    (((f.comp (P' : Subgroup H).subtype).codRestrict ((P' : Subgroup H).map f)
      fun x => ⟨x, x.2, rfl⟩) : ↥(P' : Subgroup H) →* ↥((P' : Subgroup H).map f)) ?_
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

end CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient

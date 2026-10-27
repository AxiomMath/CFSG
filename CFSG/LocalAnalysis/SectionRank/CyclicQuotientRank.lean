module

public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank

public section

namespace CFSG.SectionRank

theorem pRank_le_one_of_normal_isPGroup_cyclic_quotient
    {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    {p r : ℕ} (hp : p.Prime) (hN : IsPGroup p N) (hcyc : IsCyclic (G ⧸ N))
    (hr : r.Prime) (hrp : r ≠ p) :
    CFSG.Open.pRank r (⊤ : Subgroup G) ≤ 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hcyc
  have hcard : ¬ r ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp
      (((Nat.coprime_primes hr hp).mpr hrp).pow_right k)
  rw [← pRank_quotient_eq (p := r) N hcard]
  exact pRank_le_one_of_isCyclic hr (S := ⊤)
    (isCyclic_of_surjective (Subgroup.topEquiv).symm.toMonoidHom (MulEquiv.surjective _))

theorem pRank_le_one_of_le_normal_isPGroup_cyclic_quotient
    {X : Type*} [Group X] [Finite X] {C T : Subgroup X} (hTC : T ≤ C)
    (hTn : (T.subgroupOf C).Normal) {p r : ℕ} (hp : p.Prime) (hTp : IsPGroup p T)
    (hcyc : IsCyclic (↥C ⧸ T.subgroupOf C)) (hr : r.Prime) (hrp : r ≠ p) :
    CFSG.Open.pRank r C ≤ 1 := by
  rw [pRank_eq_pRank_top_subgroup]
  have hTp' : IsPGroup p ↥(T.subgroupOf C) :=
    IsPGroup.of_equiv hTp (Subgroup.subgroupOfEquivOfLe hTC).symm
  exact pRank_le_one_of_normal_isPGroup_cyclic_quotient hp hTp' hcyc hr hrp

theorem pRank_le_one_of_isPGroup_sup_cyclic {Y : Type*} [Group Y] [Finite Y]
    {p r : ℕ} [Fact p.Prime] (hr : r.Prime) (hpr : p ≠ r)
    {T J B : Subgroup Y} (hT : IsPGroup p T) (hJ : IsCyclic J)
    (hsup : T ⊔ J = B) (hNB : B ≤ Subgroup.normalizer (T : Set Y)) :
    CFSG.Open.pRank r B ≤ 1 := by
  have hTB : T ≤ B := hsup ▸ le_sup_left
  have hJB : J ≤ B := hsup ▸ le_sup_right
  have hTn : (T.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNB
  have hsupB : T.subgroupOf B ⊔ J.subgroupOf B = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTB hJB, hsup, Subgroup.subgroupOf_self]
  have hJsub : IsCyclic (J.subgroupOf B) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hJB)).2 hJ
  haveI : (T.subgroupOf B).Normal := hTn
  have hcyc : IsCyclic (↥B ⧸ T.subgroupOf B) :=
    CFSG.quotient_isCyclic_of_sup_cyclic_right hsupB hJsub
  exact pRank_le_one_of_le_normal_isPGroup_cyclic_quotient hTB hTn Fact.out hT hcyc hr
    (Ne.symm hpr)

end CFSG.SectionRank

module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section ReeF4Data

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_lift {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G}
    (hext : D1Extremal p P M H R) {gb : H ⧸ primeComplementCore (G := H) p}
    (hg : gb ∈ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hgN : gb ∈ Subgroup.normalizer (((R.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Set _)) :
    ∃ t : H, (t : G) ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G) ∧
      QuotientGroup.mk' (primeComplementCore (G := H) p) t = gb := by
  have hp : p.Prime := Fact.out
  have hRH : R ≤ H := hext.le_H
  have hRp : IsPGroup p R := hext.isPGroup
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  obtain ⟨k, hkX, rfl⟩ := hg
  obtain ⟨o, ho, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
    (comap_normalizer_map_le_sup hp (primeComplementCore (G := H) p)
      (primeComplementCore_coprime p) hRp.comap_subtype hgN)
  have hπo : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  have hoM : o ∈ (H ⊓ M).subgroupOf H := Subgroup.mem_subgroupOf.mpr
    ⟨o.2, hext.primeCore_le ((mem_primeComplementCore_iff_mem_glbPrimeCore p o).mp ho)⟩
  have htM : t ∈ (H ⊓ M).subgroupOf H := by
    simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ hoM) hkX
  have htN : (t : G) ∈ Subgroup.normalizer (R : Set G) := by
    have h1 : (t : G) ∈ Subgroup.normalizer
        (((R.subgroupOf H).map H.subtype : Subgroup G) : Set G) :=
      Subgroup.le_normalizer_map H.subtype ⟨t, ht, rfl⟩
    rwa [Subgroup.map_subgroupOf_eq_of_le hRH] at h1
  exact ⟨t, ⟨Subgroup.mem_subgroupOf.mp htM, htN⟩, by rw [map_mul, hπo, one_mul]⟩

omit [Finite G] in
theorem relIndex_map_dvd {G' : Type*} [Group G'] (f : G →* G') {A B : Subgroup G}
    (hAB : A ≤ B) : (A.map f).relIndex (B.map f) ∣ A.relIndex B := by
  set g : B →* B.map f := (f.comp B.subtype).codRestrict (B.map f) fun b =>
    Subgroup.mem_map_of_mem f b.2
  have hg : Function.Surjective g := by
    rintro ⟨_, ⟨b, hb, rfl⟩⟩
    exact ⟨⟨b, hb⟩, rfl⟩
  have hmap : (A.subgroupOf B).map g = (A.map f).subgroupOf (B.map f) := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨⟨a, haB⟩, ha, hax⟩
      have : x = f a := (congrArg Subtype.val hax).symm
      rw [Subgroup.mem_subgroupOf]
      exact ⟨a, Subgroup.mem_subgroupOf.mp ha, this.symm⟩
    · intro h1
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_subgroupOf.mp h1
      exact ⟨⟨a, hAB ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have := Subgroup.index_map_dvd (H := A.subgroupOf B) hg
  rwa [hmap] at this

end ReeF4Data

end CFSG.AGLEmbedding

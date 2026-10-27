module

public import CFSG.RankThree.PartOne.S12.SectionalRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace ConstrainedNormalCoreNontrivial

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le {J : Subgroup G} : CFSG.Open.pCoreOf 2 J ≤ J := Subgroup.map_subtype_le _

theorem normalizer_le_normalizer_pCoreOf (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := by
  have le_pCoreOf_of_normal {X N : Subgroup G} (hNX : N ≤ X) (hN : (N.subgroupOf X).Normal)
      (hp : IsPGroup 2 ↥N) : N ≤ CFSG.Open.pCoreOf 2 X := by
    have h1 : N.subgroupOf X ≤ CFSG.Open.pCore 2 X :=
      le_sSup ⟨hN, hp.comap_subtype⟩
    intro x hx
    exact ⟨⟨x, hNX hx⟩, h1 hx, rfl⟩
  intro g hg
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ p ∈ CFSG.Open.pCoreOf 2 X,
      g * p * g⁻¹ ∈ CFSG.Open.pCoreOf 2 X := by
    intro g hg p hp
    set P := CFSG.Open.pCoreOf 2 X with hP
    have hPX : P ≤ X := pCoreOf_le
    let Q : Subgroup G := P.map (MulAut.conj g).toMonoidHom
    have hQX : Q ≤ X := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hg y).1 (hPX hy)
    have hQp : IsPGroup 2 ↥Q :=
      (CFSG.RankThree.PartOne.SectionalRank.isPGroup_pCoreOf 2 X).map (MulAut.conj g).toMonoidHom
    have hQn : (Q.subgroupOf X).Normal := by
      constructor
      intro n hn x
      obtain ⟨y, hy, hyn⟩ := hn
      have hgx : g⁻¹ * (x : G) * g ∈ X := by
        have hginv : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ hg
        have := (Subgroup.mem_normalizer_iff.1 hginv (x : G)).1 x.2
        simpa using this
      have hQ := CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 X hgx
      have hy' : (g⁻¹ * (x : G) * g) * y * (g⁻¹ * (x : G) * g)⁻¹ ∈ P := by
        have := (Subgroup.mem_normalizer_iff.1 hQ y).1 hy
        exact this
      refine ⟨_, hy', ?_⟩
      have hyn' : g * y * g⁻¹ = (n : G) := by simpa using hyn
      show g * ((g⁻¹ * (x : G) * g) * y * (g⁻¹ * (x : G) * g)⁻¹) * g⁻¹ = (x : G) * n * (x : G)⁻¹
      rw [← hyn']
      group
    exact le_pCoreOf_of_normal hQX hQn hQp ⟨p, hp, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => key g hg p hp, fun hp => ?_⟩
  have hginv : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ hg
  simpa [mul_assoc] using key g⁻¹ hginv _ hp

end ConstrainedNormalCoreNontrivial

end CFSG.LocalAnalysis.RankThreeUC

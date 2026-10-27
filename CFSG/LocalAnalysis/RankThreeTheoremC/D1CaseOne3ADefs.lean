module

public import CFSG.LocalAnalysis.AGLEmbedding.D1CompCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G]

structure D1OneSmall3Data (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  cfg : D1ComponentConfig3 p P M H R Rbar
  comp : IsComponentOf K ⊤
  center : Subgroup.center K = ⊥
  noncyclic : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
    Subgroup (H ⧸ primeComplementCore (G := H) p))
  z : ∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
    z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  small : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmall3Data.toCore (hd : D1OneSmall3Data p P M H R Rbar K) :
    D1CompCore p P M H R Rbar K :=
  ⟨hd.cfg.ext.toD1Escape, hd.cfg.rbar, hd.cfg.red, hd.comp, hd.center, hd.noncyclic, hd.z⟩

theorem D1OneSmall3Data.exists_czElt (hd : D1OneSmall3Data p P M H R Rbar K) :
    ∃ z : G, D1SmallCZElt p H R K z ∧ z ∉ d1LiftX p H R K := by
  have hp := hd.cfg.red.prime
  obtain ⟨zb, hzR, hzK, hzp, hzc⟩ := hd.z
  rw [hd.cfg.rbar] at hzR
  obtain ⟨r, hr, rfl⟩ := hzR
  refine ⟨(r : G), ⟨hr, ?_, r.2, hzc⟩, ?_⟩
  · have hSp : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
    have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp
      (primeComplementCore (G := H) p)
      (hp.coprime_iff_not_dvd.mp (primeComplementCore_coprime p)) _ hSp
    set f := (QuotientGroup.mk' (primeComplementCore (G := H) p)).subgroupMap (R.subgroupOf H)
    have h1 : orderOf (f ⟨r, hr⟩) = orderOf (⟨r, hr⟩ : R.subgroupOf H) :=
      orderOf_injective f hinj _
    have h2 : orderOf ((f ⟨r, hr⟩ : Subgroup.map _ (R.subgroupOf H)) :
        H ⧸ primeComplementCore (G := H) p) = orderOf (f ⟨r, hr⟩) := Subgroup.orderOf_coe _
    have h3 : orderOf ((⟨r, hr⟩ : R.subgroupOf H) : H) = orderOf (⟨r, hr⟩ : R.subgroupOf H) :=
      Subgroup.orderOf_coe _
    have h4 : orderOf (r : G) = orderOf r := Subgroup.orderOf_coe r
    rw [h4, ← hzp]
    change orderOf ((⟨r, hr⟩ : R.subgroupOf H) : H) = orderOf ((f ⟨r, hr⟩ :
      Subgroup.map _ (R.subgroupOf H)) : H ⧸ primeComplementCore (G := H) p)
    rw [h3, h2, h1]
  · rintro ⟨x', ⟨-, hxK⟩, hx'⟩
    exact hzK (by rw [← Subtype.ext hx']; exact hxK)

end Data

end CFSG.LocalAnalysis.RankThreeTheoremC

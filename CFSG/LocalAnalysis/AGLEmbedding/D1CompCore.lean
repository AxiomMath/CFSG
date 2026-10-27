module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

structure D1CompCore (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  esc : D1Escape p P M H R
  rbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))
  red : ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
    (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
  comp : IsComponentOf K ⊤
  center : Subgroup.center K = ⊥
  noncyclic : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
    Subgroup (H ⧸ primeComplementCore (G := H) p))
  z : ∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
    z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.toCore (hd : D1OneSmallData p P M H R Rbar K) :
    D1CompCore p P M H R Rbar K :=
  ⟨hd.cfg.ext.toD1Escape, hd.cfg.rbar, hd.cfg.red, hd.comp, hd.center, hd.noncyclic, hd.z⟩

theorem D1OneLieData.toCore (hd : D1OneLieData p P M H R Rbar K) :
    D1CompCore p P M H R Rbar K :=
  ⟨hd.cfg.ext.toD1Escape, hd.cfg.rbar, hd.cfg.red, hd.comp, hd.center, hd.noncyclic, hd.z⟩

theorem D1CompCore.map_d1LiftX_eq_inf (hd : D1CompCore p P M H R Rbar K) :
    ((d1LiftX p H R K).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
  rw [map_d1LiftX, hd.rbar]

end CFSG.AGLEmbedding

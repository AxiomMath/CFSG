module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Uni
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L515P

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem sec5_pockets_eq (h514 : Asc82Lemma514) (hF2 : Asc82FactPocketsTwo)
    (hb : Asc82Lemma515b) (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {i j l m : Fin 4} (hij : i ≠ j) (hlm : l ≠ m) (hli : l ≠ i) (hlj : l ≠ j) (hmi : m ≠ i)
    (hmj : m ≠ j) {d : G} (hd2 : orderOf d = 2) (hdz : d ≠ z)
    (hd : d ∈ Kfam5 K₁ K₂ h i ⊔ Kfam5 K₁ K₂ h j) {S'' : Subgroup G} {r'' : G}
    {B'' A'' P₁ P₂ : Subgroup G} {h'' : G}
    (c'' : Sec5HCtx G d (layerC5 d) S'' z r'' B'' A'' P₁ P₂ h'') :
    (P₁ = Kfam5 K₁ K₂ h l ∧ P₂ = Kfam5 K₁ K₂ h m) ∨
      (P₁ = Kfam5 K₁ K₂ h m ∧ P₂ = Kfam5 K₁ K₂ h l) := by
  have hz2 : orderOf z = 2 := c.pocket.1
  have hdΔ : d ∈ Delta5 z (Gamma5 K₁ K₂ h) :=
    sec5_mem_delta_of_pair h514 c hij hd2 hdz hd
  have hKl : Kfam5 K₁ K₂ h l ∈ Gamma5 K₁ K₂ h := by
    rw [sec5b517_gamma_eq]; exact Set.mem_range_self l
  have hKm : Kfam5 K₁ K₂ h m ∈ Gamma5 K₁ K₂ h := by
    rw [sec5b517_gamma_eq]; exact Set.mem_range_self m
  have hne : Kfam5 K₁ K₂ h l ≠ Kfam5 K₁ K₂ h m :=
    (sec5b517_quad h514 c).ne hlm
  have hp : Sec5Pair (Kfam5 K₁ K₂ h l) (Kfam5 K₁ K₂ h m) z :=
    sec5_pair_of_gamma h514 c hKl hKm hne
  have hKd : IsKOf (Gamma5 K₁ K₂ h) d (Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m) :=
    (sec5_kOf_iff h514 c hij hlm hli hlj hmi hmj hd2 hdz hd
      (Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m)).mpr rfl
  have hM' : Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m =
      twoRes (centralizer ({z} : Set G) ⊓ layerC5 d) :=
    (hb G t L S z r B A K₁ K₂ h c d hdΔ).2 (Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m) hKd
  have hM : Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m =
      twoRes (layerC5 d ⊓ centralizer ({z} : Set G)) := by
    rw [hM', inf_comm]
  have hle : P₁ ⊔ P₂ ≤ Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m :=
    (c''.prod.trans hM.symm).le
  exact sec5_pair_unique hF2 hz2 hp hM c''.pocket₁ c''.pocket₂ c''.ne hle

end CFSG.OddStandard.SmallF3.Omega

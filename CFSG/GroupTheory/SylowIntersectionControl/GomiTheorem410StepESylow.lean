module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEBar

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne

variable {Ω : Type} [Group Ω] [Finite Ω] {G : Subgroup Ω}

omit [Finite Ω] in
private lemma subgroupOf_map_subtype_eq_esyl {K : Subgroup ↥G} :
    (K.map G.subtype).subgroupOf G = K := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := G.subtype_injective hyx
    rwa [this] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [Finite Ω] in
private lemma autOn_map_subtype_eq_map_gomiBar_esyl {K : Subgroup ↥G} :
    autOn (K.map G.subtype) (gomiV G) =
      (K.map (gomiBar G)).map (autOn G (gomiV G)).subtype := by
  have hKG : K.map G.subtype ≤ G := Subgroup.map_subtype_le K
  calc autOn (K.map G.subtype) (gomiV G)
      = (gomiBarOf G (K.map G.subtype)).map (autOn G (gomiV G)).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (AutOn.autOn_mono hKG)).symm
    _ = (((K.map G.subtype).subgroupOf G).map (gomiBar G)).map
          (autOn G (gomiV G)).subtype := by rw [gomiBarOf_eq_map hKG]
    _ = (K.map (gomiBar G)).map (autOn G (gomiV G)).subtype := by
        rw [subgroupOf_map_subtype_eq_esyl]

private lemma isSylowTwoOf_map_subtype_esyl (P : Sylow 2 ↥G) :
    IsSylowTwoOf (P.1.map G.subtype) G := by
  refine ⟨Subgroup.map_subtype_le P.1, P.isPGroup'.map G.subtype, ?_⟩
  rw [subgroupOf_map_subtype_eq_esyl]
  exact Sylow.not_dvd_index P

theorem exists_isSylowTwoOf_autOn_eq {S : Subgroup (MulAut ↥(gomiV G))}
    (hS : IsSylowIn 2 S (autOn G (gomiV G))) :
    ∃ T : Subgroup Ω, IsSylowTwoOf T G ∧ autOn T (gomiV G) = S := by
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective (p := 2) (f := gomiBar G)
    (gomiBar_surjective G) hS.toSylow
  refine ⟨P.1.map G.subtype, isSylowTwoOf_map_subtype_esyl P, ?_⟩
  rw [autOn_map_subtype_eq_map_gomiBar_esyl]
  have hmap : P.1.map (gomiBar G) = S.subgroupOf (autOn G (gomiV G)) := by
    have h := congrArg (fun Q : Sylow 2 ↥(autOn G (gomiV G)) =>
      (Q : Subgroup ↥(autOn G (gomiV G)))) hP
    simpa using h
  rw [hmap, Subgroup.map_subgroupOf_eq_of_le hS.le]

end CFSG.GroupTheory

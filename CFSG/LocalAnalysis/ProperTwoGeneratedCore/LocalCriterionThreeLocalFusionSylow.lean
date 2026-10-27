module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion

universe v

variable {G : Type v} [Group G]

@[expose] def centralizerSylowImage (u : G)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G))) : Subgroup G :=
  (T : Subgroup (Subgroup.centralizer ({u} : Set G))).map
    (Subgroup.centralizer ({u} : Set G)).subtype

theorem centralizerSylowImage_le (u : G)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G))) :
    centralizerSylowImage u T ≤ Subgroup.centralizer ({u} : Set G) :=
  Subgroup.map_subtype_le _

theorem centralizerSylowImage_isPGroup (u : G)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G))) :
    IsPGroup 2 (centralizerSylowImage u T) :=
  T.isPGroup'.map (Subgroup.centralizer ({u} : Set G)).subtype

theorem involution_mem_centralizerSylowImage {u : G} (hu : orderOf u = 2)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G))) :
    u ∈ centralizerSylowImage u T := by
  let C := Subgroup.centralizer ({u} : Set G)
  have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl u)
  let uC : C := ⟨u, huC⟩
  have huZ : uC ∈ Subgroup.center C := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp x.property
  have hzZ : Subgroup.zpowers uC ≤ Subgroup.center C :=
    Subgroup.zpowers_le.mpr huZ
  let : (Subgroup.zpowers uC).Normal := Subgroup.normal_of_le_center hzZ
  have huCorder : orderOf uC = 2 := (Subgroup.orderOf_coe uC).symm.trans hu
  have hcyclic : IsPGroup 2 (Subgroup.zpowers uC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huCorder]; norm_num)
  have huT : uC ∈ (T : Subgroup C) :=
    (hcyclic.le_sylow_of_normal T) (Subgroup.mem_zpowers uC)
  exact Subgroup.mem_map_of_mem C.subtype huT

theorem involution_centralizes_centralizerSylowImage (u : G)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G))) :
    ∀ x ∈ centralizerSylowImage u T, Commute u x := by
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (centralizerSylowImage_le u T hx)).symm

theorem centralizerSylowImage_maximal (u : G)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hTQ : centralizerSylowImage u T ≤ Q)
    (hQC : Q ≤ Subgroup.centralizer ({u} : Set G)) :
    Q = centralizerSylowImage u T := by
  let C := Subgroup.centralizer ({u} : Set G)
  have hQsub : IsPGroup 2 (Q.subgroupOf C) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  have hTsub : (T : Subgroup C) ≤ Q.subgroupOf C := by
    intro x hx
    exact hTQ (Subgroup.mem_map_of_mem C.subtype hx)
  have heq := T.is_maximal' hQsub hTsub
  have hmap := congrArg (fun R : Subgroup C => R.map C.subtype) heq
  rw [Subgroup.map_subgroupOf_eq_of_le hQC] at hmap
  exact hmap

theorem centralizerSylowImage_ambient_sylow [Finite G] (u : G)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (hnormalizer : Subgroup.normalizer (centralizerSylowImage u T : Set G) ≤
      Subgroup.centralizer ({u} : Set G)) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = centralizerSylowImage u T := by
  obtain ⟨S, hTS⟩ := (centralizerSylowImage_isPGroup u T).exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : centralizerSylowImage u T < (S : Subgroup G) :=
    lt_of_le_of_ne hTS (Ne.symm hne)
  have hgrowth :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime.pSubgroup_lt_normalizer_intersection
      2 Nat.prime_two (centralizerSylowImage u T) (S : Subgroup G) S.isPGroup' hlt
  let Q := (S : Subgroup G) ⊓ Subgroup.normalizer (centralizerSylowImage u T : Set G)
  have hQp : IsPGroup 2 Q := S.isPGroup'.of_injective (Subgroup.inclusion inf_le_left)
    (Subgroup.inclusion_injective _)
  have hQT := centralizerSylowImage_maximal u T Q hQp hgrowth.le
    (inf_le_right.trans hnormalizer)
  exact (ne_of_lt hgrowth) hQT.symm

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion

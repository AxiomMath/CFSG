module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSettingX1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15YstarBot
public import CFSG.Quasithin.Background.G2
import CFSG.LocalAnalysis.RankThreeUC.GN15JOutSolvSite

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin
open CFSG.Open CFSG.AGLEmbedding
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem gnV_subgroupOf_map_le {T H : Subgroup X} (hT : T ≤ H) :
    (gnV (T.subgroupOf H)).map H.subtype ≤ gnV T := by
  haveI hVn : (gnV T).Normal := Subgroup.normalClosure_normal
  rw [Subgroup.map_le_iff_le_comap]
  change Subgroup.normalClosure (CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf H) : Set ↥H) ≤
    (gnV T).comap H.subtype
  refine Subgroup.normalClosure_le_normal ?_
  intro x hx
  change (x : X) ∈ gnV T
  have hxT' : x ∈ T.subgroupOf H :=
    (CFSG.Quasithin.omegaOneCenterOf_le (T.subgroupOf H)) hx
  have hxT : (x : X) ∈ T := Subgroup.mem_subgroupOf.mp hxT'
  have hxcentH : ∀ y ∈ T.subgroupOf H, y * x = x * y :=
    fun y hy => CFSG.Quasithin.mem_centralizer_of_mem_omegaOneCenterOf hx hy
  have hxcent : ∀ y ∈ T, y * (x : X) = (x : X) * y := by
    intro y hy
    simpa using congrArg Subtype.val (hxcentH ⟨y, hT hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
  have hx2 : (x : X) ^ 2 = 1 := by
    simpa using congrArg Subtype.val (CFSG.Quasithin.sq_eq_one_of_mem_omegaOneCenterOf hx)
  exact Subgroup.subset_normalClosure (CFSG.Quasithin.mem_omegaOneCenterOf hxT hxcent hx2)

theorem gnC_subgroupOf_le_gnC_subgroupOf {T H : Subgroup X} (hT : T ≤ H) :
    (gnC T).subgroupOf H ≤ gnC (T.subgroupOf H) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [gnC, Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  apply Subtype.ext
  exact hx (y : X) (gnV_subgroupOf_map_le hT (Subgroup.mem_map_of_mem H.subtype hy))

theorem isSolvable_restrictedQuotient {T H : Subgroup X} (hT : T ≤ H)
    (hsolvY : Group.IsSolvable ↥(gnImg T H)) :
    Group.IsSolvable (↥H ⧸ gnC (T.subgroupOf H)) := by
  classical
  let K : Subgroup ↥H := (gnC T).subgroupOf H
  let C' : Subgroup ↥H := gnC (T.subgroupOf H)
  have hKC : K ≤ C' := gnC_subgroupOf_le_gnC_subgroupOf hT
  let φ : ↥H →* ↥(gnImg T H) :=
    ((QuotientGroup.mk' (gnC T)).comp H.subtype).codRestrict (gnImg T H)
      (fun x => Subgroup.mem_map_of_mem (QuotientGroup.mk' (gnC T)) x.2)
  have hφker : φ.ker = K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (x : X)).mp (congrArg Subtype.val hx)
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : X)).mpr hx
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hxH, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hxH⟩, Subtype.ext hxy⟩
  haveI : Group.IsSolvable ↥(gnImg T H) := hsolvY
  have hsolvK : Group.IsSolvable (↥H ⧸ K) :=
    Group.isSolvable_of_surjective
      (f := (QuotientGroup.liftEquiv (N := K) (φ := φ) hφsurj hφker.symm).symm.toMonoidHom)
      (MulEquiv.surjective _)
  haveI : Group.IsSolvable (↥H ⧸ K) := hsolvK
  exact Group.isSolvable_of_surjective
    (f := QuotientGroup.map K C' (MonoidHom.id ↥H) hKC)
    (QuotientGroup.map_surjective_of_surjective K C' (MonoidHom.id ↥H)
      QuotientGroup.mk_surjective hKC)

theorem borelPre_factors_of_isSolvable_gnImg (hX : GNSetting X T) (hGood : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)}
    (hNB : ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False)
    (hsolvY : Group.IsSolvable ↥(gnImg T (borelPre T Ls))) :
    ((Subgroup.centralizer (T₁.subgroupOf (borelPre T Ls) : Set ↥(borelPre T Ls)) :
        Set ↥(borelPre T Ls)) *
      (Subgroup.normalizer (T₂.subgroupOf (borelPre T Ls) : Set ↥(borelPre T Ls)) :
        Set ↥(borelPre T Ls))) = Set.univ := by
  have hSet := gnSetting_borelPre_of_noXBlock hX hNB
  have hquot := isSolvable_restrictedQuotient (t_le_borelPre hX) hsolvY
  have hfac := hGood.factorSub (borelPre T Ls) (t_le_borelPre hX) hSet
    (GN15.jOutCentralAt_of_isSolvable_quotient hquot)
  have hY0 := Y0_eq_gnC_of_isSolvable_quotient
    (T := T.subgroupOf (borelPre T Ls))
    (T₁ := T₁.subgroupOf (borelPre T Ls))
    (T₂ := T₂.subgroupOf (borelPre T Ls)) hSet hquot
  have hC : (gnC (T.subgroupOf (borelPre T Ls)) : Subgroup ↥(borelPre T Ls)) ≤
      Subgroup.centralizer (T₁.subgroupOf (borelPre T Ls) : Set ↥(borelPre T Ls)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
      (gnC_le_centralizer_T1 hX hGood.pair
        (Subgroup.mem_map_of_mem (Subgroup.subtype (borelPre T Ls)) hy))
      (z : X) (Subgroup.mem_subgroupOf.mp hz))
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨a, ha, y, hy, b, hb, rfl⟩ := hfac x
  rw [hY0] at hy
  exact Set.mul_mem_mul (mul_mem ha (hC hy)) hb

end CFSG.LocalAnalysis.RankThreeUC.S15

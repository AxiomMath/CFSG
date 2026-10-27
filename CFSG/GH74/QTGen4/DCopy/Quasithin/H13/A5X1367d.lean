module

public import CFSG.Quasithin.H13.A5X1367d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem isSylowTwoOf_Tv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) :
    IsSylowTwoOf S.Tv (Subgroup.centralizer ({S.v12} : Set G)) :=
  S.isSylowTwoOf_centralizer_F4 h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1

theorem isTwoReducedIn_Uv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    IsTwoReducedIn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv := by
  have hsyl := S.isSylowTwoOf_Tv_F4 h1222 h517
  exact isTwoReducedIn_conjClosure_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hF S.V1_le_omega_Tv

theorem elemAbelian_Uv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    IsElemAbelian 2 S.Uv :=
  (S.isTwoReducedIn_Uv_F4 h1222 h517 hF).2.2.1

theorem pCoreOf_GvS_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    pCoreOf 2 (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) = ⊥ :=
  Setup.pCoreOf_autOn_eq_bot (S.isTwoReducedIn_Uv_F4 h1222 h517 hF)

theorem Uv_le_Tv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    S.Uv ≤ S.Tv := by
  have hsyl := S.isSylowTwoOf_Tv_F4 h1222 h517
  obtain ⟨hUc, -⟩ :=
    conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hF S.V1_le_omega_Tv
  exact hUc.trans (inf_le_left.trans (pCoreOf_two_le_of_isSylowTwoOf hsyl))

theorem pCoreOf_Gv_ne_bot_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    pCoreOf 2 (Subgroup.centralizer ({S.v12} : Set G)) ≠ ⊥ := by
  have hsyl := S.isSylowTwoOf_Tv_F4 h1222 h517
  obtain ⟨hUc, -⟩ :=
    conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hF S.V1_le_omega_Tv
  intro h
  have hz : S.z ∈ pCoreOf 2 (Subgroup.centralizer ({S.v12} : Set G)) :=
    (hUc (S.z_mem_Uv)).1
  rw [h, Subgroup.mem_bot] at hz
  exact S.z_ne_one hz

theorem sqtkGroup_Gv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    SQTKGroup ↥(Subgroup.centralizer ({S.v12} : Set G)) :=
  sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian
    (S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hF)

theorem isSylowTwoOf_TvS_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) :
    IsSylowTwoOf (autOn S.Tv S.Uv) (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) :=
  Setup.isSylowTwoOf_autOn (S.isSylowTwoOf_Tv_F4 h1222 h517) S.Gv_le_normalizer_Uv

theorem isFFStarOffender_of_mem_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {A : Subgroup G} (hA : IsFFOffender S.Tv S.Uv A) :
    haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv_F4 h1222 h517 hF).1
    IsFFStarOffender (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) (autOn A S.Uv) := by
  have hUe := S.elemAbelian_Uv_F4 h1222 h517 hF
  have hUT := S.Uv_le_Tv_F4 h1222 h517 hF
  have hTN : S.Tv ≤ Subgroup.normalizer (S.Uv : Set G) := S.Tv_le_Gv.trans S.Gv_le_normalizer_Uv
  have h1 := offenderImages_isFFStarOffender hUe hUT hTN ⟨A, hA, rfl⟩
  exact ⟨h1.1.trans (S.autOn_le_GvS S.Tv_le_Gv), h1.2.1, h1.2.2.1, h1.2.2.2⟩

theorem JGv_eq_ffJ_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv_F4 h1222 h517 hF).1
    S.JGv = ffJ S.JGv := by
  have : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv_F4 h1222 h517 hF).1
  refine le_antisymm ?_ (B6.ffJ_le _)
  refine iSup₂_le fun A hA => iSup₂_le fun g hg => ?_
  have h1 := S.isFFStarOffender_of_mem_F4 h1222 h517 hF hA
  have h2 := B6.isFFStarOffender_conjSub h1 hg
  have h3 := InternalSec.isFFStarOffender_of_le h2 (S.conjSub_le_JGv hA hg)
  exact le_iSup₂_of_le (f := fun B (_ : IsFFStarOffender S.JGv B) => B) _ h3 le_rfl

theorem pCoreOf_JGv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    pCoreOf 2 S.JGv = ⊥ := by
  have h := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 S.JGv
    (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) S.JGv_le_GvS
    ((Subgroup.normal_subgroupOf_iff_le_normalizer S.JGv_le_GvS).2 S.GvS_le_normalizer_JGv)
  rw [S.pCoreOf_GvS_F4 h1222 h517 hF] at h
  exact le_bot_iff.1 h

theorem b53Hyp_JGv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv_F4 h1222 h517 hF).1
    B53Hyp S.JGv := by
  have : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv_F4 h1222 h517 hF).1
  set Y := Subgroup.centralizer ({S.v12} : Set G) with hY
  set X := autOn Y S.Uv with hX
  set J := S.JGv with hJ
  have hJX : J ≤ X := S.JGv_le_GvS
  have hYW : Y ≤ Subgroup.normalizer (S.Uv : Set G) := S.Gv_le_normalizer_Uv
  set ρ := InternalSec.autOnHom hYW with hρ
  set H : Subgroup ↥Y := (J.subgroupOf X).comap ρ with hH
  let f : ↥H →* ↥J :=
    { toFun := fun h => ⟨((ρ (h : ↥Y) : ↥X) : MulAut ↥S.Uv), h.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    rintro ⟨j, hj⟩
    obtain ⟨y, hy⟩ := InternalSec.autOnHom_surjective hYW ⟨j, hJX hj⟩
    refine ⟨⟨y, ?_⟩, ?_⟩
    · show ρ y ∈ J.subgroupOf X
      rw [Subgroup.mem_subgroupOf, hy]
      exact hj
    · apply Subtype.ext
      show ((ρ y : ↥X) : MulAut ↥S.Uv) = j
      rw [hy]
  refine ⟨S.pCoreOf_JGv_F4 h1222 h517 hF, S.JGv_eq_ffJ_F4 h1222 h517 hF, ↥H, inferInstance,
    inferInstance, f.ker, inferInstance,
    InternalSec.sqtkGroup_subgroup (S.sqtkGroup_Gv_F4 h1222 h517 hF) H,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

theorem b56Cases_JGv_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (h56 : AsB56) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (hJ : ¬ thompsonJ S.Tv ≤ Subgroup.centralizer (S.Uv : Set G)) :
    haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv_F4 h1222 h517 hF).1
    B56Case1 S.JGv ∨ B56Case2 S.JGv ∨ B56Case3 S.JGv ∨ B56Case4 S.JGv ∨ B56Case5 S.JGv := by
  have hUe := S.elemAbelian_Uv_F4 h1222 h517 hF
  have : IsMulCommutative ↥S.Uv := hUe.1
  have hV : ∀ v : ↥S.Uv, v ^ 2 = 1 := fun v =>
    Subtype.ext (by rw [Subgroup.coe_pow, hUe.2 _ v.2, Subgroup.coe_one])
  exact h56 ↥S.Uv hV _ (S.JGv_ne_bot hJ) (S.b53Hyp_JGv_F4 h1222 h517 hF)

end Setting

end CFSG.Quasithin.H13.A5

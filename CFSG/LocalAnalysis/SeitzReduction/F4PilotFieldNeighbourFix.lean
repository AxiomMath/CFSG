module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)

section Fix


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

omit
  [Finite G] in
theorem commutator_neighbourLeviG_X [Finite K] [CharP K 2] (e : L ≃* adjointGroup .F4 K) :
    ⁅neighbourLeviG e .X, neighbourLeviG e .X⁆ = neighbourLeviG e .X := by
  have hCp : ⁅C3Levi K, C3Levi K⁆ = C3Levi K := isPerfect_iff.mp isQuasisimple_C3Levi.1
  change ⁅((C3Levi K).map e.symm.toMonoidHom).map L.subtype,
    ((C3Levi K).map e.symm.toMonoidHom).map L.subtype⁆ =
      ((C3Levi K).map e.symm.toMonoidHom).map L.subtype
  rw [← map_commutator, ← map_commutator, hCp]

theorem perfectCore_neighbourCore_inf_centralizer_X {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) :
    perfectCore (neighbourCore e .X ⊓ centralizer ({t} : Set G)) =
      modelToG e ((AmalgamNeighbour.X.levi K).map (adjointGroup .F4 K).subtype) := by
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  rw [modelToG_map_subtype_levi]
  set A : Subgroup (adjointGroup .F4 K) := (torusLineR K).subgroupOf (adjointGroup .F4 K) with hA
  set X : Subgroup G := neighbourTorusG e .X with hXdef
  set D : Subgroup G := neighbourLeviG e .X with hDdef
  have hX : X = (A.map e.symm.toMonoidHom).map L.subtype := rfl
  have hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  have hDperf : ⁅D, D⁆ = D := commutator_neighbourLeviG_X e
  have hDE : D ≤ neighbourCore e .X := by
    have h1 := modelToG_le_neighbourCore e (levi_le_centralizer_torus (K := K) .X)
      (by rw [modelToG_map_subtype_levi]; exact hDperf)
    rwa [modelToG_map_subtype_levi] at h1
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hDE hDt) hDperf)
  set P := perfectCore (neighbourCore e .X ⊓ centralizer ({t} : Set G)) with hPdef
  have hP : ⁅P, P⁆ = P := CFSG.Quasithin.perfectCore_perfect _
  have hPt : P ≤ centralizer ({t} : Set G) := (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hPL : P ≤ L := std_perfect_le hw.standard (isSolvable_outer_of_mulEquiv_F4 e) htC
    hw.orderOf_eq hP hPt
  have hPX : P ≤ centralizer (X : Set G) :=
    (CFSG.Quasithin.perfectCore_le _).trans
      (inf_le_left.trans (centralizerPerfectCore_le_centralizer _))
  have hPLX : P ≤ L ⊓ centralizer (X : Set G) := le_inf hPL hPX
  rw [hX, inf_centralizer_map_symm, centralizer_torusLineR_eq hq, Subgroup.map_sup,
    Subgroup.map_sup, ← hX, ← hDe] at hPLX
  have hXD : X ≤ centralizer (D : Set G) := by
    rw [hX, hDe]
    exact le_centralizer_iff.mp (map_map_symm_le_centralizer e torusLineR_subgroupOf_le_centralizer)
  have hXX : X ≤ centralizer (X : Set G) := by
    rw [hX]
    exact map_map_symm_le_centralizer e torusLineR_subgroupOf_le_centralizer_self
  have hXsolv : Group.IsSolvable X := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (mem_centralizer_iff.1 (hXX b.2) a a.2)
  exact perfect_le_of_le_sup (hXD.trans (centralizer_le_normalizer _)) hXsolv hP
    (by rw [sup_comm]; exact hPLX)

theorem perfectCore_neighbourCore_inf_centralizer_Y {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) :
    perfectCore (neighbourCore e .Y ⊓ centralizer ({t} : Set G)) =
      modelToG e ((AmalgamNeighbour.Y.levi K).map (adjointGroup .F4 K).subtype) := by
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hw.card_eq
  rw [neighbourCore_Y_eq_X, modelToG_levi_Y_eq_X]
  exact perfectCore_neighbourCore_inf_centralizer_X hw hf _

theorem perfectCore_neighbourCore_inf_centralizer_eq {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X') :
    perfectCore (neighbourCore e N ⊓ centralizer ({t} : Set G)) =
      modelToG e ((N.levi K).map (adjointGroup .F4 K).subtype) := by
  cases N
  · exact perfectCore_neighbourCore_inf_centralizer_X hw hf e
  · exact perfectCore_neighbourCore_inf_centralizer_Y hw hf e
  · exact absurd rfl hN

end Fix

end CFSG.SeitzReduction.F4Pilot

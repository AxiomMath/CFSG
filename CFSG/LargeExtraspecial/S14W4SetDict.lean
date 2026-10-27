module

public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

theorem Setting.clSub_zpowers_z {X : Type*} [Group X] (S : Setting X) :
    S.clSub (zpowers S.z) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  have hv' : ∃ x ∈ zpowers S.z, x ∈ S.QG ∧ S.cl x = v := S.mem_clSub_iff.mp hv
  cases hv' with
  | intro x hx =>
    cases hx with
    | intro hxz hx =>
      cases hx with
      | intro hxQ hxv =>
        subst hxv
        rcases (Setting.mem_zpowers_iff_of_mul_self S.z_mul_z).mp hxz with h1 | h1
        · subst h1
          exact S.cl_one
        · subst h1
          exact S.cl_z

theorem Setting.clSub_QG {X : Type*} [Group X] (S : Setting X) : S.clSub S.QG = ⊤ :=
  (congrArg S.clSub S.clPre_top.symm).trans (S.clSub_clPre ⊤)

namespace S14.W4Dict

variable {X Y : Type*} [Group X] [Group Y] (T : Setting X) (ι : X →* Y)

@[expose] def IsInv (R : Subgroup X) (W : Submodule (ZMod 2) T.Qt) [Finite X] : Prop :=
  ∀ r : T.M, (r : X) ∈ R → ∀ v ∈ W, ((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v ∈ W

@[expose] noncomputable def DW (W : Submodule (ZMod 2) T.Qt) : Subgroup Y := (T.clPre W).map ι

@[expose] noncomputable def WU (U : Subgroup Y) : Submodule (ZMod 2) T.Qt :=
  T.clSub (U.comap ι)

structure Hyp (N R : Subgroup Y) (t : Y) : Prop where
  inj : Function.Injective ι
  z_eq : ι T.z = t
  mem_QG : ∀ x : X, x ∈ T.QG ↔ ι x ∈ N
  N_le : N ≤ ι.range
  R_lift : ∀ y ∈ R, ∃ x : X, x ∈ T.M ∧ ι x = y

variable {T ι} {N R : Subgroup Y} {t : Y} (H : Hyp T ι N R t)
include H

theorem DW_le (W : Submodule (ZMod 2) T.Qt) : DW T ι W ≤ N := by
  intro y hy
  have hy' : ∃ x, x ∈ T.clPre W ∧ ι x = y := Subgroup.mem_map.mp hy
  cases hy' with
  | intro x hx => exact hx.2 ▸ (H.mem_QG x).mp hx.1.1

theorem zpowers_le_DW (W : Submodule (ZMod 2) T.Qt) : zpowers t ≤ DW T ι W :=
  zpowers_le.mpr (H.z_eq ▸ Subgroup.mem_map_of_mem ι (T.z_mem_clPre W))

theorem comap_DW (W : Submodule (ZMod 2) T.Qt) : (DW T ι W).comap ι = T.clPre W :=
  Subgroup.comap_map_eq_self_of_injective H.inj _

theorem clSub_comap_DW (W : Submodule (ZMod 2) T.Qt) : T.clSub ((DW T ι W).comap ι) = W :=
  (congrArg T.clSub (comap_DW H W)).trans (T.clSub_clPre W)

theorem comap_zpowers : (zpowers t).comap ι = zpowers T.z := by
  have e : (zpowers T.z).map ι = zpowers t := (MonoidHom.map_zpowers ι T.z).trans (H.z_eq ▸ rfl)
  exact (congrArg (Subgroup.comap ι) e.symm).trans
    (Subgroup.comap_map_eq_self_of_injective H.inj _)

theorem comap_N : N.comap ι = T.QG := by
  ext x
  exact (H.mem_QG x).symm

theorem eq_bot_of_DW_eq {W : Submodule (ZMod 2) T.Qt} (hD : DW T ι W = zpowers t) : W = ⊥ :=
  (clSub_comap_DW H W).symm.trans <|
    (congrArg (fun D : Subgroup Y => T.clSub (D.comap ι)) hD).trans <|
      (congrArg T.clSub (comap_zpowers H)).trans T.clSub_zpowers_z

theorem eq_top_of_DW_eq {W : Submodule (ZMod 2) T.Qt} (hD : DW T ι W = N) : W = ⊤ :=
  (clSub_comap_DW H W).symm.trans <|
    (congrArg (fun D : Subgroup Y => T.clSub (D.comap ι)) hD).trans <|
      (congrArg T.clSub (comap_N H)).trans T.clSub_QG

theorem eq_WU_of_DW_eq {W : Submodule (ZMod 2) T.Qt} {U : Subgroup Y} (hD : DW T ι W = U) :
    W = WU T ι U :=
  (clSub_comap_DW H W).symm.trans (congrArg (fun D : Subgroup Y => T.clSub (D.comap ι)) hD)

theorem comap_le_QG {U : Subgroup Y} (hU : U ≤ N) : U.comap ι ≤ T.QG :=
  fun x hx => (H.mem_QG x).mpr (hU hx)

theorem clPre_WU {U : Subgroup Y} (htU : zpowers t ≤ U) (hU : U ≤ N) :
    T.clPre (WU T ι U) = U.comap ι :=
  T.clPre_clSub (comap_le_QG H hU) (show ι T.z ∈ U from H.z_eq ▸ htU (mem_zpowers t))

theorem DW_WU {U : Subgroup Y} (htU : zpowers t ≤ U) (hU : U ≤ N) : DW T ι (WU T ι U) = U :=
  (congrArg (Subgroup.map ι) (clPre_WU H htU hU)).trans <|
    (Subgroup.map_comap_eq ι U).trans (inf_of_le_right (hU.trans H.N_le))

theorem card_WU {U : Subgroup Y} (htU : zpowers t ≤ U) (hU : U ≤ N) :
    2 * Nat.card (WU T ι U) = Nat.card U := by
  have h1 := T.card_clPre (WU T ι U)
  have h3 : Nat.card (DW T ι (WU T ι U)) = Nat.card (T.clPre (WU T ι U)) :=
    Subgroup.card_map_of_injective H.inj
  have h2 : Nat.card (T.clPre (WU T ι U)) = Nat.card U :=
    h3.symm.trans (congrArg (fun D : Subgroup Y => Nat.card D) (DW_WU H htU hU))
  exact h1.symm.trans h2

end S14.W4Dict

end CFSG.LargeExtraspecial

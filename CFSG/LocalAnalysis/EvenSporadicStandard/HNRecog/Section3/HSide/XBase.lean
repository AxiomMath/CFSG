module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem Gxy_eq_map_of_eq {z p : G} {x : ↥(Gx p)} (hx : (x : G) = z) :
    Gxy p z = (Gx x).map (Gx p).subtype := by
  rw [← hx, Gxy_comm p (x : G)]
  exact Gxy_eq_map_subtype x

theorem derivedOf_Gxy_eq_map {z p : G} {x : ↥(Gx p)} (hx : (x : G) = z) :
    derivedOf (Gxy p z) = (derivedOf (Gx x)).map (Gx p).subtype := by
  rw [Gxy_eq_map_of_eq hx]
  exact derivedOf_map_of_injective (Subgroup.subtype_injective (Gx p)) (Gx x)

theorem pCoreOf_Gxy_eq_map {z p : G} {x : ↥(Gx p)} (hx : (x : G) = z) :
    CFSG.Open.pCoreOf 2 (Gxy p z) = (CFSG.Open.pCoreOf 2 (Gx x)).map (Gx p).subtype := by
  rw [Gxy_eq_map_of_eq hx]
  exact pCoreOf_map_of_injective (Subgroup.subtype_injective (Gx p)) (Gx x)

theorem pCoreOf_derivedOf_Gxy_eq_map {z p : G} {x : ↥(Gx p)} (hx : (x : G) = z) :
    CFSG.Open.pCoreOf 2 (derivedOf (Gxy p z)) =
      (CFSG.Open.pCoreOf 2 (derivedOf (Gx x))).map (Gx p).subtype := by
  rw [derivedOf_Gxy_eq_map hx]
  exact pCoreOf_map_of_injective (Subgroup.subtype_injective (Gx p)) (derivedOf (Gx x))

theorem centerOf_derivedOf_Gxy_eq_map {z p : G} {x : ↥(Gx p)} (hx : (x : G) = z) :
    centerOf (derivedOf (Gxy p z)) = (centerOf (derivedOf (Gx x))).map (Gx p).subtype := by
  rw [derivedOf_Gxy_eq_map hx]
  exact centerOf_map_of_injective (Subgroup.subtype_injective (Gx p)) (derivedOf (Gx x))

theorem centerOf_pCoreOf_derivedOf_Gxy_eq_map {z p : G} {x : ↥(Gx p)} (hx : (x : G) = z) :
    centerOf (CFSG.Open.pCoreOf 2 (derivedOf (Gxy p z))) =
      (centerOf (CFSG.Open.pCoreOf 2 (derivedOf (Gx x)))).map (Gx p).subtype := by
  rw [pCoreOf_derivedOf_Gxy_eq_map hx]
  exact centerOf_map_of_injective (Subgroup.subtype_injective (Gx p))
    (CFSG.Open.pCoreOf 2 (derivedOf (Gx x)))

theorem Gxy_inf_derivedOf_Gx_eq_map {z p : G} {x : ↥(Gx p)} (hx : (x : G) = z) :
    Gxy p z ⊓ derivedOf (Gx p) = (commutator ↥(Gx p) ⊓ Gx x).map (Gx p).subtype := by
  rw [Gxy_eq_map_of_eq hx,
    show derivedOf (Gx p) = (commutator ↥(Gx p)).map (Gx p).subtype from rfl,
    ← Subgroup.map_inf_eq (Gx x) (commutator ↥(Gx p)) (Gx p).subtype
      (Subgroup.subtype_injective (Gx p))]
  exact congrArg (Subgroup.map (Gx p).subtype) (inf_comm (Gx x) (commutator ↥(Gx p)))

theorem Gxyz_eq_map_of_eq {z p : G} {x : ↥(Gx p)} (hx : (x : G) = z) (c : ↥(Gx p)) :
    Gxyz p z (c : G) = (Gx x ⊓ Gx c).map (Gx p).subtype := by
  rw [Gxyz_eq_inf, Gxy_eq_map_of_eq hx]
  exact map_inf_Gx_of_injective (Subgroup.subtype_injective (Gx p)) (Gx x) c

theorem Gxyz_inf_Qz_eq_map {z p : G} {x : ↥(Gx p)} (hx : (x : G) = z)
    (hR : CFSG.Open.pCoreOf 2 (Gxy p z) = Gxy p z ⊓ Qz z) (c : ↥(Gx p)) :
    Gxyz p z (c : G) ⊓ Qz z = (Gx x ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx x)).map (Gx p).subtype := by
  let R : Subgroup ↥(Gx p) := CFSG.Open.pCoreOf 2 (Gx x)
  have hRmap : Gxy p z ⊓ Qz z = R.map (Gx p).subtype := by
    rw [← hR, pCoreOf_Gxy_eq_map hx]
  have hRle : R ≤ Gx x := by
    change (CFSG.pCore 2 ↥(Gx x)).map (Gx x).subtype ≤ Gx x
    exact Subgroup.map_subtype_le _
  have hReq : R ⊓ Gx c = Gx x ⊓ Gx c ⊓ R := by
    conv_rhs => rw [inf_right_comm, inf_of_le_right hRle]
  calc Gxyz p z (c : G) ⊓ Qz z
      = (Gxy p z ⊓ Gx (c : G)) ⊓ Qz z := by rw [Gxyz_eq_inf]
    _ = (Gxy p z ⊓ Qz z) ⊓ Gx (c : G) := inf_right_comm _ _ _
    _ = R.map (Gx p).subtype ⊓ Gx (c : G) := by rw [hRmap]
    _ = (R ⊓ Gx c).map (Gx p).subtype :=
          map_inf_Gx_of_injective (Subgroup.subtype_injective (Gx p)) R c
    _ = (Gx x ⊓ Gx c ⊓ R).map (Gx p).subtype := by rw [hReq]
    _ = (Gx x ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx x)).map (Gx p).subtype := rfl

theorem Gxyz_inf_derivedOf_eq_map {z p : G} {x : ↥(Gx p)} (hx : (x : G) = z) (c : ↥(Gx p)) :
    Gxyz p z (c : G) ⊓ derivedOf (Gxy p z) =
      (Gx x ⊓ Gx c ⊓ derivedOf (Gx x)).map (Gx p).subtype := by
  rw [Gxyz_eq_map_of_eq hx c, derivedOf_Gxy_eq_map hx,
    ← Subgroup.map_inf_eq (Gx x ⊓ Gx c) (derivedOf (Gx x)) (Gx p).subtype
      (Subgroup.subtype_injective (Gx p))]

theorem Gxyz_inf_Qz_inf_derivedOf_eq_map {z p : G} {x : ↥(Gx p)} (hx : (x : G) = z)
    (hR : CFSG.Open.pCoreOf 2 (Gxy p z) = Gxy p z ⊓ Qz z) (c : ↥(Gx p)) :
    Gxyz p z (c : G) ⊓ Qz z ⊓ derivedOf (Gxy p z) =
      (Gx x ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx x) ⊓ derivedOf (Gx x)).map (Gx p).subtype := by
  rw [Gxyz_inf_Qz_eq_map hx hR c, derivedOf_Gxy_eq_map hx,
    ← Subgroup.map_inf_eq (Gx x ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx x)) (derivedOf (Gx x))
      (Gx p).subtype (Subgroup.subtype_injective (Gx p))]

end CFSG.EvenSporadicStandard.HNRecog.Section3

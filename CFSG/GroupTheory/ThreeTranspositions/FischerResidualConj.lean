module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual

import CFSG.GroupTheory.PResidualNormalizer
import TauCeti.GroupTheory.QuotientGroup.MulAut

public section

namespace CFSG.GroupTheory.ThreeTranspositions

variable {G : Type} [Group G] {X : Subgroup G} [X.Normal]

omit [X.Normal] in
theorem mk_mem_threeResidualQuot_of_mem {d : ↥X} {x : ↥X}
    (hx : x ∈ threeResidualJoin d) :
    (QuotientGroup.mk x : ↥X ⧸ Subgroup.center ↥X) ∈ threeResidualQuot d :=
  Subgroup.mem_map_of_mem _ hx

theorem conjNormal_apply_self_of_mem_centralizer {d : ↥X}
    (c : ↥(Subgroup.centralizer ({(d : G)} : Set G))) :
    MulAut.conjNormal (c : G) d = d := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have hc := Subgroup.mem_centralizer_iff.mp c.2 (d : G) (Set.mem_singleton (d : G))
  rw [hc.symm, mul_assoc, mul_inv_cancel, mul_one]

theorem map_conjNormal_threeResidualJoin {d : ↥X}
    (c : ↥(Subgroup.centralizer ({(d : G)} : Set G))) :
    (threeResidualJoin d).map
        (MulAut.conjNormal (c : G)).toMonoidHom = threeResidualJoin d := by
  have hcomm : (commutator ↥X).Characteristic := inferInstance
  have hpRes : (CFSG.Quasithin.pResidual 3 ↥(commutator ↥X)).Characteristic :=
    CFSG.Quasithin.pResidual_characteristic 3 ↥(commutator ↥X)
  have hOchar : (CFSG.Quasithin.pResidualOf 3 (commutator ↥X)).Characteristic :=
    @Subgroup.characteristic_of_characteristic_of_characteristic (↥X) _
      (commutator ↥X) hcomm (CFSG.Quasithin.pResidual 3 ↥(commutator ↥X)) hpRes
  have hO : (CFSG.Quasithin.pResidualOf 3 (commutator ↥X)).map
      (MulAut.conjNormal (c : G)).toMonoidHom =
      CFSG.Quasithin.pResidualOf 3 (commutator ↥X) :=
    Subgroup.characteristic_iff_map_eq.mp hOchar _
  have hz : (Subgroup.zpowers d).map (MulAut.conjNormal (c : G)).toMonoidHom =
      Subgroup.zpowers d := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conjNormal (c : G)) d) = Subgroup.zpowers d
    rw [conjNormal_apply_self_of_mem_centralizer]
  rw [threeResidualJoin, Subgroup.map_sup, hO, hz]

noncomputable def residualConjOnQuot {d : ↥X}
    (c : ↥(Subgroup.centralizer ({(d : G)} : Set G))) :
    MulAut (↥X ⧸ Subgroup.center ↥X) :=
  letI : (Subgroup.center ↥X).Characteristic := Subgroup.centerCharacteristic
  (MulAut.mapQuotient (Subgroup.center ↥X)) (MulAut.conjNormal (c : G))

theorem residualConjOnQuot_mk {d : ↥X}
    (c : ↥(Subgroup.centralizer ({(d : G)} : Set G))) (n : ↥X) :
    residualConjOnQuot (d := d) c (QuotientGroup.mk n) =
      QuotientGroup.mk (MulAut.conjNormal (c : G) n) := by
  have hZ : (Subgroup.center ↥X).Characteristic := Subgroup.centerCharacteristic
  simpa only [residualConjOnQuot] using
    @MulAut.mapQuotient_mk (↥X) _ (Subgroup.center ↥X) hZ
      (MulAut.conjNormal (c : G)) n

theorem map_residualConjOnQuot_threeResidualQuot {d : ↥X}
    (c : ↥(Subgroup.centralizer ({(d : G)} : Set G))) :
    (threeResidualQuot d).map (residualConjOnQuot (d := d) c).toMonoidHom =
      threeResidualQuot d := by
  have hcomp : (residualConjOnQuot (d := d) c).toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center ↥X)) =
      (QuotientGroup.mk' (Subgroup.center ↥X)).comp
        (MulAut.conjNormal (c : G)).toMonoidHom := by
    ext x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply]
    exact residualConjOnQuot_mk (d := d) c x
  rw [threeResidualQuot, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    map_conjNormal_threeResidualJoin]

noncomputable def residualConjMap {d : ↥X}
    (c : ↥(Subgroup.centralizer ({(d : G)} : Set G))) :
    MulAut ↥(threeResidualQuot d) where
  toFun x :=
    ⟨residualConjOnQuot (d := d) c (x : ↥X ⧸ Subgroup.center ↥X), by
      have hx := Subgroup.mem_map_of_mem (residualConjOnQuot (d := d) c).toMonoidHom x.2
      rwa [map_residualConjOnQuot_threeResidualQuot (d := d) c] at hx⟩
  invFun x :=
    ⟨(residualConjOnQuot (d := d) c).symm (x : ↥X ⧸ Subgroup.center ↥X), by
      have hx : (x : ↥X ⧸ Subgroup.center ↥X) ∈ (threeResidualQuot d).map
          (residualConjOnQuot (d := d) c).toMonoidHom := by
        rw [map_residualConjOnQuot_threeResidualQuot (d := d) c]
        exact x.2
      exact Subgroup.mem_map_equiv.mp hx⟩
  left_inv x := Subtype.ext ((residualConjOnQuot (d := d) c).symm_apply_apply
    (x : ↥X ⧸ Subgroup.center ↥X))
  right_inv x := Subtype.ext ((residualConjOnQuot (d := d) c).apply_symm_apply
    (x : ↥X ⧸ Subgroup.center ↥X))
  map_mul' x y := Subtype.ext (map_mul (residualConjOnQuot (d := d) c)
    (x : ↥X ⧸ Subgroup.center ↥X) (y : ↥X ⧸ Subgroup.center ↥X))

theorem residualConjMap_apply_mk {d : ↥X}
    (c : ↥(Subgroup.centralizer ({(d : G)} : Set G))) (n : ↥X)
    (hn : (QuotientGroup.mk n : ↥X ⧸ Subgroup.center ↥X) ∈ threeResidualQuot d) :
    ((residualConjMap (d := d) c ⟨QuotientGroup.mk n, hn⟩ :
        ↥(threeResidualQuot d)) : ↥X ⧸ Subgroup.center ↥X) =
      QuotientGroup.mk (MulAut.conjNormal (c : G) n) := by
  change ((residualConjOnQuot (d := d) c) (QuotientGroup.mk n) :
    ↥X ⧸ Subgroup.center ↥X) =
      QuotientGroup.mk (MulAut.conjNormal (c : G) n)
  exact residualConjOnQuot_mk (d := d) c n

noncomputable def residualConj (d : ↥X) :
    ↥(Subgroup.centralizer ({(d : G)} : Set G)) →*
      MulAut ↥(threeResidualQuot d) where
  toFun c := residualConjMap (d := d) c
  map_one' := by
    ext x
    rcases x with ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
    rw [residualConjMap_apply_mk]
    simp
  map_mul' c c' := by
    ext x
    rcases x with ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MulAut.mul_apply, residualConjMap_apply_mk]
    have hmem : (QuotientGroup.mk (MulAut.conjNormal (c' : G) n) :
        ↥X ⧸ Subgroup.center ↥X) ∈ threeResidualQuot d := by
      rw [← residualConjMap_apply_mk (d := d) c' n hy]
      exact (residualConjMap (d := d) c' (⟨QuotientGroup.mk n, hy⟩ :
        ↥(threeResidualQuot d))).2
    have hz : residualConjMap (d := d) c'
        (⟨QuotientGroup.mk n, hy⟩ : ↥(threeResidualQuot d)) =
        (⟨QuotientGroup.mk (MulAut.conjNormal (c' : G) n), hmem⟩ :
          ↥(threeResidualQuot d)) := by
      apply Subtype.ext
      rw [residualConjMap_apply_mk]
    rw [hz, residualConjMap_apply_mk]
    congr 1
    simp only [Subgroup.coe_mul, map_mul, MulAut.mul_apply]

theorem residualConj_apply_mk {d : ↥X}
    (c : ↥(Subgroup.centralizer ({(d : G)} : Set G))) (n : ↥X)
    (hn : (QuotientGroup.mk n : ↥X ⧸ Subgroup.center ↥X) ∈ threeResidualQuot d) :
    ((residualConj d c ⟨QuotientGroup.mk n, hn⟩ : ↥(threeResidualQuot d)) :
        ↥X ⧸ Subgroup.center ↥X) =
      QuotientGroup.mk (MulAut.conjNormal (c : G) n) :=
  residualConjMap_apply_mk c n hn

omit [X.Normal] in
theorem mk_mem_threeResidualQuot_self (d : ↥X) :
    (QuotientGroup.mk d : ↥X ⧸ Subgroup.center ↥X) ∈ threeResidualQuot d :=
  mk_mem_threeResidualQuot_of_mem (d := d) (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))

theorem residualConj_fix_self {d : ↥X}
    (c : ↥(Subgroup.centralizer ({(d : G)} : Set G))) :
    residualConj d c ⟨QuotientGroup.mk d, mk_mem_threeResidualQuot_self d⟩ =
      ⟨QuotientGroup.mk d, mk_mem_threeResidualQuot_self d⟩ := by
  apply Subtype.ext
  rw [residualConj_apply_mk, conjNormal_apply_self_of_mem_centralizer]

theorem residualConj_mem_threeResidualClass {d : ↥X}
    (c : ↥(Subgroup.centralizer ({(d : G)} : Set G)))
    {x : ↥(threeResidualQuot d)} (hx : x ∈ threeResidualClass d) :
    residualConj d c x ∈ threeResidualClass d := by
  rw [threeResidualClass] at hx ⊢
  obtain ⟨w, hw, hwx⟩ := hx
  have hw' : MulAut.conjNormal (c : G) w ∈ threeResidualJoin d := by
    rw [← map_conjNormal_threeResidualJoin (d := d) c]
    exact Subgroup.mem_map_of_mem _ hw
  refine ⟨MulAut.conjNormal (c : G) w, hw', ?_⟩
  have hmem : (QuotientGroup.mk (w * d * w⁻¹) : ↥X ⧸ Subgroup.center ↥X) ∈
      threeResidualQuot d := by
    rw [show (QuotientGroup.mk (w * d * w⁻¹) : ↥X ⧸ Subgroup.center ↥X) =
        (x : ↥X ⧸ Subgroup.center ↥X) from hwx]
    exact x.2
  have hx_eq : x = (⟨QuotientGroup.mk (w * d * w⁻¹), hmem⟩ :
      ↥(threeResidualQuot d)) := Subtype.ext hwx.symm
  rw [hx_eq, residualConj_apply_mk]
  rw [map_mul, map_mul, map_inv, conjNormal_apply_self_of_mem_centralizer]

theorem residualConj_eq_conj {d : ↥X}
    (c : ↥(Subgroup.centralizer ({(d : G)} : Set G))) (hcX : (c : G) ∈ X)
    (hcW : (⟨c, hcX⟩ : ↥X) ∈ threeResidualJoin d) :
    residualConj d c =
      MulAut.conj (⟨QuotientGroup.mk ⟨c, hcX⟩,
        mk_mem_threeResidualQuot_of_mem hcW⟩ : ↥(threeResidualQuot d)) := by
  ext x
  rcases x with ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
  rw [residualConj_apply_mk, MulAut.conj_apply]
  have hconj : MulAut.conjNormal (c : G) n =
      (⟨c, hcX⟩ : ↥X) * n * ⟨c, hcX⟩⁻¹ := by
    apply Subtype.ext
    simp [MulAut.conjNormal_apply]
  change (QuotientGroup.mk' (Subgroup.center ↥X)) (MulAut.conjNormal (c : G) n) =
    (QuotientGroup.mk' (Subgroup.center ↥X))
      ((⟨c, hcX⟩ : ↥X) * n * ⟨c, hcX⟩⁻¹)
  rw [hconj]

theorem conjNormal_div_mem_center_of_residualConj_eq_one {d : ↥X}
    {c : ↥(Subgroup.centralizer ({(d : G)} : Set G))} (hc : residualConj d c = 1)
    (n : ↥X)
    (hn : (QuotientGroup.mk n : ↥X ⧸ Subgroup.center ↥X) ∈ threeResidualQuot d) :
    (MulAut.conjNormal (c : G) n) / n ∈ Subgroup.center ↥X := by
  have h := congrArg
    (fun f : MulAut ↥(threeResidualQuot d) =>
      (f ⟨QuotientGroup.mk n, hn⟩ : ↥(threeResidualQuot d))) hc
  have hq : ((residualConj d c ⟨QuotientGroup.mk n, hn⟩ :
        ↥(threeResidualQuot d)) : ↥X ⧸ Subgroup.center ↥X) =
      (QuotientGroup.mk n : ↥X ⧸ Subgroup.center ↥X) := by
    rw [h]
    rfl
  rw [residualConj_apply_mk] at hq
  rwa [QuotientGroup.eq_iff_div_mem] at hq

end CFSG.GroupTheory.ThreeTranspositions

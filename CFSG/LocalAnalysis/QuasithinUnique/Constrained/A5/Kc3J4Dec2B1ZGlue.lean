module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4ClassBase
public import CFSG.Sporadic.J4.QT2ASyl

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

theorem classRad_of_map_cm {Y : Type*} [Group Y] (g : Y) {V : Subgroup Y}
    (h : ClassRad (V.map (cm g))) : ClassRad V := by
  have := classRad_map_cm g⁻¹ h
  rwa [map_cm_inv_map_cm] at this

theorem map_cm_closure {Y : Type*} [Group Y] (g : Y) (S : Set Y) :
    (Subgroup.closure S).map (cm g) = Subgroup.closure (cm g '' S) :=
  MonoidHom.map_closure (cm g) S

theorem Mx_conj_el5
    (hM : MatFacts) {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0) {x : J} {X : Array V2}
    (hx : Mx x = rowsMatrix X) :
    Mx (el5 w * x * (el5 w)⁻¹) = rowsMatrix (mulRows (mulRows (wR w) X) (wR (invW w))) := by
  have hinv : (el5 w)⁻¹ = el5 (invW w) := by
    rw [invW_eq]
    unfold el5
    exact (wordProd_invWord gen5 _ hw).symm
  rw [hinv, map_mul, map_mul, Mx_el5 hM, hx, Mx_el5 hM, rowsMatrix_mulRows, rowsMatrix_mulRows]

end CFSG.QuasithinUnique.A5

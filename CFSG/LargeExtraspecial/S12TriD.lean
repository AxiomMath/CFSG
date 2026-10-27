module

public import CFSG.Timmesfeld.Transvection.QTwoThin

public section

namespace CFSG.LargeExtraspecial.S12Tri

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Subgroup Matrix QuadraticMap CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer
open CFSG.Fischer.Classification CFSG.Timmesfeld.Transvection.QTwo

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)}

variable (Q) in
abbrev OG : Subgroup (GL ι (ZMod 2)) := fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x

abbrev oact (g : OG Q) (x : ι → ZMod 2) : ι → ZMod 2 :=
  ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ x

theorem oact_mul (g h : OG Q) (x : ι → ZMod 2) : oact (g * h) x = oact g (oact h x) := by
  simp only [oact, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem oact_one (x : ι → ZMod 2) : oact (1 : OG Q) x = x := by
  simp only [oact, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]

theorem oact_oact_inv (g : OG Q) (x : ι → ZMod 2) : oact g (oact g⁻¹ x) = x := by
  rw [← oact_mul, mul_inv_cancel, oact_one]

theorem oact_add (g : OG Q) (x y : ι → ZMod 2) : oact g (x + y) = oact g x + oact g y :=
  Matrix.mulVec_add _ _ _

theorem oact_smul (g : OG Q) (c : ZMod 2) (x : ι → ZMod 2) : oact g (c • x) = c • oact g x :=
  Matrix.mulVec_smul _ _ _

theorem map_oact (g : OG Q) (x : ι → ZMod 2) : Q (oact g x) = Q x :=
  (mem_fischerMatrixGroup_isometry_iff Q (g : GL ι (ZMod 2))).1 g.2 x

theorem polar_oact (g : OG Q) (x y : ι → ZMod 2) :
    polar Q (oact g x) (oact g y) = polar Q x y := by
  simp only [QuadraticMap.polar, ← oact_add, map_oact]

theorem OG.ext {g h : OG Q} (H : ∀ x, oact g x = oact h x) : g = h := by
  apply Subtype.ext
  apply Units.ext
  exact Matrix.ext_of_mulVec_single fun i => H _

variable (Q) in
@[expose] noncomputable def tvO {v : ι → ZMod 2} (hv : Q v = 1) : OG Q :=
  ⟨orthTransvectionGL Q v, tv_mem_group hv⟩

theorem oact_tvO {v : ι → ZMod 2} (hv : Q v = 1) (x : ι → ZMod 2) :
    oact (tvO Q hv) x = x + polar Q x v • v :=
  tv_mulVec hv x

theorem conj_tvO (g : OG Q) {v : ι → ZMod 2} (hv : Q v = 1) :
    g * tvO Q hv * g⁻¹ = tvO Q (show Q (oact g v) = 1 by rw [map_oact, hv]) := by
  refine OG.ext fun x => ?_
  rw [oact_mul, oact_mul, oact_tvO, oact_tvO, oact_add, oact_smul, oact_oact_inv]
  congr 2
  rw [← polar_oact g, oact_oact_inv]

theorem tvO_commute_iff (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) {a b : ι → ZMod 2}
    (ha : Q a = 1) (hb : Q b = 1) :
    tvO Q ha * tvO Q hb = tvO Q hb * tvO Q ha ↔ polar Q a b = 0 := by
  rw [← tv_commute_iff hnd ha hb]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem tvO_eq_iff (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) {a b : ι → ZMod 2}
    (ha : Q a = 1) (hb : Q b = 1) : tvO Q ha = tvO Q hb ↔ a = b := by
  refine ⟨fun h => eq_of_tv_eq hnd ha hb (congrArg Subtype.val h), ?_⟩
  rintro rfl
  rfl

theorem oact_eq_of_commute (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) {v : ι → ZMod 2}
    (hv : Q v = 1) {y : OG Q} (hy : y * tvO Q hv = tvO Q hv * y) : oact y v = v := by
  have h := conj_tvO y hv
  rw [hy, mul_inv_cancel_right] at h
  exact ((tvO_eq_iff hnd _ _).1 h).symm

theorem zmod_two_add_self (c : ZMod 2) : c + c = 0 := by revert c; decide

theorem eq_one_or_eq_of_centralizes_tv (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    {v : ι → ZMod 2} (hv : Q v = 1) {y : OG Q} (hyt : y * tvO Q hv = tvO Q hv * y)
    (hyD : ∀ w (hw : Q w = 1), polar Q w v = 0 → w ≠ v → y * tvO Q hw = tvO Q hw * y) :
    y = 1 ∨ y = tvO Q hv := by
  have hyv := oact_eq_of_commute hnd hv hyt
  have hfix1 : ∀ w, Q w = 1 → polar Q w v = 0 → oact y w = w := by
    intro w hw hwv
    by_cases hwv' : w = v
    · rw [hwv']
      exact hyv
    · exact oact_eq_of_commute hnd hw (hyD w hw hwv hwv')
  have hfix : ∀ u, polar Q u v = 0 → oact y u = u := by
    intro u huv
    rcases zmod_two_eq_zero_or_one (Q u) with h0 | h1
    · have hQ : Q (u + v) = 1 := by rw [map_add_polar, h0, hv, huv]; rfl
      have hpol : polar Q (u + v) v = 0 := by
        rw [polar_add_left, huv, polar_self_zmod_two, add_zero]
      have := hfix1 _ hQ hpol
      rw [oact_add, hyv] at this
      exact add_right_cancel this
    · exact hfix1 u h1 huv
  obtain ⟨x₀, hx₀⟩ := exists_polar_eq_one hnd (ne_zero_of_eq_one hv)
  set z := oact y x₀ + x₀ with hz
  have hyx₀ : oact y x₀ = z + x₀ := by
    rw [hz, add_assoc, add_self_zmod_two, add_zero]
  have hperp : ∀ x, polar Q (x + polar Q x v • x₀) v = 0 := fun x => by
    rw [polar_add_left, polar_smul_left, hx₀, smul_eq_mul, mul_one, zmod_two_add_self]
  have hform : ∀ x, oact y x = x + polar Q x v • z := by
    intro x
    have hdec : x = (x + polar Q x v • x₀) + polar Q x v • x₀ := by
      rw [add_assoc, add_self_zmod_two, add_zero]
    conv_lhs => rw [hdec]
    rw [oact_add, oact_smul, hfix _ (hperp x), hyx₀, smul_add]
    calc x + polar Q x v • x₀ + (polar Q x v • z + polar Q x v • x₀)
        = x + polar Q x v • z + (polar Q x v • x₀ + polar Q x v • x₀) := by abel
      _ = x + polar Q x v • z := by rw [add_self_zmod_two, add_zero]
  have hzperp : ∀ u, polar Q u v = 0 → polar Q u z = 0 := by
    intro u huv
    rw [hz, polar_add_right, ← polar_oact y u x₀, hfix u huv, zmod_two_add_self]
  set c := polar Q x₀ z with hc
  have hz' : z + c • v = 0 := by
    refine hnd _ fun x => ?_
    rw [polar_comm]
    have hdec : x = (x + polar Q x v • x₀) + polar Q x v • x₀ := by
      rw [add_assoc, add_self_zmod_two, add_zero]
    rw [hdec, polar_add_left, polar_smul_left, polar_add_right, polar_smul_right,
      hzperp _ (hperp x), (hperp x), polar_add_right, polar_smul_right, hx₀, ← hc]
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one, zmod_two_add_self]
  have hzc : z = c • v := eq_of_add_eq_zero_zmod_two hz'
  rcases zmod_two_eq_zero_or_one c with h0 | h1
  · left
    refine OG.ext fun x => ?_
    rw [hform, hzc, h0, zero_smul, smul_zero, add_zero, oact_one]
  · right
    refine OG.ext fun x => ?_
    rw [hform, hzc, h1, one_smul, oact_tvO]

end CFSG.LargeExtraspecial.S12Tri

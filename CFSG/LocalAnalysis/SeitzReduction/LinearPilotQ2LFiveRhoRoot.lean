module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRhoLift
import all CFSG.Fischer.F4

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.Fischer CFSG.LieType.Steinberg.CentralExt.SLClosed

@[expose] def rhoPairVec (i j : Fin 4) : Fin 4 → F4 :=
  fun r => if r = i ∨ r = j then F4.ω else F4.ω * F4.ω

@[expose] def rhoPtVec (m : Fin 4) : Fin 4 → F4 := fun r => if r = m then 1 else F4.ω

@[expose] noncomputable def rhoDiag (d : Fin 4 → F4) : SpecialLinearGroup (Fin 4) F4 :=
  if h : (diagonal d).det = 1 then (⟨diagonal d, h⟩ : SpecialLinearGroup (Fin 4) F4) else 1

theorem coe_rhoDiag {d : Fin 4 → F4} (h : d 0 * d 1 * d 2 * d 3 = 1) :
    (rhoDiag d : Matrix (Fin 4) (Fin 4) F4) = diagonal d := by
  have h' : (diagonal d).det = 1 := by rw [det_diagonal, Fin.prod_univ_four, h]
  simp [rhoDiag, h']

theorem rhoPairVec_prod : ∀ i j : Fin 4, i ≠ j →
    rhoPairVec i j 0 * rhoPairVec i j 1 * rhoPairVec i j 2 * rhoPairVec i j 3 = 1 := by
  decide +kernel

theorem rhoPairVec_ne_one : ∀ i j r : Fin 4, rhoPairVec i j r ≠ 1 := by decide +kernel

theorem rhoPairVec_sq_ne_one : ∀ i j r : Fin 4, rhoPairVec i j r * rhoPairVec i j r ≠ 1 := by
  decide +kernel

theorem rhoPtVec_prod : ∀ m : Fin 4,
    rhoPtVec m 0 * rhoPtVec m 1 * rhoPtVec m 2 * rhoPtVec m 3 = 1 := by
  decide +kernel

theorem commute_of_diag {g g' : SpecialLinearGroup (Fin 4) F4} {d d' : Fin 4 → F4}
    (hg : (g : Matrix (Fin 4) (Fin 4) F4) = diagonal d)
    (hg' : (g' : Matrix (Fin 4) (Fin 4) F4) = diagonal d') : g * g' = g' * g := by
  have h := commute_of_coe_eq_diagonal hg hg'
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem diag_mul_tv {g : SpecialLinearGroup (Fin 4) F4} {d : Fin 4 → F4}
    (hg : (g : Matrix (Fin 4) (Fin 4) F4) = diagonal d) {i j : Fin 4} (h : i ≠ j)
    (hd : d i = d j) (s : F4) : g * tv F4 i j s = tv F4 i j s * g := by
  have h1 := conj_tv hg h s
  rw [hd, mul_inv_cancel₀ (diag_ne_zero hg j), one_mul, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem coe_veeFrob_eq_map (g : SpecialLinearGroup (Fin 4) F4) :
    (veeFrob g : Matrix (Fin 4) (Fin 4) F4) =
      (g : Matrix (Fin 4) (Fin 4) F4).map (fun x => x * x) := by
  rw [veeFrob, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  rfl

theorem coe_veeFrob_of_diag {g : SpecialLinearGroup (Fin 4) F4} {d : Fin 4 → F4}
    (hg : (g : Matrix (Fin 4) (Fin 4) F4) = diagonal d) :
    (veeFrob g : Matrix (Fin 4) (Fin 4) F4) = diagonal (fun r => d r * d r) := by
  rw [coe_veeFrob_eq_map, hg, diagonal_map (f := fun x : F4 => x * x) (mul_zero 0)]

theorem veeFrob_tv {i j : Fin 4} (h : i ≠ j) (s : F4) :
    veeFrob (tv F4 i j s) = tv F4 i j (s * s) := by
  apply Subtype.ext
  rw [coe_veeFrob_eq_map, tv_of_ne h, tv_of_ne h, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  ext a b
  simp only [map_apply, Matrix.add_apply, one_apply, single_apply]
  by_cases hab : a = b
  · subst hab
    have : ¬(i = a ∧ j = a) := fun hh => h (hh.1.trans hh.2.symm)
    simp [this]
  · simp only [hab, ite_false, zero_add]
    split_ifs <;> simp

theorem tv_mulVec {i j : Fin 4} (h : i ≠ j) (s : F4) (v : Fin 4 → F4) (r : Fin 4) :
    ((tv F4 i j s : Matrix (Fin 4) (Fin 4) F4) *ᵥ v) r = v r + if r = i then s * v j else 0 := by
  rw [tv_of_ne h, SpecialLinearGroup.transvection_coe, add_mulVec, one_mulVec, single_mulVec]
  simp [Function.update_apply]

namespace RhoExt

variable {E : Type*} [Group E] (X : RhoExt E)

@[expose] noncomputable def torN : E := Function.surjInv X.surj (rhoDiag (rhoPairVec 2 3))

@[expose] noncomputable def torH : E := X.torN * (X.τ X.torN)⁻¹

theorem π_torH : (X.π X.torH : Matrix (Fin 4) (Fin 4) F4) = diagonal (rhoPairVec 0 1) := by
  have hn : X.π X.torN = rhoDiag (rhoPairVec 2 3) := Function.surjInv_eq X.surj _
  have h23 := coe_rhoDiag (rhoPairVec_prod 2 3 (by decide))
  have h01 := coe_rhoDiag (rhoPairVec_prod 0 1 (by decide))
  have key : rhoDiag (rhoPairVec 0 1) * veeFrob (rhoDiag (rhoPairVec 2 3)) =
      rhoDiag (rhoPairVec 2 3) := by
    apply Subtype.ext
    change (rhoDiag (rhoPairVec 0 1) : Matrix (Fin 4) (Fin 4) F4) *
        (veeFrob (rhoDiag (rhoPairVec 2 3)) : Matrix (Fin 4) (Fin 4) F4) =
        (rhoDiag (rhoPairVec 2 3) : Matrix (Fin 4) (Fin 4) F4)
    rw [coe_veeFrob_of_diag h23, h01, h23, diagonal_mul_diagonal]
    congr 1
    funext r
    revert r
    decide +kernel
  have h : X.π X.torH = rhoDiag (rhoPairVec 0 1) := by
    rw [torH, map_mul, map_inv, X.π_τ, hn, mul_inv_eq_iff_eq_mul]
    exact key.symm
  rw [h, h01]

theorem τ_torH : X.τ X.torH = X.torH⁻¹ := by
  rw [torH, map_mul, map_inv, X.τ_τ, _root_.mul_inv_rev, inv_inv]

@[expose] noncomputable def tor (g : SpecialLinearGroup (Fin 4) F4) : E := X.fixLift X.torH g

theorem tor_spec {g : SpecialLinearGroup (Fin 4) F4} {d : Fin 4 → F4}
    (hg : (g : Matrix (Fin 4) (Fin 4) F4) = diagonal d) :
    X.π (X.tor g) = g ∧ X.torH * X.tor g = X.tor g * X.torH :=
  X.fixLift_spec X.π_torH (rhoPairVec_ne_one 0 1) (commute_of_diag X.π_torH hg)

theorem tor_commute {g g' : SpecialLinearGroup (Fin 4) F4} {d d' : Fin 4 → F4}
    (hg : (g : Matrix (Fin 4) (Fin 4) F4) = diagonal d)
    (hg' : (g' : Matrix (Fin 4) (Fin 4) F4) = diagonal d') :
    X.tor g * X.tor g' = X.tor g' * X.tor g := by
  obtain ⟨h1, h2⟩ := X.tor_spec hg
  obtain ⟨h1', h2'⟩ := X.tor_spec hg'
  have hy : X.π (X.tor g * X.tor g' * (X.tor g)⁻¹) = g' := by
    rw [map_mul, map_mul, map_inv, h1, h1', commute_of_diag hg hg', mul_inv_cancel_right]
  have hyk : X.torH * (X.tor g * X.tor g' * (X.tor g)⁻¹) =
      (X.tor g * X.tor g' * (X.tor g)⁻¹) * X.torH :=
    (((show Commute X.torH (X.tor g) from h2).mul_right (show Commute _ _ from h2')).mul_right
      (show Commute X.torH (X.tor g) from h2).inv_right).eq
  have h3 : X.tor g' = X.tor g * X.tor g' * (X.tor g)⁻¹ :=
    X.fixLift_eq X.π_torH (rhoPairVec_ne_one 0 1) hy hyk
  rw [eq_mul_inv_iff_mul_eq] at h3
  exact h3.symm

theorem τ_tor {g : SpecialLinearGroup (Fin 4) F4} {d : Fin 4 → F4}
    (hg : (g : Matrix (Fin 4) (Fin 4) F4) = diagonal d) :
    X.τ (X.tor g) = X.tor (veeFrob g) := by
  obtain ⟨h1, h2⟩ := X.tor_spec hg
  have h3 : X.τ X.torH * X.τ (X.tor g) = X.τ (X.tor g) * X.τ X.torH := by
    rw [← map_mul, h2, map_mul]
  rw [X.τ_torH] at h3
  exact (X.fixLift_eq X.π_torH (rhoPairVec_ne_one 0 1) (by rw [X.π_τ, h1])
    (Commute.inv_left_iff.mp h3).eq).symm

@[expose] noncomputable def rootK (i j : Fin 4) : E := X.tor (rhoDiag (rhoPairVec i j))

theorem π_rootK {i j : Fin 4} (h : i ≠ j) :
    (X.π (X.rootK i j) : Matrix (Fin 4) (Fin 4) F4) = diagonal (rhoPairVec i j) := by
  rw [rootK, (X.tor_spec (coe_rhoDiag (rhoPairVec_prod i j h))).1,
    coe_rhoDiag (rhoPairVec_prod i j h)]

@[expose] noncomputable def rootLift (i j : Fin 4) (s : F4) : E :=
  if i ≠ j then X.fixLift (X.rootK i j) (tv F4 i j s) else 1

theorem rootLift_spec {i j : Fin 4} (h : i ≠ j) (s : F4) :
    X.π (X.rootLift i j s) = tv F4 i j s ∧
      X.rootK i j * X.rootLift i j s = X.rootLift i j s * X.rootK i j := by
  rw [rootLift, ite_eq_left h]
  exact X.fixLift_spec (X.π_rootK h) (rhoPairVec_ne_one i j)
    (diag_mul_tv (X.π_rootK h) h (by simp [rhoPairVec]) s)

theorem π_rootLift {i j : Fin 4} (h : i ≠ j) (s : F4) : X.π (X.rootLift i j s) = tv F4 i j s :=
  (X.rootLift_spec h s).1

theorem rootLift_commute_tor {i j : Fin 4} (h : i ≠ j) {g : SpecialLinearGroup (Fin 4) F4}
    {d : Fin 4 → F4} (hg : (g : Matrix (Fin 4) (Fin 4) F4) = diagonal d) (hd : d i = d j)
    (s : F4) : X.tor g * X.rootLift i j s = X.rootLift i j s * X.tor g := by
  obtain ⟨h1, h2⟩ := X.rootLift_spec h s
  obtain ⟨hg1, -⟩ := X.tor_spec hg
  have hc : X.rootK i j * X.tor g = X.tor g * X.rootK i j :=
    X.tor_commute (coe_rhoDiag (rhoPairVec_prod i j h)) hg
  have hy : X.π (X.tor g * X.rootLift i j s * (X.tor g)⁻¹) = X.π (X.rootLift i j s) := by
    rw [map_mul, map_mul, map_inv, hg1, h1, diag_mul_tv hg h hd s, mul_inv_cancel_right]
  have hyk : X.rootK i j * (X.tor g * X.rootLift i j s * (X.tor g)⁻¹) =
      (X.tor g * X.rootLift i j s * (X.tor g)⁻¹) * X.rootK i j :=
    (((show Commute (X.rootK i j) (X.tor g) from hc).mul_right (show Commute _ _ from h2)).mul_right
      (show Commute (X.rootK i j) (X.tor g) from hc).inv_right).eq
  have h3 := X.eq_of_commute (X.π_rootK h) (rhoPairVec_ne_one i j) hy hyk h2
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem rootLift_add {i j : Fin 4} (h : i ≠ j) (s s' : F4) :
    X.rootLift i j (s + s') = X.rootLift i j s * X.rootLift i j s' := by
  obtain ⟨h1, h2⟩ := X.rootLift_spec h s
  obtain ⟨h1', h2'⟩ := X.rootLift_spec h s'
  obtain ⟨h1'', h2''⟩ := X.rootLift_spec h (s + s')
  refine X.eq_of_commute (X.π_rootK h) (rhoPairVec_ne_one i j) ?_ h2''
    ((show Commute _ _ from h2).mul_right (show Commute _ _ from h2')).eq
  rw [h1'', map_mul, h1, h1', tv_add h]

theorem rootLift_zero {i j : Fin 4} (h : i ≠ j) : X.rootLift i j 0 = 1 := by
  have h1 := X.rootLift_add h 0 0
  rw [add_zero] at h1
  exact left_eq_mul.mp h1

theorem rootLift_mul_self {i j : Fin 4} (h : i ≠ j) (s : F4) :
    X.rootLift i j s * X.rootLift i j s = 1 := by
  rw [← X.rootLift_add h, CharTwo.add_self_eq_zero, X.rootLift_zero h]

theorem rootLift_inv {i j : Fin 4} (h : i ≠ j) (s : F4) :
    (X.rootLift i j s)⁻¹ = X.rootLift i j s :=
  inv_eq_of_mul_eq_one_right (X.rootLift_mul_self h s)

theorem τ_rootLift {i j : Fin 4} (h : i ≠ j) (s : F4) :
    X.τ (X.rootLift i j s) = X.rootLift i j (s * s) := by
  have hg := coe_rhoDiag (rhoPairVec_prod i j h)
  have hfg := coe_veeFrob_of_diag hg
  obtain ⟨hk1, -⟩ := X.tor_spec hfg
  have hk : (X.π (X.tor (veeFrob (rhoDiag (rhoPairVec i j)))) : Matrix (Fin 4) (Fin 4) F4) =
      diagonal (fun r => rhoPairVec i j r * rhoPairVec i j r) := by rw [hk1, hfg]
  obtain ⟨h1, h2⟩ := X.rootLift_spec h s
  have hτk : X.τ (X.rootK i j) = X.tor (veeFrob (rhoDiag (rhoPairVec i j))) := X.τ_tor hg
  have hc1 : X.tor (veeFrob (rhoDiag (rhoPairVec i j))) * X.τ (X.rootLift i j s) =
      X.τ (X.rootLift i j s) * X.tor (veeFrob (rhoDiag (rhoPairVec i j))) := by
    rw [← hτk, ← map_mul, h2, map_mul]
  have hc2 := X.rootLift_commute_tor h hfg (by simp [rhoPairVec]) (s * s)
  refine X.eq_of_commute hk (fun r => rhoPairVec_sq_ne_one i j r) ?_ hc1 hc2
  rw [X.π_τ, h1, veeFrob_tv h, (X.rootLift_spec h (s * s)).1]

end RhoExt

end CFSG.SeitzReduction.LinearPilot

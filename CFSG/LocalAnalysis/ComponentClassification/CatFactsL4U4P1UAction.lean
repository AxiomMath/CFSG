module

public import CFSG.LieType.Multipliers.U43Action

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43

open CFSG.LieType.Multipliers.U43 Matrix CFSG.Assembly.LowTwoRank
open scoped LinearAlgebra.Projectivization

@[expose] noncomputable def perm820 : GL (Fin 4) F9 →* Equiv.Perm (Fin 820) :=
  (Equiv.permCongrHom ptEquiv).toMonoidHom.comp (MulAction.toPermHom (GL (Fin 4) F9) Pt)

theorem perm820_apply (A : GL (Fin 4) F9) (i : Fin 820) :
    (perm820 A i : ℕ) = ptIndex ((A : Matrix (Fin 4) (Fin 4) F9) *ᵥ decode i) := by
  have h1 : perm820 A i = ptEquiv (A • ptEquiv.symm i) := by
    simp only [perm820, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Equiv.permCongrHom_coe, Equiv.permCongr_apply, MulAction.toPermHom_apply,
      MulAction.toPerm_apply]
  rw [h1, ptEquiv_symm_apply, Projectivization.smul_mk, ptEquiv_apply, ptFin_mk, gl_smul_vec]

theorem psi_mk (g : StatedSU 4 3 F9) :
    psi (QuotientGroup.mk g) = perm820 (g : GL (Fin 4) F9) := by
  ext i
  rw [psi_mk_apply, perm820_apply]

theorem decode_ptIndex {w : V} (hw : w ≠ 0) :
    ∃ c : F9, c ≠ 0 ∧ decode (ptIndex w) = c • w := by
  have h1 : ptEquiv.symm (ptEquiv (Projectivization.mk F9 w hw)) =
      Projectivization.mk F9 w hw := Equiv.symm_apply_apply _ _
  rw [ptEquiv_apply, ptFin_mk, ptEquiv_symm_apply] at h1
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F9 _ _ _ _).mp h1
  exact ⟨a, a.ne_zero, ha.symm⟩

theorem mulVec_ne_zero (A : GL (Fin 4) F9) {w : V} (hw : w ≠ 0) :
    (A : Matrix (Fin 4) (Fin 4) F9) *ᵥ w ≠ 0 :=
  (smul_ne_zero_iff_ne A).mpr hw

@[expose] def barF (a : F9) : F9 := ⟨a.re, -a.im⟩

theorem barF_eq_pow : ∀ a : F9, barF a = a ^ 3 := by decide

theorem barF_barF : ∀ a : F9, barF (barF a) = a := by decide

theorem barF_mul : ∀ a b : F9, barF (a * b) = barF a * barF b := by decide

theorem barF_add : ∀ a b : F9, barF (a + b) = barF a + barF b := by decide

theorem barF_ne_zero : ∀ a : F9, a ≠ 0 → barF a ≠ 0 := by decide

@[expose] def barEquiv : F9 ≃+* F9 where
  toFun := barF
  invFun := barF
  left_inv := barF_barF
  right_inv := barF_barF
  map_mul' := barF_mul
  map_add' := barF_add

theorem barEquiv_apply (a : F9) : barEquiv a = barF a := rfl

@[expose] def barV (v : V) : V := fun i => barF (v i)

theorem barV_barV (v : V) : barV (barV v) = v := funext fun i => barF_barF (v i)

theorem barV_smul (c : F9) (v : V) : barV (c • v) = barF c • barV v :=
  funext fun i => barF_mul c (v i)

theorem barV_ne_zero {v : V} (hv : v ≠ 0) : barV v ≠ 0 := by
  intro h
  apply hv
  rw [← barV_barV v, h]
  funext i
  show barF 0 = 0
  decide

theorem barV_mulVec (A : Matrix (Fin 4) (Fin 4) F9) (v : V) :
    barV (A *ᵥ v) = A.map barF *ᵥ barV v :=
  funext fun i => RingHom.map_mulVec (barEquiv : F9 →+* F9) A v i

theorem frob_left : ∀ i : Fin 820, ptIndex (barV (decode (ptIndex (barV (decode i))))) = i := by
  decide +kernel

@[expose] def frobFun (i : Fin 820) : Fin 820 := ⟨ptIndex (barV (decode i)), ptIndex_lt _⟩

theorem frobFun_val (i : Fin 820) : (frobFun i : ℕ) = ptIndex (barV (decode i)) := rfl

theorem frobFun_frobFun (i : Fin 820) : frobFun (frobFun i) = i := by
  apply Fin.ext
  rw [frobFun_val, frobFun_val]
  exact frob_left i

@[expose] def frob820 : Equiv.Perm (Fin 820) where
  toFun := frobFun
  invFun := frobFun
  left_inv := frobFun_frobFun
  right_inv := frobFun_frobFun

theorem frob820_apply (i : Fin 820) : (frob820 i : ℕ) = ptIndex (barV (decode i)) := rfl

theorem frob820_mul_self : frob820 * frob820 = 1 := by
  ext i
  exact congrArg Fin.val (frobFun_frobFun i)

theorem frob820_inv : frob820⁻¹ = frob820 :=
  inv_eq_of_mul_eq_one_right frob820_mul_self

theorem ptIndex_barV_smul {c : F9} (hc : c ≠ 0) (w : V) :
    ptIndex (barV (c • w)) = ptIndex (barV w) := by
  rw [barV_smul, ptIndex_smul (barF_ne_zero c hc)]

theorem frob820_conj (A B : GL (Fin 4) F9)
    (hB : (B : Matrix (Fin 4) (Fin 4) F9) = (A : Matrix (Fin 4) (Fin 4) F9).map barF) :
    frob820 * perm820 A * frob820⁻¹ = perm820 B := by
  rw [frob820_inv]
  ext i
  simp only [Equiv.Perm.mul_apply]
  rw [frob820_apply, perm820_apply, perm820_apply, frob820_apply]
  have hu : barV (decode i) ≠ 0 := barV_ne_zero (decode_ne_zero i)
  obtain ⟨c₁, hc₁, h₁⟩ := decode_ptIndex hu
  rw [h₁, Matrix.mulVec_smul, ptIndex_smul hc₁]
  obtain ⟨c₂, hc₂, h₂⟩ := decode_ptIndex (mulVec_ne_zero A hu)
  rw [h₂, ptIndex_barV_smul hc₂, barV_mulVec, barV_barV, hB]

end CFSG.ComponentClassification.HarrisLit.P1.U43

module

public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.EvenSmallLie.Child3.SelL39

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.Multipliers.U43 Matrix
open scoped LinearAlgebra.Projectivization

abbrev V3 : Type := Fin 3 → F9

@[expose] def lead3 (v : V3) : F9 := if v 0 ≠ 0 then v 0 else if v 1 ≠ 0 then v 1 else v 2

@[expose] def normalize3 (v : V3) : V3 := (lead3 v)⁻¹ • v

@[expose] def rawIndex3 (v : V3) : ℕ :=
  if v 0 ≠ 0 then 9 * code (v 1) + code (v 2) else if v 1 ≠ 0 then 81 + code (v 2) else 90

@[expose] def ptIndex3 (v : V3) : ℕ := rawIndex3 (normalize3 v)

@[expose] def decode3 (i : ℕ) : V3 :=
  if i < 81 then ![1, uncode (i / 9), uncode (i % 9)]
  else if i < 90 then ![0, 1, uncode (i - 81)] else ![0, 0, 1]

theorem rawIndex3_lt (v : V3) : rawIndex3 v < 91 := by
  have := code_lt (v 1)
  have := code_lt (v 2)
  unfold rawIndex3
  split_ifs <;> omega

theorem ptIndex3_lt (v : V3) : ptIndex3 v < 91 := rawIndex3_lt _

theorem lead3_smul {t : F9} (ht : t ≠ 0) (v : V3) : lead3 (t • v) = t * lead3 v := by
  simp only [lead3, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, ht, false_or]
  split_ifs <;> rfl

theorem normalize3_smul {t : F9} (ht : t ≠ 0) (v : V3) : normalize3 (t • v) = normalize3 v := by
  rw [normalize3, normalize3, lead3_smul ht, smul_smul, mul_inv, mul_comm t⁻¹, mul_assoc,
    inv_mul_cancel₀ ht, mul_one]

theorem ptIndex3_smul {t : F9} (ht : t ≠ 0) (v : V3) : ptIndex3 (t • v) = ptIndex3 v := by
  rw [ptIndex3, ptIndex3, normalize3_smul ht]

theorem decode3_ne_zero (i : ℕ) : decode3 i ≠ 0 := by
  intro h
  unfold decode3 at h
  split_ifs at h
  · exact one_ne_zero (congrFun h 0)
  · exact one_ne_zero (congrFun h 1)
  · exact one_ne_zero (congrFun h 2)

theorem ptIndex3_decode3 : ∀ i : Fin 91, ptIndex3 (decode3 i) = i := by
  decide +kernel

abbrev Pt3 : Type := ℙ F9 V3

@[expose] def ptFin3 : Pt3 → Fin 91 :=
  Projectivization.lift (fun v => ⟨ptIndex3 v.1, ptIndex3_lt _⟩) fun a b t h => by
    have ht : t ≠ 0 := by
      rintro rfl
      exact a.2 (by rw [h, zero_smul])
    exact Fin.ext (by simp only [h, ptIndex3_smul ht])

theorem ptFin3_mk (v : V3) (hv : v ≠ 0) :
    ptFin3 (Projectivization.mk F9 v hv) = ⟨ptIndex3 v, ptIndex3_lt _⟩ := rfl

theorem ptFin3_surjective : Function.Surjective ptFin3 := fun i =>
  ⟨Projectivization.mk F9 (decode3 i) (decode3_ne_zero i), Fin.ext (ptIndex3_decode3 i)⟩

theorem card_pt3 : Nat.card Pt3 = 91 := by
  rw [Projectivization.card'', Nat.card_fun, Nat.card_eq_fintype_card, F9.card_eq]
  simp

instance : Finite Pt3 := Nat.finite_of_card_ne_zero (by rw [card_pt3]; norm_num)

@[expose] noncomputable def ptEquiv3 : Pt3 ≃ Fin 91 :=
  Equiv.ofBijective ptFin3 (ptFin3_surjective.bijective_of_nat_card_le (by simp [card_pt3]))

theorem ptEquiv3_apply (p : Pt3) : ptEquiv3 p = ptFin3 p := rfl

theorem ptEquiv3_symm_apply (i : Fin 91) :
    ptEquiv3.symm i = Projectivization.mk F9 (decode3 i) (decode3_ne_zero i) := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (ptIndex3_decode3 i).symm

@[expose] noncomputable def rhoSL3 : SpecialLinearGroup (Fin 3) F9 →* Equiv.Perm Pt3 :=
  (MulAction.toPermHom (GL (Fin 3) F9) Pt3).comp SpecialLinearGroup.toGL

theorem rhoSL3_mk (A : SpecialLinearGroup (Fin 3) F9) (v : V3) (hv : v ≠ 0) :
    rhoSL3 A (Projectivization.mk F9 v hv) = Projectivization.mk F9
      (((SpecialLinearGroup.toGL A : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) *ᵥ v)
      ((smul_ne_zero_iff_ne (SpecialLinearGroup.toGL A : GL (Fin 3) F9)).mpr hv) :=
  rfl

theorem le_ker_rhoSL3 : scalars 3 F9 ≤ rhoSL3.ker := by
  rintro A ⟨c, -, hc⟩
  rw [MonoidHom.mem_ker]
  ext p
  induction p using Projectivization.ind with
  | h v hv =>
    rw [rhoSL3_mk, Equiv.Perm.one_apply, Projectivization.mk_eq_mk_iff]
    refine ⟨c, ?_⟩
    have hA : ((SpecialLinearGroup.toGL A : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) =
        Matrix.scalar (Fin 3) (c : F9) := hc
    rw [hA]
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, Units.smul_def]

@[expose] noncomputable def rho3 : projectiveSL 3 F9 →* Equiv.Perm Pt3 :=
  QuotientGroup.lift _ rhoSL3 le_ker_rhoSL3

@[expose] noncomputable def psiL : projectiveSL 3 F9 →* Equiv.Perm (Fin 91) :=
  (Equiv.permCongrHom ptEquiv3).toMonoidHom.comp rho3

theorem psiL_proj_apply (A : SpecialLinearGroup (Fin 3) F9) (i : Fin 91) :
    (psiL (proj 3 F9 A) i : ℕ) =
      ptIndex3 (((SpecialLinearGroup.toGL A : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) *ᵥ
        decode3 i) := by
  have h1 : psiL (proj 3 F9 A) i = ptEquiv3 (rhoSL3 A (ptEquiv3.symm i)) := by
    simp only [psiL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Equiv.permCongrHom_coe, Equiv.permCongr_apply, rho3, proj, QuotientGroup.mk'_apply,
      QuotientGroup.lift_mk]
  rw [h1, ptEquiv3_symm_apply, rhoSL3_mk, ptEquiv3_apply, ptFin3_mk]

end CFSG.EvenSmallLie.Child3.SelL39

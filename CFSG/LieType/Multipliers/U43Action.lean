module

public import CFSG.LieType.Multipliers.U43Field
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LieType.Multipliers.U43

open CFSG.Assembly.LowTwoRank Matrix
open scoped LinearAlgebra.Projectivization

abbrev V : Type := Fin 4 → F9

abbrev X₀ : Type := StatedProj (StatedSU 4 3 F9)

@[expose] def lead (v : V) : F9 :=
  if v 0 ≠ 0 then v 0 else if v 1 ≠ 0 then v 1 else if v 2 ≠ 0 then v 2 else v 3

@[expose] def normalize (v : V) : V := (lead v)⁻¹ • v

@[expose] def code (a : F9) : ℕ := 3 * a.re.val + a.im.val

@[expose] def rawIndex (v : V) : ℕ :=
  if v 0 ≠ 0 then 81 * code (v 1) + 9 * code (v 2) + code (v 3)
  else if v 1 ≠ 0 then 729 + 9 * code (v 2) + code (v 3)
  else if v 2 ≠ 0 then 810 + code (v 3) else 819

@[expose] def ptIndex (v : V) : ℕ := rawIndex (normalize v)

@[expose] def uncode (c : ℕ) : F9 := ⟨((c / 3 : ℕ) : ZMod 3), ((c % 3 : ℕ) : ZMod 3)⟩

@[expose] def decode (i : ℕ) : V :=
  if i < 729 then ![1, uncode (i / 81), uncode (i / 9 % 9), uncode (i % 9)]
  else if i < 810 then ![0, 1, uncode ((i - 729) / 9), uncode ((i - 729) % 9)]
  else if i < 819 then ![0, 0, 1, uncode (i - 810)] else ![0, 0, 0, 1]

theorem code_lt (a : F9) : code a < 9 := by
  have h1 := ZMod.val_lt a.re
  have h2 := ZMod.val_lt a.im
  unfold code
  omega

theorem rawIndex_lt (v : V) : rawIndex v < 820 := by
  have := code_lt (v 1)
  have := code_lt (v 2)
  have := code_lt (v 3)
  unfold rawIndex
  split_ifs <;> omega

theorem ptIndex_lt (v : V) : ptIndex v < 820 := rawIndex_lt _

theorem lead_smul {t : F9} (ht : t ≠ 0) (v : V) : lead (t • v) = t * lead v := by
  simp only [lead, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, ht, false_or]
  split_ifs <;> rfl

theorem normalize_smul {t : F9} (ht : t ≠ 0) (v : V) : normalize (t • v) = normalize v := by
  rw [normalize, normalize, lead_smul ht, smul_smul, mul_inv, mul_comm t⁻¹, mul_assoc,
    inv_mul_cancel₀ ht, mul_one]

theorem ptIndex_smul {t : F9} (ht : t ≠ 0) (v : V) : ptIndex (t • v) = ptIndex v := by
  rw [ptIndex, ptIndex, normalize_smul ht]

theorem decode_ne_zero (i : ℕ) : decode i ≠ 0 := by
  intro h
  unfold decode at h
  split_ifs at h
  · exact one_ne_zero (congrFun h 0)
  · exact one_ne_zero (congrFun h 1)
  · exact one_ne_zero (congrFun h 2)
  · exact one_ne_zero (congrFun h 3)

theorem ptIndex_decode : ∀ i : Fin 820, ptIndex (decode i) = i := by
  decide +kernel

abbrev Pt : Type := ℙ F9 V

@[expose] def ptFin : Pt → Fin 820 :=
  Projectivization.lift (fun v => ⟨ptIndex v.1, ptIndex_lt _⟩) fun a b t h => by
    have ht : t ≠ 0 := by
      rintro rfl
      exact a.2 (by rw [h, zero_smul])
    exact Fin.ext (by simp only [h, ptIndex_smul ht])

theorem ptFin_mk (v : V) (hv : v ≠ 0) : ptFin (Projectivization.mk F9 v hv) = ⟨ptIndex v,
    ptIndex_lt _⟩ := rfl

theorem ptFin_surjective : Function.Surjective ptFin := fun i =>
  ⟨Projectivization.mk F9 (decode i) (decode_ne_zero i), Fin.ext (ptIndex_decode i)⟩

theorem card_pt : Nat.card Pt = 820 := by
  rw [Projectivization.card'', Nat.card_fun, Nat.card_eq_fintype_card, F9.card_eq]
  simp

instance : Finite Pt := Nat.finite_of_card_ne_zero (by rw [card_pt]; norm_num)

@[expose] noncomputable def ptEquiv : Pt ≃ Fin 820 :=
  Equiv.ofBijective ptFin (ptFin_surjective.bijective_of_nat_card_le (by simp [card_pt]))

theorem ptEquiv_apply (p : Pt) : ptEquiv p = ptFin p := rfl

theorem ptEquiv_symm_apply (i : Fin 820) :
    ptEquiv.symm i = Projectivization.mk F9 (decode i) (decode_ne_zero i) := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (ptIndex_decode i).symm

@[expose] noncomputable def rhoSU : StatedSU 4 3 F9 →* Equiv.Perm Pt :=
  (MulAction.toPermHom (GL (Fin 4) F9) Pt).comp (StatedSU 4 3 F9).subtype

theorem gl_smul_vec (A : GL (Fin 4) F9) (v : V) : A • v = (A : Matrix (Fin 4) (Fin 4) F9) *ᵥ v :=
  rfl

theorem rhoSU_mk (A : StatedSU 4 3 F9) (v : V) (hv : v ≠ 0) :
    rhoSU A (Projectivization.mk F9 v hv) = Projectivization.mk F9
      (((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) *ᵥ v)
      ((smul_ne_zero_iff_ne (A : GL (Fin 4) F9)).mpr hv) :=
  rfl

theorem le_ker_rhoSU : (StatedScalars (Fin 4) F9).subgroupOf (StatedSU 4 3 F9) ≤ rhoSU.ker := by
  intro A hA
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hA
  obtain ⟨c, hc⟩ := hA
  rw [MonoidHom.mem_ker]
  ext p
  induction p using Projectivization.ind with
  | h v hv =>
    rw [rhoSU_mk, Equiv.Perm.one_apply, Projectivization.mk_eq_mk_iff]
    refine ⟨c, ?_⟩
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, Units.smul_def]

@[expose] noncomputable def rho : X₀ →* Equiv.Perm Pt := QuotientGroup.lift _ rhoSU le_ker_rhoSU

@[expose] noncomputable def psi : X₀ →* Equiv.Perm (Fin 820) :=
  (Equiv.permCongrHom ptEquiv).toMonoidHom.comp rho

theorem psi_mk_apply (A : StatedSU 4 3 F9) (i : Fin 820) :
    (psi (QuotientGroup.mk A) i : ℕ) =
      ptIndex (((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) *ᵥ decode i) := by
  have h1 : psi (QuotientGroup.mk A) i = ptEquiv (rhoSU A (ptEquiv.symm i)) := by
    simp only [psi, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Equiv.permCongrHom_coe, Equiv.permCongr_apply, rho, QuotientGroup.lift_mk]
  rw [h1, ptEquiv_symm_apply, rhoSU_mk, ptEquiv_apply, ptFin_mk]

end CFSG.LieType.Multipliers.U43

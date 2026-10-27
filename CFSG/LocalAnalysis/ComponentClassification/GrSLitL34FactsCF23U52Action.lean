module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23U52Points
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.GSThmB.U52

open CFSG.Assembly.LowTwoRank CFSG.Fischer Matrix
open scoped LinearAlgebra.Projectivization

abbrev X₀ : Type := StatedProj (StatedSU 5 2 F4)

abbrev Pt : Type := ℙ F4 V

@[expose] def ptFin : Pt → Fin 341 :=
  Projectivization.lift (fun v => ⟨ptIndex v.1, ptIndex_lt _⟩) fun a b t h => by
    have ht : t ≠ 0 := by
      rintro rfl
      exact a.2 (by rw [h, zero_smul])
    exact Fin.ext (by simp only [h, ptIndex_smul ht])

theorem ptFin_mk (v : V) (hv : v ≠ 0) :
    ptFin (Projectivization.mk F4 v hv) = ⟨ptIndex v, ptIndex_lt _⟩ := rfl

theorem ptFin_surjective : Function.Surjective ptFin := fun i =>
  ⟨Projectivization.mk F4 (decode i) (decode_ne_zero i), Fin.ext (ptIndex_decode i)⟩

theorem card_pt : Nat.card Pt = 341 := by
  rw [Projectivization.card'', Nat.card_fun, Nat.card_eq_fintype_card, F4.card]
  simp

instance : Finite Pt := Nat.finite_of_card_ne_zero (by rw [card_pt]; norm_num)

@[expose] noncomputable def ptEquiv : Pt ≃ Fin 341 :=
  Equiv.ofBijective ptFin (ptFin_surjective.bijective_of_nat_card_le (by simp [card_pt]))

theorem ptEquiv_apply (p : Pt) : ptEquiv p = ptFin p := rfl

theorem ptEquiv_symm_apply (i : Fin 341) :
    ptEquiv.symm i = Projectivization.mk F4 (decode i) (decode_ne_zero i) := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (ptIndex_decode i).symm

@[expose] noncomputable def rhoSU : StatedSU 5 2 F4 →* Equiv.Perm Pt :=
  (MulAction.toPermHom (GL (Fin 5) F4) Pt).comp (StatedSU 5 2 F4).subtype

theorem rhoSU_mk (A : StatedSU 5 2 F4) (v : V) (hv : v ≠ 0) :
    rhoSU A (Projectivization.mk F4 v hv) = Projectivization.mk F4
      (((A : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) *ᵥ v)
      ((smul_ne_zero_iff_ne (A : GL (Fin 5) F4)).mpr hv) :=
  rfl

theorem le_ker_rhoSU : (StatedScalars (Fin 5) F4).subgroupOf (StatedSU 5 2 F4) ≤ rhoSU.ker := by
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

@[expose] noncomputable def psi : X₀ →* Equiv.Perm (Fin 341) :=
  (Equiv.permCongrHom ptEquiv).toMonoidHom.comp rho

theorem psi_mk_apply (A : StatedSU 5 2 F4) (i : Fin 341) :
    (psi (QuotientGroup.mk A) i : ℕ) =
      ptIndex (((A : GL (Fin 5) F4) : Matrix (Fin 5) (Fin 5) F4) *ᵥ decode i) := by
  have h1 : psi (QuotientGroup.mk A) i = ptEquiv (rhoSU A (ptEquiv.symm i)) := by
    simp only [psi, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Equiv.permCongrHom_coe, Equiv.permCongr_apply, rho, QuotientGroup.lift_mk]
  rw [h1, ptEquiv_symm_apply, rhoSU_mk, ptEquiv_apply, ptFin_mk]

end CFSG.ComponentClassification.GSThmB.U52

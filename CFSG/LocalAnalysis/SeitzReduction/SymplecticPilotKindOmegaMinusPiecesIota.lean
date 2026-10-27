module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusIota

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus
  commutator_coordinateQuadMinus)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable (k : Type) [Field k] (r : ℕ) {b c : k}

theorem kOmM_quadMinus_vec : quadMinus (r + 1) k b c (kOmMVec k r) = 1 := by
  rw [coe_quadMinus]
  exact kOmM_statedQuadMinus_vec k b c

theorem kOmM_reindexQuadraticForm_vec :
    reindexQuadraticForm (minusIndexEquiv (r + 1) (by omega)) (quadMinus (r + 1) k b c)
      (reindexVectorEquiv (minusIndexEquiv (r + 1) (by omega)) (kOmMVec k r)) = 1 := by
  rw [F4Pilot.reindexQuadraticForm_reindexVectorEquiv, kOmM_quadMinus_vec]

variable [CharP k 2]

variable (b c) in
theorem kOmM_matrixDerivedScalars_eq_bot :
    matrixDerivedScalars (reindexQuadraticForm (minusIndexEquiv (r + 1) (by omega))
      (quadMinus (r + 1) k b c)) = ⊥ :=
  LocalAnalysis.ComponentInitial.UnitaryHigher.matrixDerivedScalars_eq_bot_of_charTwo _
    ⟨_, by rw [kOmM_reindexQuadraticForm_vec]; exact one_ne_zero⟩

variable (b c) in
@[expose] noncomputable def kOmMBetaC : MulAut (StatedOmega (StatedQuadMinus (r + 1) k b c)) :=
  F4Pilot.omegaSymmetryAut (minusIndexEquiv (r + 1) (by omega)) (quadMinus (r + 1) k b c)
    (coe_quadMinus (r + 1) k b c) (kOmM_matrixDerivedScalars_eq_bot k r b c) (kOmMVec k r)

variable {r}

theorem mem_fixedSubgroup_kOmMBetaC_iff [Finite k] (hr : 3 ≤ r)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) (A : StatedOmega (StatedQuadMinus (r + 1) k b c)) :
    A ∈ fixedSubgroup (kOmMBetaC k r b c) ↔
      ((A : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) :
        Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
          (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) *ᵥ kOmMVec k r = kOmMVec k r :=
  F4Pilot.mem_fixedSubgroup_omegaSymmetryAut_iff _ _ _ _ _
    (regular_coordinateQuadMinus (r + 1) k b c (by omega) hirr).1 (kOmM_quadMinus_vec k r) A

theorem coe_mem_kOmMStab [Finite k] (hr : 3 ≤ r) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    {A : StatedOmega (StatedQuadMinus (r + 1) k b c)} (hA : A ∈ fixedSubgroup (kOmMBetaC k r b c)) :
    (A : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) ∈ kOmMStab k r b c :=
  ⟨kOmM_isometry_of_mem A.2, (mem_fixedSubgroup_kOmMBetaC_iff k hr hirr A).1 hA⟩

variable [Finite k] (hr : 3 ≤ r) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def kOmMFixRes : fixedSubgroup (kOmMBetaC k r b c) →* StatedSp r k :=
  (kOmMRes k r (F4Pilot.ne_zero_of_irreducible k hirr)).comp
    ((((StatedOmega (StatedQuadMinus (r + 1) k b c)).subtype.comp
      (fixedSubgroup (kOmMBetaC k r b c)).subtype)).codRestrict (kOmMStab k r b c)
        fun A => coe_mem_kOmMStab k hr hirr A.2)

theorem coe_kOmMFixRes (A : fixedSubgroup (kOmMBetaC k r b c)) :
    (((kOmMFixRes k hr hirr A : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      (((A : StatedOmega (StatedQuadMinus (r + 1) k b c)) :
        GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) :
          Matrix (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2)
            (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k).submatrix (kOmMEmb r) (kOmMEmb r) :=
  rfl

include hr hirr in
theorem nonempty_fixedSubgroup_kOmMBetaC_mulEquiv {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card k = 2 ^ f) : Nonempty (fixedSubgroup (kOmMBetaC k r b c) ≃* StatedSp r k) :=
  F4Pilot.nonempty_fixedSubgroup_omegaSymmetryAut_mulEquiv hf hK (by omega)
    (minusIndexEquiv (r + 1) (by omega)) (quadMinus (r + 1) k b c) (coe_quadMinus (r + 1) k b c)
    (regular_coordinateQuadMinus (r + 1) k b c (by omega) hirr).1
    (regular_coordinateQuadMinus (r + 1) k b c (by omega) hirr).2
    (commutator_coordinateQuadMinus (r + 1) k b c (by omega) hirr)
    (kOmM_matrixDerivedScalars_eq_bot k r b c) (kOmM_quadMinus_vec k r)

theorem kOmMFixRes_injective {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f) :
    Function.Injective (kOmMFixRes k hr hirr) := by
  have hk4 : 4 ≤ Nat.card k := (LinearPilot.four_le_card_iff_two_le hK).2 hf
  obtain ⟨e⟩ := nonempty_fixedSubgroup_kOmMBetaC_mulEquiv k hr hirr (by omega) hK
  have : IsSimpleGroup (StatedSp r k) := isSimpleGroup_statedSp_of_four_le hk4 (by omega)
  have : IsSimpleGroup (fixedSubgroup (kOmMBetaC k r b c)) := e.isSimpleGroup
  rcases (kOmMFixRes k hr hirr).normal_ker.eq_bot_or_eq_top with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    obtain ⟨a, ha⟩ := LieType.Steinberg.CentralExt.SpinTorus.exists_unit_sq_ne_one hk4
    set t : Fin r → kˣ := Pi.mulSingle ⟨0, by omega⟩ a with htdef
    have hfix : (⟨kOmMDiag k r t, kOmMDiag_mem b c t⟩ :
        StatedOmega (StatedQuadMinus (r + 1) k b c)) ∈ fixedSubgroup (kOmMBetaC k r b c) := by
      rw [mem_fixedSubgroup_kOmMBetaC_iff k hr hirr]
      exact kOmMDiag_mulVec_vec t
    have hker : (⟨_, hfix⟩ : fixedSubgroup (kOmMBetaC k r b c)) ∈ (kOmMFixRes k hr hirr).ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hker
    have h1 := congrArg (fun A : StatedSp r k =>
      ((A : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
        (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) hker
    simp only [coe_kOmMFixRes, submatrix_apply, OneMemClass.coe_one, Units.val_one,
      one_apply_eq] at h1
    rw [kOmMEmb_inl, kOmMDiag_apply_self, kOmMWeight_inl, htdef, Pi.mulSingle_eq_same] at h1
    apply ha
    rw [Units.val_eq_one.mp h1, one_pow]

theorem kOmMFixRes_bijective {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f) :
    Function.Bijective (kOmMFixRes k hr hirr) := by
  obtain ⟨e⟩ := nonempty_fixedSubgroup_kOmMBetaC_mulEquiv k hr hirr (by omega) hK
  exact (kOmMFixRes_injective k hr hirr hK hf).bijective_of_nat_card_le
    (Nat.card_congr e.toEquiv).ge

section Iota

variable {k} {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f)

@[expose] noncomputable def kOmMIota :
    StatedSp r k →* StatedOmega (StatedQuadMinus (r + 1) k b c) :=
  (fixedSubgroup (kOmMBetaC k r b c)).subtype.comp
    (MulEquiv.ofBijective (kOmMFixRes k hr hirr)
      (kOmMFixRes_bijective k hr hirr hK hf)).symm.toMonoidHom

theorem kOmMIota_injective : Function.Injective (kOmMIota hr hirr hK hf) :=
  (fixedSubgroup _).subtype_injective.comp (MulEquiv.injective _)

theorem range_kOmMIota :
    (kOmMIota hr hirr hK hf).range = fixedSubgroup (kOmMBetaC k r b c) := by
  rw [kOmMIota, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
    ← MonoidHom.range_eq_map, range_subtype]

theorem kOmMIota_eq_of_res {g : StatedSp r k} {y : fixedSubgroup (kOmMBetaC k r b c)}
    (hy : kOmMFixRes k hr hirr y = g) : kOmMIota hr hirr hK hf g = y := by
  change (((MulEquiv.ofBijective (kOmMFixRes k hr hirr)
    (kOmMFixRes_bijective k hr hirr hK hf)).symm g : fixedSubgroup (kOmMBetaC k r b c)) :
      StatedOmega (StatedQuadMinus (r + 1) k b c)) = y
  rw [(MulEquiv.symm_apply_eq _).mpr hy.symm]

theorem coe_kOmMIota_diagSp (t : Fin r → kˣ) :
    ((kOmMIota hr hirr hK hf (diagSp k r t) : StatedOmega (StatedQuadMinus (r + 1) k b c)) :
      GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) k) = kOmMDiag k r t := by
  have hfix : (⟨kOmMDiag k r t, kOmMDiag_mem b c t⟩ :
      StatedOmega (StatedQuadMinus (r + 1) k b c)) ∈ fixedSubgroup (kOmMBetaC k r b c) := by
    rw [mem_fixedSubgroup_kOmMBetaC_iff k hr hirr]
    exact kOmMDiag_mulVec_vec t
  rw [kOmMIota_eq_of_res hr hirr hK hf (y := ⟨_, hfix⟩)]
  apply mat_injective
  rw [mat_diagSp, CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_kOmMFixRes]
  ext i j
  simp only [submatrix_apply, kOmMDiag_coe, diagonal_apply, kOmMEmb_injective.eq_iff]
  split_ifs with hij
  · subst hij
    rcases i with i | i
    · simp
      rfl
    · simp
      exact Units.val_inv_eq_inv_val (t i)
  · rfl

end Iota

end CFSG.SeitzReduction.SymplecticPilot

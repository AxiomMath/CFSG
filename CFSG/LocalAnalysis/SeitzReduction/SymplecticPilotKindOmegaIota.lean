module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPiecesOrders
public import CFSG.LieType.Steinberg.CentralExt.SpinTorus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus
  commutator_coordinateQuadPlus)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.SeitzReduction.OmegaPilot (diagOmega isometry_of_mem_isometryClosure diagOmega_coe)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable (k : Type) [Field k] (r : ℕ)

theorem kOmega_quadPlus_vec : quadPlus (r + 1) k (kOmegaVec k r) = 1 := by
  rw [coe_quadPlus]
  exact kOmega_statedQuadPlus_vec k

theorem kOmega_reindexQuadraticForm_vec :
    reindexQuadraticForm (plusIndexEquiv (r + 1)) (quadPlus (r + 1) k)
      (reindexVectorEquiv (plusIndexEquiv (r + 1)) (kOmegaVec k r)) = 1 := by
  rw [F4Pilot.reindexQuadraticForm_reindexVectorEquiv,
    kOmega_quadPlus_vec]

variable [CharP k 2]

theorem kOmega_matrixDerivedScalars_eq_bot :
    matrixDerivedScalars (reindexQuadraticForm (plusIndexEquiv (r + 1)) (quadPlus (r + 1) k)) =
      ⊥ :=
  LocalAnalysis.ComponentInitial.UnitaryHigher.matrixDerivedScalars_eq_bot_of_charTwo _
    ⟨_, by rw [kOmega_reindexQuadraticForm_vec]; exact one_ne_zero⟩

@[expose] noncomputable def kOmegaBetaC : MulAut (StatedOmega (StatedQuadPlus (r + 1) k)) :=
  F4Pilot.omegaSymmetryAut (plusIndexEquiv (r + 1)) (quadPlus (r + 1) k) (coe_quadPlus (r + 1) k)
    (kOmega_matrixDerivedScalars_eq_bot k r) (kOmegaVec k r)

variable {r}

theorem mem_fixedSubgroup_kOmegaBetaC_iff (hr : 2 ≤ r)
    (A : StatedOmega (StatedQuadPlus (r + 1) k)) :
    A ∈ fixedSubgroup (kOmegaBetaC k r) ↔
      ((A : GL (Fin (r + 1) ⊕ Fin (r + 1)) k) :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k) *ᵥ kOmegaVec k r =
        kOmegaVec k r :=
  F4Pilot.mem_fixedSubgroup_omegaSymmetryAut_iff _ _ _ _ _
    (regular_coordinateQuadPlus (r + 1) k (by omega)).1 (kOmega_quadPlus_vec k r) A

omit [CharP k 2] in
theorem kOmega_isometry_of_mem (A : StatedOmega (StatedQuadPlus (r + 1) k))
    (x : Fin (r + 1) ⊕ Fin (r + 1) → k) :
    StatedQuadPlus (r + 1) k
      (((A : GL (Fin (r + 1) ⊕ Fin (r + 1)) k) :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k) *ᵥ x) =
        StatedQuadPlus (r + 1) k x :=
  isometry_of_mem_isometryClosure (Subgroup.commutator_le_self _ A.2) x

theorem coe_mem_kOmegaStab (hr : 2 ≤ r) {A : StatedOmega (StatedQuadPlus (r + 1) k)}
    (hA : A ∈ fixedSubgroup (kOmegaBetaC k r)) :
    (A : GL (Fin (r + 1) ⊕ Fin (r + 1)) k) ∈ kOmegaStab k r :=
  ⟨kOmega_isometry_of_mem k A, (mem_fixedSubgroup_kOmegaBetaC_iff k hr A).1 hA⟩

variable (hr : 2 ≤ r)

@[expose] noncomputable def kOmegaFixRes : fixedSubgroup (kOmegaBetaC k r) →* StatedSp r k :=
  (kOmegaRes k r).comp ((((StatedOmega (StatedQuadPlus (r + 1) k)).subtype.comp
    (fixedSubgroup (kOmegaBetaC k r)).subtype)).codRestrict (kOmegaStab k r)
      fun A => coe_mem_kOmegaStab k hr A.2)

theorem coe_kOmegaFixRes (A : fixedSubgroup (kOmegaBetaC k r)) :
    (((kOmegaFixRes k hr A : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      (((A : StatedOmega (StatedQuadPlus (r + 1) k)) : GL (Fin (r + 1) ⊕ Fin (r + 1)) k) :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k).submatrix
          (kOmegaEmb r) (kOmegaEmb r) := rfl

variable [Finite k]

theorem nonempty_fixedSubgroup_kOmegaBetaC_mulEquiv (hr3 : 3 ≤ r) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card k = 2 ^ f) : Nonempty (fixedSubgroup (kOmegaBetaC k r) ≃* StatedSp r k) :=
  F4Pilot.nonempty_fixedSubgroup_omegaSymmetryAut_mulEquiv hf hK (by omega)
    (plusIndexEquiv (r + 1)) (quadPlus (r + 1) k) (coe_quadPlus (r + 1) k)
    (regular_coordinateQuadPlus (r + 1) k (by omega)).1
    (regular_coordinateQuadPlus (r + 1) k (by omega)).2
    (commutator_coordinateQuadPlus (r + 1) k (by omega))
    (kOmega_matrixDerivedScalars_eq_bot k r) (kOmega_quadPlus_vec k r)

omit [CharP k 2] [Finite k] in
theorem kOmega_diagOmega_mulVec_vec {t : Fin (r + 1) → kˣ} (ht : t (Fin.last r) = 1) :
    (diagOmega k (r + 1) t : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k) *ᵥ
        kOmegaVec k r = kOmegaVec k r := by
  rw [diagOmega_coe]
  funext i
  rw [mulVec_diagonal]
  rcases i with i | i
  · rw [kOmegaVec_inl]
    by_cases hi : i = Fin.last r
    · subst hi
      simp [ht]
    · simp [hi]
  · rw [kOmegaVec_inr]
    by_cases hi : i = Fin.last r
    · subst hi
      simp [ht]
    · simp [hi]

theorem kOmegaFixRes_injective (hr3 : 3 ≤ r) {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f) :
    Function.Injective (kOmegaFixRes k hr) := by
  have hk4 : 4 ≤ Nat.card k := (LinearPilot.four_le_card_iff_two_le hK).2 hf
  obtain ⟨e⟩ := nonempty_fixedSubgroup_kOmegaBetaC_mulEquiv k hr3 (by omega) hK
  have : IsSimpleGroup (StatedSp r k) := isSimpleGroup_statedSp_of_four_le hk4 (by omega)
  have : IsSimpleGroup (fixedSubgroup (kOmegaBetaC k r)) := e.isSimpleGroup
  rcases (kOmegaFixRes k hr).normal_ker.eq_bot_or_eq_top with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    obtain ⟨a, ha⟩ := LieType.Steinberg.CentralExt.SpinTorus.exists_unit_sq_ne_one hk4
    set t : Fin (r + 1) → kˣ := Pi.mulSingle 0 a with htdef
    have hfix : (⟨diagOmega k (r + 1) t, F4Pilot.diagOmega_mem_statedOmega t⟩ :
        StatedOmega (StatedQuadPlus (r + 1) k)) ∈ fixedSubgroup (kOmegaBetaC k r) := by
      rw [mem_fixedSubgroup_kOmegaBetaC_iff k hr]
      refine kOmega_diagOmega_mulVec_vec k ?_
      rw [htdef, Pi.mulSingle_eq_of_ne]
      intro h0
      have := congrArg Fin.val h0
      simp only [Fin.val_last, Fin.val_zero] at this
      omega
    have hker : (⟨_, hfix⟩ : fixedSubgroup (kOmegaBetaC k r)) ∈ (kOmegaFixRes k hr).ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hker
    have h1 := congrArg (fun A : StatedSp r k =>
      ((A : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
        (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) hker
    simp only [coe_kOmegaFixRes, submatrix_apply, diagOmega_coe, OneMemClass.coe_one,
      Units.val_one, one_apply_eq] at h1
    rw [diagonal_apply_eq, kOmegaEmb, Sum.map_inl, diagSpEntry_inl, htdef] at h1
    have h2 : (Fin.castSucc (⟨0, by omega⟩ : Fin r) : Fin (r + 1)) = 0 := rfl
    rw [h2, Pi.mulSingle_eq_same] at h1
    apply ha
    rw [Units.val_eq_one.mp h1, one_pow]

theorem kOmegaFixRes_bijective (hr3 : 3 ≤ r) {f : ℕ} (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f) :
    Function.Bijective (kOmegaFixRes k hr) := by
  obtain ⟨e⟩ := nonempty_fixedSubgroup_kOmegaBetaC_mulEquiv k hr3 (by omega) hK
  exact (kOmegaFixRes_injective k hr hr3 hK hf).bijective_of_nat_card_le
    (Nat.card_congr e.toEquiv).ge

@[expose] def kOmegaSnoc (t : Fin r → kˣ) : Fin (r + 1) → kˣ := Fin.snoc (α := fun _ => kˣ) t 1

omit [CharP k 2] [Finite k] in
@[simp] theorem kOmegaSnoc_castSucc (t : Fin r → kˣ) (i : Fin r) :
    kOmegaSnoc k t (Fin.castSucc i) = t i := Fin.snoc_castSucc (α := fun _ => kˣ) _ _ _

omit [CharP k 2] [Finite k] in
@[simp] theorem kOmegaSnoc_last (t : Fin r → kˣ) : kOmegaSnoc k t (Fin.last r) = 1 :=
  Fin.snoc_last (α := fun _ => kˣ) _ _

section Iota

variable {k} {f : ℕ} (hr3 : 3 ≤ r) (hK : Nat.card k = 2 ^ f) (hf : 2 ≤ f)

@[expose] noncomputable def kOmegaIota : StatedSp r k →* StatedOmega (StatedQuadPlus (r + 1) k) :=
  (fixedSubgroup (kOmegaBetaC k r)).subtype.comp
    (MulEquiv.ofBijective (kOmegaFixRes k hr)
      (kOmegaFixRes_bijective k hr hr3 hK hf)).symm.toMonoidHom

theorem kOmegaIota_injective : Function.Injective (kOmegaIota hr hr3 hK hf) :=
  (fixedSubgroup _).subtype_injective.comp (MulEquiv.injective _)

theorem range_kOmegaIota :
    (kOmegaIota hr hr3 hK hf).range = fixedSubgroup (kOmegaBetaC k r) := by
  rw [kOmegaIota, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
    ← MonoidHom.range_eq_map, range_subtype]

theorem kOmegaIota_eq_of_res {g : StatedSp r k} {y : fixedSubgroup (kOmegaBetaC k r)}
    (hy : kOmegaFixRes k hr y = g) : kOmegaIota hr hr3 hK hf g = y := by
  change (((MulEquiv.ofBijective (kOmegaFixRes k hr)
    (kOmegaFixRes_bijective k hr hr3 hK hf)).symm g : fixedSubgroup (kOmegaBetaC k r)) :
      StatedOmega (StatedQuadPlus (r + 1) k)) = y
  rw [(MulEquiv.symm_apply_eq _).mpr hy.symm]

theorem coe_kOmegaIota_diagSp (t : Fin r → kˣ) :
    ((kOmegaIota hr hr3 hK hf (diagSp k r t) : StatedOmega (StatedQuadPlus (r + 1) k)) :
      GL (Fin (r + 1) ⊕ Fin (r + 1)) k) = diagOmega k (r + 1) (kOmegaSnoc k t) := by
  have hfix : (⟨diagOmega k (r + 1) (kOmegaSnoc k t), F4Pilot.diagOmega_mem_statedOmega _⟩ :
      StatedOmega (StatedQuadPlus (r + 1) k)) ∈ fixedSubgroup (kOmegaBetaC k r) := by
    rw [mem_fixedSubgroup_kOmegaBetaC_iff k hr]
    exact kOmega_diagOmega_mulVec_vec k (kOmegaSnoc_last k t)
  rw [kOmegaIota_eq_of_res hr hr3 hK hf (y := ⟨_, hfix⟩)]
  apply mat_injective
  rw [mat_diagSp, CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_kOmegaFixRes]
  ext i j
  simp only [submatrix_apply, diagOmega_coe, diagonal_apply, kOmegaEmb_injective.eq_iff]
  split_ifs with hij
  · subst hij
    rcases i with i | i
    · simp [kOmegaEmb]
    · simp [kOmegaEmb]
  · rfl

end Iota

end CFSG.SeitzReduction.SymplecticPilot

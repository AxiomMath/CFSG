module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MHerm3SU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MClassModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MHerm3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Matrix
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary CFSG.Blueprint

open scoped commutatorElement

private theorem conjTr_scalar_three (c : F9) :
    conjTr σ9 (Matrix.scalar (Fin 3) c) = Matrix.scalar (Fin 3) (σ9 c) := by
  rw [conjTr, Matrix.scalar_apply, Matrix.diagonal_map (map_zero σ9), Matrix.diagonal_transpose,
    Matrix.scalar_apply]

private theorem det_conjTr_three (M : Matrix (Fin 3) (Fin 3) F9) :
    (conjTr σ9 M).det = σ9 M.det := by
  rw [conjTr, Matrix.det_transpose]
  exact (RingHom.map_det σ9.toRingHom M).symm

private theorem σ9_eq_cube (z : F9) : σ9 z = z ^ 3 := by
  rw [σ9, unitaryInvolution_apply]
  norm_num

private theorem conjTr_scalar_mul_self_three (u : F9ˣ)
    (hu : σ9 (u : F9) * (u : F9) = 1) :
    conjTr σ9 (Matrix.scalar (Fin 3) (u : F9)) * Matrix.scalar (Fin 3) (u : F9) = 1 := by
  rw [conjTr_scalar_three, ← map_mul]
  show Matrix.scalar (Fin 3) (σ9 (u : F9) * (u : F9)) = 1
  rw [hu, map_one]

private theorem scalar_mem_uid_three (u : F9ˣ)
    (hu : σ9 (u : F9) * (u : F9) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ Uid σ9 3 := by
  rw [mem_Uid_iff]
  exact conjTr_scalar_mul_self_three u hu

private theorem det_scalar_three (u : F9ˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = u ^ 3 := by
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem scalar_mul_mem_SUid (A : Uid σ9 3) (u : F9ˣ)
    (hu : σ9 (u : F9) * (u : F9) = 1)
    (hdet : (u : F9) ^ 3 * ((A : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9).det = 1) :
    (Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) F9)) ∈ SUid σ9 3 := by
  refine (mem_SUid (σ := σ9)).mpr ⟨?_, ?_⟩
  · have hBdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) u *
        (A : GL (Fin 3) F9)) = u ^ 3 * (A : GL (Fin 3) F9).det := by
      rw [map_mul, det_scalar_three]
    have hval : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) u *
        (A : GL (Fin 3) F9)) : F9ˣ) : F9) = 1 := by
      rw [hBdet, Units.val_mul, Units.val_pow_eq_pow_val]
      exact hdet
    exact hval
  · set S : Matrix (Fin 3) (Fin 3) F9 := Matrix.scalar (Fin 3) (u : F9)
    set Am : Matrix (Fin 3) (Fin 3) F9 := ((A : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9)
    have hS : conjTr σ9 S * S = 1 := conjTr_scalar_mul_self_three u hu
    have hU : conjTr σ9 Am * Am = 1 := (mem_Uid_iff σ9 3 (A : GL (Fin 3) F9)).mp A.2
    change conjTr σ9 (S * Am) * (S * Am) = 1
    calc conjTr σ9 (S * Am) * (S * Am)
        = (conjTr σ9 Am * conjTr σ9 S) * (S * Am) := by rw [conjTr_mul]
      _ = conjTr σ9 Am * (conjTr σ9 S * (S * Am)) :=
            Matrix.mul_assoc (conjTr σ9 Am) (conjTr σ9 S) (S * Am)
      _ = conjTr σ9 Am * ((conjTr σ9 S * S) * Am) := by
            rw [← Matrix.mul_assoc (conjTr σ9 S) S Am]
      _ = conjTr σ9 Am * (1 * Am) := by rw [hS]
      _ = 1 := by rw [Matrix.one_mul, hU]

private noncomputable def scU (u : F9ˣ) : Uid σ9 3 :=
  if h : σ9 (u : F9) * (u : F9) = 1 then
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u, scalar_mem_uid_three u h⟩
  else 1

private noncomputable def scG (u : F9ˣ) : OGroup (hermForm 3) := uidToOrth 3 (scU u)

private theorem scU_of_norm (u : F9ˣ) (hu : σ9 (u : F9) * (u : F9) = 1) :
    scU u = (⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u, scalar_mem_uid_three u hu⟩ :
      Uid σ9 3) := by
  rw [scU, dif_pos hu]

private theorem scG_of_norm (u : F9ˣ) (hu : σ9 (u : F9) * (u : F9) = 1) :
    scG u = uidToOrth 3 (⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u,
      scalar_mem_uid_three u hu⟩ : Uid σ9 3) := by
  rw [scG, scU_of_norm u hu]

private theorem suToOrth3_mk (A : Uid σ9 3)
    (hA : (A : GL (Fin 3) F9) ∈ SUid σ9 3) :
    suToOrth3 (⟨(A : GL (Fin 3) F9), hA⟩ : Su F9 3 1 3) = uidToOrth 3 A := rfl

private theorem commutatorElement_mem_SUid3 (A B : Uid σ9 3) :
    ((⁅A, B⁆ : Uid σ9 3) : GL (Fin 3) F9) ∈ SUid σ9 3 := by
  have h : ⁅A, B⁆ ∈ specialUnitary σ9 3 := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  rw [specialUnitary_eq_subgroupOf, Subgroup.mem_subgroupOf] at h
  exact h

private theorem scG_mul (u v : F9ˣ) (hu : σ9 (u : F9) * (u : F9) = 1)
    (hv : σ9 (v : F9) * (v : F9) = 1)
    (huv : σ9 ((u * v : F9ˣ) : F9) * ((u * v : F9ˣ) : F9) = 1) :
    scG u * scG v = scG (u * v) := by
  rw [scG_of_norm u hu, scG_of_norm v hv, scG_of_norm (u * v) huv, ← map_mul]
  congr 1
  apply Subtype.ext
  change Matrix.GeneralLinearGroup.scalar (Fin 3) u *
      Matrix.GeneralLinearGroup.scalar (Fin 3) v =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (u * v)
  rw [map_mul]

private theorem scG_neg_one (h : σ9 (-1 : F9) * (-1 : F9) = 1) :
    scG (-1 : F9ˣ) = piOrth (hermForm 3) := by
  rw [scG_of_norm (-1) h]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  rw [coe_uidToOrth, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mulVec_diagonal, coe_piOrth_apply]
  simp [Pi.neg_apply]

private theorem fourth_root_cases {d : F9} (h : d ^ 4 = 1) :
    d = 1 ∨ d = -1 ∨ d = omega9 ∨ d = -omega9 := by
  have hω2 : omega9 ^ 2 = -1 := by rw [pow_two, omega9_mul_omega9]
  have hfac : (d - 1) * (d + 1) * (d - omega9) * (d + omega9) = 0 := by
    calc (d - 1) * (d + 1) * (d - omega9) * (d + omega9)
        = (d ^ 2 - 1) * (d ^ 2 - omega9 ^ 2) := by ring
      _ = (d ^ 2 - 1) * (d ^ 2 + 1) := by rw [hω2]; ring
      _ = d ^ 4 - 1 := by ring
      _ = 0 := by rw [h, sub_self]
  rcases mul_eq_zero.mp hfac with h0 | h0
  · rcases mul_eq_zero.mp h0 with h0 | h0
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact Or.inl (sub_eq_zero.mp h0)
      · exact Or.inr (Or.inl (by linear_combination h0))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h0)))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h0)))

theorem herm3_centralizer_eq :
    Subgroup.centralizer ({omegaOrth 3} : Set (OGroup (hermForm 3))) = (uidToOrth 3).range := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_range]
  constructor
  · intro hg
    exact exists_uid_of_comm hg
  · rintro ⟨A, rfl⟩
    exact uidToOrth_comm_omega A

theorem herm3_derived_eq :
    ⁅Subgroup.centralizer ({omegaOrth 3} : Set (OGroup (hermForm 3))),
      Subgroup.centralizer ({omegaOrth 3} : Set (OGroup (hermForm 3)))⁆ = suToOrth3.range := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [herm3_centralizer_eq, MonoidHom.mem_range] at ha hb
    obtain ⟨A, rfl⟩ := ha
    obtain ⟨B, rfl⟩ := hb
    rw [← map_commutatorElement (f := uidToOrth 3)]
    exact ⟨⟨((⁅A, B⁆ : Uid σ9 3) : GL (Fin 3) F9),
      commutatorElement_mem_SUid3 A B⟩, suToOrth3_mk ⁅A, B⁆ (commutatorElement_mem_SUid3 A B)⟩
  · have hle : suToOrth3.range ≤
        Subgroup.centralizer ({omegaOrth 3} : Set (OGroup (hermForm 3))) := by
      rw [herm3_centralizer_eq]
      rintro _ ⟨s, rfl⟩
      exact ⟨Subgroup.inclusion _ s, rfl⟩
    calc suToOrth3.range = Subgroup.map suToOrth3 ⊤ := (Subgroup.map_top suToOrth3).symm
      _ = Subgroup.map suToOrth3 (commutator (Su F9 3 1 3)) := by rw [su3_commutator_eq_top]
      _ = Subgroup.map suToOrth3 ⁅(⊤ : Subgroup (Su F9 3 1 3)), ⊤⁆ := rfl
      _ = ⁅Subgroup.map suToOrth3 ⊤, Subgroup.map suToOrth3 ⊤⁆ :=
            Subgroup.map_commutator (⊤ : Subgroup (Su F9 3 1 3))
              (⊤ : Subgroup (Su F9 3 1 3)) suToOrth3
      _ = ⁅suToOrth3.range, suToOrth3.range⁆ := by simp [Subgroup.map_top]
      _ ≤ ⁅Subgroup.centralizer ({omegaOrth 3} : Set (OGroup (hermForm 3))),
            Subgroup.centralizer ({omegaOrth 3} : Set (OGroup (hermForm 3)))⁆ :=
          Subgroup.commutator_mono hle hle

theorem herm3_lieModel_derived :
    LieModel ↥⁅Subgroup.centralizer ({omegaOrth 3} : Set (OGroup (hermForm 3))),
      Subgroup.centralizer ({omegaOrth 3} : Set (OGroup (hermForm 3)))⁆ .PSU 3 3 1 := by
  rw [herm3_derived_eq]
  exact LieModel.of_mulEquiv (MonoidHom.ofInjective suToOrth3_injective) su3_lieModel

theorem herm3_mem_cases {g : OGroup (hermForm 3)}
    (hg : g ∈ omegaGroup (hermForm_nondegenerate 3))
    (hC : g ∈ Subgroup.centralizer ({omegaOrth 3} : Set (OGroup (hermForm 3)))) :
    g ∈ suToOrth3.range ∨ piOrth (hermForm 3) * g ∈ suToOrth3.range := by
  rw [herm3_centralizer_eq, MonoidHom.mem_range] at hC
  obtain ⟨A, rfl⟩ := hC
  let M : Matrix (Fin 3) (Fin 3) F9 := (A : GL (Fin 3) F9)
  let d : F9 := M.det
  have hdA : ((A : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9).det = d := rfl
  have hU : conjTr σ9 M * M = 1 := (mem_Uid_iff σ9 3 (A : GL (Fin 3) F9)).mp A.2
  have hdet1 : (conjTr σ9 M).det * M.det = 1 := by
    have h := congrArg Matrix.det hU
    rwa [Matrix.det_mul, Matrix.det_one] at h
  have hdet2 : σ9 d * d = 1 := by
    rw [det_conjTr_three M] at hdet1
    simpa [d] using hdet1
  have h4 : d ^ 4 = 1 := by
    rw [σ9_eq_cube] at hdet2
    simpa [pow_succ] using hdet2
  have hdim3 : Module.finrank (ZMod 3) (Fin 3 → F9) = 6 := by rw [finrank_hermSpace]
  have hωnorm : σ9 (omegaUnit : F9) * (omegaUnit : F9) = 1 := by
    show σ9 omega9 * omega9 = 1
    rw [σ9_omega, neg_mul, omega9_mul_omega9, neg_neg]
  have hneg : σ9 (-1 : F9) * (-1 : F9) = 1 := by simp
  have hnnorm : σ9 ((-omegaUnit : F9ˣ) : F9) * ((-omegaUnit : F9ˣ) : F9) = 1 := by
    rw [show ((-omegaUnit : F9ˣ) : F9) = -(omegaUnit : F9) from rfl, map_neg, neg_mul, mul_neg,
      neg_neg]
    exact hωnorm
  have hωω : omegaUnit * omegaUnit = (-1 : F9ˣ) := by
    apply Units.ext
    rw [Units.val_mul]
    exact omega9_mul_omega9
  have hsquare_norm : σ9 ((omegaUnit * omegaUnit : F9ˣ) : F9) *
      ((omegaUnit * omegaUnit : F9ˣ) : F9) = 1 := by
    rw [hωω]
    exact hneg
  have step : ∀ (u : F9ˣ), σ9 (u : F9) * (u : F9) = 1 →
      (u : F9) ^ 3 * d = 1 → scG u * uidToOrth 3 A ∈ suToOrth3.range := by
    intro u hu hdet
    have hSU : (Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) F9)) ∈
        SUid σ9 3 := scalar_mul_mem_SUid A u hu (by rw [hdA]; exact hdet)
    refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) F9), hSU⟩, ?_⟩
    have hmem : (Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) F9)) ∈
        Uid σ9 3 := Subgroup.mul_mem _ (scalar_mem_uid_three u hu) A.2
    have hEq : (⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) F9), hmem⟩ :
        Uid σ9 3) = scU u * A := by
      rw [scU_of_norm u hu]
      apply Subtype.ext
      rfl
    show uidToOrth 3 (⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * (A : GL (Fin 3) F9),
        hmem⟩ : Uid σ9 3) = scG u * uidToOrth 3 A
    rw [hEq, map_mul]
    rfl
  have hsq : scG omegaUnit * scG omegaUnit = piOrth (hermForm 3) := by
    rw [scG_mul omegaUnit omegaUnit hωnorm hωnorm hsquare_norm, hωω]
    exact scG_neg_one hneg
  have hpi : piOrth (hermForm 3) ∈ omegaGroup (hermForm_nondegenerate 3) :=
    ff6m_piOrth_mem_omega (hermForm_nondegenerate 3) hdim3 quadSign_hermForm_three
  have hnmem : scG omegaUnit ∉ omegaGroup (hermForm_nondegenerate 3) :=
    ff6m_not_mem_omega_of_mul_self_eq_pi (hermForm_nondegenerate 3) hdim3
      quadSign_hermForm_three hsq
  rcases fourth_root_cases h4 with h1 | h1 | h1 | h1
  · left
    have hSU : (A : GL (Fin 3) F9) ∈ SUid σ9 3 :=
      (mem_SUid (σ := σ9)).mpr ⟨hdA.trans h1, hU⟩
    exact ⟨⟨(A : GL (Fin 3) F9), hSU⟩, suToOrth3_mk A hSU⟩
  · right
    have hdet : ((-1 : F9ˣ) : F9) ^ 3 * d = 1 := by
      rw [h1]
      norm_num
    have h := step (-1 : F9ˣ) hneg hdet
    rwa [scG_neg_one hneg] at h
  · exfalso
    have hdet : (omegaUnit : F9) ^ 3 * d = 1 := by
      rw [h1, show (omegaUnit : F9) = omega9 from rfl,
        show omega9 ^ 3 * omega9 = omega9 ^ 4 by rw [← pow_succ]]
      exact omega9_pow_four
    have h := step omegaUnit hωnorm hdet
    have hScΩ : scG omegaUnit ∈ omegaGroup (hermForm_nondegenerate 3) := by
      obtain ⟨s, hs⟩ := h
      have hsΩ : suToOrth3 s ∈ omegaGroup (hermForm_nondegenerate 3) := suToOrth3_mem_omega s
      rw [hs] at hsΩ
      have h2 : scG omegaUnit = (scG omegaUnit * uidToOrth 3 A) * (uidToOrth 3 A)⁻¹ := by group
      rw [h2]
      exact Subgroup.mul_mem _ hsΩ (Subgroup.inv_mem _ hg)
    exact hnmem hScΩ
  · exfalso
    have hdet : ((-omegaUnit : F9ˣ) : F9) ^ 3 * d = 1 := by
      rw [h1, show ((-omegaUnit : F9ˣ) : F9) = -omega9 from rfl,
        show (-omega9 : F9) ^ 3 * (-omega9) = omega9 ^ 4 by ring]
      exact omega9_pow_four
    have h := step (-omegaUnit) hnnorm hdet
    have hScΩ : scG (-omegaUnit) ∈ omegaGroup (hermForm_nondegenerate 3) := by
      obtain ⟨s, hs⟩ := h
      have hsΩ : suToOrth3 s ∈ omegaGroup (hermForm_nondegenerate 3) := suToOrth3_mem_omega s
      rw [hs] at hsΩ
      have h2 : scG (-omegaUnit) = (scG (-omegaUnit) * uidToOrth 3 A) * (uidToOrth 3 A)⁻¹ := by
        group
      rw [h2]
      exact Subgroup.mul_mem _ hsΩ (Subgroup.inv_mem _ hg)
    have hnew : σ9 (((-1 : F9ˣ) * omegaUnit : F9ˣ) : F9) *
        (((-1 : F9ˣ) * omegaUnit : F9ˣ) : F9) = 1 := by
      have hval : (((-1 : F9ˣ) * omegaUnit : F9ˣ) : F9) = -(omegaUnit : F9) := by
        rw [Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul]
      rw [hval]
      exact hnnorm
    have hU : (-omegaUnit : F9ˣ) = (-1 : F9ˣ) * omegaUnit := by
      apply Units.ext
      show -((omegaUnit : F9)) = (-1 : F9) * (omegaUnit : F9)
      rw [neg_mul, one_mul]
    have hfac : scG (-omegaUnit) = piOrth (hermForm 3) * scG omegaUnit := by
      rw [hU, ← scG_mul (-1 : F9ˣ) omegaUnit hneg hωnorm hnew, scG_neg_one hneg]
    have hScωΩ : scG omegaUnit ∈ omegaGroup (hermForm_nondegenerate 3) := by
      have h3 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hpi) hScΩ
      rwa [hfac, ← mul_assoc, inv_mul_cancel, one_mul] at h3
    exact hnmem hScωΩ

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameSylowOvergroups
public import CFSG.ClassicalGroups.Orthogonal.FiveSquareSignOrbit

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameWeakClosure

open CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration
open CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameSylowOvergroups
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow
open CFSG.GH74.GLS.IVK.Proofs2.Sp48
open CFSG.ClassicalGroups.Orthogonal.FiveSquareSignOrbit
open QuadraticMap
open scoped commutatorElement

abbrev G : Type := ↥derived

@[expose] noncomputable def rD : G :=
  ⟨(stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V),
    stdFrame.betaO_diag_mem_commutator (FrameData.sigmaO2 (K := F))⟩

@[expose] noncomputable def sD : G :=
  ⟨(stdFrame.s : V ≃ₗ[F] V), by
    have h : stdFrame.sO ∈ commutator O := sO_mem_derived stdFrame
    have hmap : (commutator O).map O.subtype = derived :=
      Subgroup.map_subtype_commutator O
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨stdFrame.sO, h, rfl⟩⟩

theorem coe_rD :
    ((rD : G) : V ≃ₗ[F] V) =
      (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) := rfl

theorem coe_sD : ((sD : G) : V ≃ₗ[F] V) = stdFrame.s := rfl

@[simp] theorem rD_e0 : ((rD : G) : V ≃ₗ[F] V) (e 0) = e 1 := by
  rw [coe_rD]
  rw [show (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) (e 0) =
      (stdFrame.beta (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) (stdFrame.e 0)) from rfl]
  rw [stdFrame.beta_e_zero]
  simp [FrameData.sigmaO2_coe, O2Plane.coe_sig, stdFrame_e, Generic.e_apply,
    Pi.single_apply, Fin.sum_univ_two]

@[simp] theorem rD_e1 : ((rD : G) : V ≃ₗ[F] V) (e 1) = e 0 := by
  rw [coe_rD]
  rw [show (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) (e 1) =
      (stdFrame.beta (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) (stdFrame.e 1)) from rfl]
  rw [stdFrame.beta_e_one]
  simp [FrameData.sigmaO2_coe, O2Plane.coe_sig, stdFrame_e, Generic.e_apply,
    Pi.single_apply]

@[simp] theorem rD_e2 : ((rD : G) : V ≃ₗ[F] V) (e 2) = e 3 := by
  rw [coe_rD]
  rw [show (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) (e 2) =
      (stdFrame.beta (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) (stdFrame.e 2)) from rfl]
  rw [stdFrame.beta_e_two]
  simp [FrameData.sigmaO2_coe, O2Plane.coe_sig, stdFrame_e, Generic.e_apply,
    Pi.single_apply]

@[simp] theorem rD_e3 : ((rD : G) : V ≃ₗ[F] V) (e 3) = e 2 := by
  rw [coe_rD]
  rw [show (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) (e 3) =
      (stdFrame.beta (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) (stdFrame.e 3)) from rfl]
  rw [stdFrame.beta_e_three]
  simp [FrameData.sigmaO2_coe, O2Plane.coe_sig, stdFrame_e, Generic.e_apply,
    Pi.single_apply]

@[simp] theorem rD_e4 : ((rD : G) : V ≃ₗ[F] V) (e 4) = e 4 := by
  rw [coe_rD]
  rw [show (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) (e 4) =
      (stdFrame.beta (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) (stdFrame.e 4)) from rfl]
  rw [stdFrame.beta_e_four]
  simp [FrameData.sigmaO2_coe, O2Plane.coe_sig, O2Plane.det_sig, stdFrame_e,
    Generic.e_apply, Pi.single_apply]

@[simp] theorem sD_e0 : ((sD : G) : V ≃ₗ[F] V) (e 0) = e 2 := by
  rw [coe_sD]
  simpa [stdFrame_e] using stdFrame.s_e 0

@[simp] theorem sD_e1 : ((sD : G) : V ≃ₗ[F] V) (e 1) = e 3 := by
  rw [coe_sD]
  simpa [stdFrame_e] using stdFrame.s_e 1

@[simp] theorem sD_e2 : ((sD : G) : V ≃ₗ[F] V) (e 2) = e 0 := by
  rw [coe_sD]
  simpa [stdFrame_e] using stdFrame.s_e 2

@[simp] theorem sD_e3 : ((sD : G) : V ≃ₗ[F] V) (e 3) = e 1 := by
  rw [coe_sD]
  simpa [stdFrame_e] using stdFrame.s_e 3

@[simp] theorem sD_e4 : ((sD : G) : V ≃ₗ[F] V) (e 4) = e 4 := by
  rw [coe_sD]
  simpa [stdFrame_e] using stdFrame.s_e 4

theorem e_ne {i j : Fin 5} (hij : i ≠ j) : e i ≠ e j := by
  intro h
  have h' := congrFun h i
  simp [Generic.e_apply, Pi.single_apply, hij] at h'

theorem rD_mul_self : rD * rD = 1 := by
  apply Subtype.ext
  change ((rD : G) : V ≃ₗ[F] V) * ((rD : G) : V ≃ₗ[F] V) = 1
  rw [coe_rD]
  change (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) *
      (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) = 1
  rw [show (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) *
      (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) =
      ((stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) *
        stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : TauCeti.QuadraticMap.orthogonalGroup Q) :
        V ≃ₗ[F] V) from rfl]
  rw [stdFrame.betaO_mul, FrameData.sigmaO2_mul_self, stdFrame.betaO_one]
  rfl

theorem sD_mul_self : sD * sD = 1 := by
  apply Subtype.ext
  change ((sD : G) : V ≃ₗ[F] V) * ((sD : G) : V ≃ₗ[F] V) = 1
  rw [coe_sD]
  change stdFrame.s * stdFrame.s = 1
  exact stdFrame.s_mul_self

theorem sD_conj_rD : sD * rD * sD = rD := by
  apply Subtype.ext
  change (stdFrame.s : V ≃ₗ[F] V) *
      (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) * stdFrame.s =
    (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V)
  rw [show (stdFrame.s : V ≃ₗ[F] V) *
      (stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) : V ≃ₗ[F] V) * stdFrame.s =
      ((stdFrame.sO * stdFrame.betaO (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)) * stdFrame.sO :
        TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[F] V) from rfl]
  rw [stdFrame.sO_betaO_conj']

theorem rD_commute_sD : rD * sD = sD * rD := by
  calc rD * sD = (sD * rD * sD) * sD := by rw [sD_conj_rD]
    _ = sD * rD * (sD * sD) := by group
    _ = sD * rD := by rw [sD_mul_self, mul_one]

theorem rD_ne_one : rD ≠ 1 := by
  intro h
  have h' : ((rD : G) : V ≃ₗ[F] V) (e 0) = ((1 : G) : V ≃ₗ[F] V) (e 0) := by rw [h]
  rw [rD_e0] at h'
  simp only [Subgroup.coe_one, LinearEquiv.coe_one, id_eq] at h'
  exact e_ne (by decide : (0 : Fin 5) ≠ 1) h'.symm

theorem sD_ne_one : sD ≠ 1 := by
  intro h
  have h' : ((sD : G) : V ≃ₗ[F] V) (e 0) = ((1 : G) : V ≃ₗ[F] V) (e 0) := by rw [h]
  rw [sD_e0] at h'
  simp only [Subgroup.coe_one, LinearEquiv.coe_one, id_eq] at h'
  exact e_ne (by decide : (2 : Fin 5) ≠ 0) h'

theorem rD_ne_sD : rD ≠ sD := by
  intro h
  have h' : ((rD : G) : V ≃ₗ[F] V) (e 0) = ((sD : G) : V ≃ₗ[F] V) (e 0) := by rw [h]
  rw [rD_e0, sD_e0] at h'
  exact e_ne (by decide : (1 : Fin 5) ≠ 2) h'

theorem orderOf_rD : orderOf rD = 2 :=
  orderOf_eq_prime (p := 2) (by rw [pow_two]; exact rD_mul_self) rD_ne_one

theorem orderOf_sD : orderOf sD = 2 :=
  orderOf_eq_prime (p := 2) (by rw [pow_two]; exact sD_mul_self) sD_ne_one

@[expose] noncomputable def permutationFour : Subgroup G :=
  Subgroup.zpowers rD ⊔ Subgroup.zpowers sD

theorem permutationFour_def :
    permutationFour = Subgroup.zpowers rD ⊔ Subgroup.zpowers sD := rfl

theorem disjoint_zpowers_rD_zpowers_sD : Disjoint (Subgroup.zpowers rD) (Subgroup.zpowers sD) := by
  rw [Subgroup.disjoint_def]
  intro x hx hs
  have hx' := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two orderOf_rD).mp hx
  have hs' := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two orderOf_sD).mp hs
  rcases hx' with hx1 | hxr
  · rwa [hx1]
  · rcases hs' with hs1 | hss
    · exact absurd (hxr.symm.trans hs1) rD_ne_one
    · exact absurd (hxr.symm.trans hss) rD_ne_sD

theorem zpowers_sD_le_normalizer_zpowers_rD :
    Subgroup.zpowers sD ≤ Subgroup.normalizer (Subgroup.zpowers rD : Set G) := by
  refine (Subgroup.zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y = 1 ∨ y = rD := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two orderOf_rD).mp hy
  rcases hy' with rfl | rfl
  · simp
  · exact rD_commute_sD

theorem card_permutationFour : Nat.card permutationFour = 4 := by
  rw [permutationFour,
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers rD) (Subgroup.zpowers sD)
      zpowers_sD_le_normalizer_zpowers_rD disjoint_zpowers_rD_zpowers_sD]
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_rD, orderOf_sD]

noncomputable def hadamardP : V := (2 : F) • e 0 + 3 • e 1 + 3 • e 2 + 3 • e 3

noncomputable def hadamardQ : V := e 4

theorem Q_hadamardP : Q hadamardP = 1 := by
  simp [hadamardP, QuadraticMap.map_add, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, Generic.polar_single,
    Generic.Q_single, Generic.e_apply, Pi.single_apply]
  decide

theorem Q_hadamardQ : Q hadamardQ = 1 := by
  rw [hadamardQ]
  exact Generic.Q_single F 4

theorem polar_hadamardP (x : V) :
    polar Q hadamardP x = 4 * x 0 + x 1 + x 2 + x 3 := by
  calc polar Q hadamardP x = 2 * ∑ i, hadamardP i * x i :=
        Generic.polar_apply F hadamardP x
    _ = 4 * x 0 + x 1 + x 2 + x 3 := by
      simp [hadamardP, Generic.e_apply, Pi.single_apply, Fin.sum_univ_five]
      ring_nf
      have h5 : (5 : F) = 0 := by decide
      linear_combination (x 1 + x 2 + x 3) * h5

theorem polar_hadamardQ (x : V) : polar Q hadamardQ x = 2 * x 4 := by
  calc polar Q hadamardQ x = 2 * ∑ i, hadamardQ i * x i :=
        Generic.polar_apply F hadamardQ x
    _ = 2 * x 4 := by
      simp [hadamardQ, Generic.e_apply, Pi.single_apply, Fin.sum_univ_five]

@[instance_reducible] private def hadamardAddCommGroup : AddCommGroup V :=
  { Pi.addCommGroup with toAddCommMonoid := Pi.addCommMonoid }

private noncomputable def hadamardReflectP : V ≃ₗ[F] V :=
  @reflect F V (inferInstance : Field F) hadamardAddCommGroup
    (Pi.Function.module (Fin 5) F F) Q hadamardP

private noncomputable def hadamardReflectQ : V ≃ₗ[F] V :=
  @reflect F V (inferInstance : Field F) hadamardAddCommGroup
    (Pi.Function.module (Fin 5) F F) Q hadamardQ

noncomputable def hadamardLinear : V ≃ₗ[F] V :=
  hadamardReflectP * hadamardReflectQ

theorem hadamardLinear_apply (x : V) :
    hadamardLinear x =
      x - (2 * x 4) • e 4 - (4 * x 0 + x 1 + x 2 + x 3) • hadamardP := by
  rw [hadamardLinear, LinearEquiv.mul_apply]
  have hp : Q hadamardP ≠ 0 :=
    Q_hadamardP ▸ (by decide : (1 : F) ≠ 0)
  have hq : Q hadamardQ ≠ 0 :=
    Q_hadamardQ ▸ (by decide : (1 : F) ≠ 0)
  rw [show hadamardReflectQ x =
      x - (polar Q hadamardQ x / Q hadamardQ) • hadamardQ from
    @reflect_apply F V (inferInstance : Field F) hadamardAddCommGroup
      (Pi.Function.module (Fin 5) F F) (Q := Q) (v := hadamardQ) hq x]
  rw [show hadamardReflectP (x - (polar Q hadamardQ x / Q hadamardQ) • hadamardQ) =
      (x - (polar Q hadamardQ x / Q hadamardQ) • hadamardQ) -
        (polar Q hadamardP
          (x - (polar Q hadamardQ x / Q hadamardQ) • hadamardQ) / Q hadamardP) •
          hadamardP from
    @reflect_apply F V (inferInstance : Field F) hadamardAddCommGroup
      (Pi.Function.module (Fin 5) F F) (Q := Q) (v := hadamardP) hp
      (x - (polar Q hadamardQ x / Q hadamardQ) • hadamardQ)]
  have hq1 : Q hadamardQ = 1 := Q_hadamardQ
  have hp1 : Q hadamardP = 1 := Q_hadamardP
  rw [hq1, hp1, div_one]
  rw [polar_hadamardQ, hadamardQ]
  have hpol : polar Q hadamardP (x - (2 * x 4) • e 4) = polar Q hadamardP x := by
    simp only [polar_hadamardP]
    simp [Generic.e_apply, Pi.single_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  rw [hpol, polar_hadamardP, div_one]

@[simp] theorem hadamardLinear_e0 :
    hadamardLinear (e 0) = 3 • e 0 + 3 • e 1 + 3 • e 2 + 3 • e 3 := by
  rw [hadamardLinear_apply]
  funext i
  fin_cases i <;> simp [Generic.e_apply, Pi.single_apply, hadamardP, Fin.sum_univ_five] <;>
    decide

@[simp] theorem hadamardLinear_e1 :
    hadamardLinear (e 1) = 3 • e 0 + 3 • e 1 + 2 • e 2 + 2 • e 3 := by
  rw [hadamardLinear_apply]
  funext i
  fin_cases i <;> simp [Generic.e_apply, Pi.single_apply, hadamardP, Fin.sum_univ_five] <;>
    decide

@[simp] theorem hadamardLinear_e2 :
    hadamardLinear (e 2) = 3 • e 0 + 2 • e 1 + 3 • e 2 + 2 • e 3 := by
  rw [hadamardLinear_apply]
  funext i
  fin_cases i <;> simp [Generic.e_apply, Pi.single_apply, hadamardP, Fin.sum_univ_five] <;>
    decide

@[simp] theorem hadamardLinear_e3 :
    hadamardLinear (e 3) = 3 • e 0 + 2 • e 1 + 2 • e 2 + 3 • e 3 := by
  rw [hadamardLinear_apply]
  funext i
  fin_cases i <;> simp [Generic.e_apply, Pi.single_apply, hadamardP, Fin.sum_univ_five] <;>
    decide

@[simp] theorem hadamardLinear_e4 : hadamardLinear (e 4) = 4 • e 4 := by
  rw [hadamardLinear_apply]
  funext i
  fin_cases i <;> simp [Generic.e_apply, Pi.single_apply, hadamardP, Fin.sum_univ_five] <;>
    decide

end CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameWeakClosure

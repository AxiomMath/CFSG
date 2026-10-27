module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryAut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryKernel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

variable {K : Type} [Field K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

abbrev unitaryRootCenter : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ)

section Coordinates

theorem conj_hermitianUnipotentPSU (y z : hermitianUnipotentCoord J) :
    MulAut.conj (hermitianUnipotentPSU J hJ y) (hermitianUnipotentPSU J hJ z) =
      hermitianUnipotentPSU J hJ (y * z * y⁻¹) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

omit hJ in
theorem fst_mul_mul_inv (y z : hermitianUnipotentCoord J) : (y * z * y⁻¹).1.1 = z.1.1 := by
  rw [fst_mul, fst_mul, fst_inv]
  ring

omit hJ in
theorem diagCoord_diagCoord_inv (c : normOne J) (z : hermitianUnipotentCoord J) :
    diagCoord J c (diagCoord J c⁻¹ z) = z := by
  have hc : J.conj ((c : Kˣ) : K) = ((c : Kˣ) : K)⁻¹ := conj_eq_inv_of_mem_normOne J c.2
  have hc' : J.conj (((c⁻¹ : normOne J) : Kˣ) : K) = ((c : Kˣ) : K) := by
    rw [InvMemClass.coe_inv, Units.val_inv_eq_inv_val, map_inv₀, hc, inv_inv]
  refine coord_ext ?_ rfl
  rw [fst_diagCoord, fst_diagCoord, hc', hc, mul_assoc, mul_inv_cancel₀ (Units.ne_zero _),
    mul_one]

omit hJ in
theorem rootTau_rootTau (z : hermitianUnipotentCoord J) : rootTau J (rootTau J z) = z :=
  DFunLike.congr_fun (rootTau_mul_self J) z

theorem exists_diag_bar_apply (c : normOne J) (ε : Fin 2) (z : hermitianUnipotentCoord J) :
    ∃ w : hermitianUnipotentCoord J,
      (diagAut J hJ c * barAut J hJ ^ (ε : ℕ)) (hermitianUnipotentPSU J hJ z) =
          hermitianUnipotentPSU J hJ w ∧
        w.1.1 = (J.conj ^ (ε : ℕ)) z.1.1 * J.conj ((c : Kˣ) : K) := by
  fin_cases ε
  · exact ⟨diagCoord J c z, by simp [diagAut_hermitianUnipotentPSU], by simp⟩
  · exact ⟨diagCoord J c (rootTau J z), by
      simp [MulAut.mul_apply, barAut_hermitianUnipotentPSU, diagAut_hermitianUnipotentPSU],
      by simp⟩

theorem exists_conj_diag_bar_apply (y : hermitianUnipotentCoord J) (c : normOne J) (ε : Fin 2)
    (z : hermitianUnipotentCoord J) :
    ∃ w : hermitianUnipotentCoord J,
      (MulAut.conj (hermitianUnipotentPSU J hJ y) * diagAut J hJ c * barAut J hJ ^ (ε : ℕ))
          (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ w ∧
        w.1.1 = (J.conj ^ (ε : ℕ)) z.1.1 * J.conj ((c : Kˣ) : K) := by
  obtain ⟨w, hw, hw1⟩ := exists_diag_bar_apply J hJ c ε z
  refine ⟨y * w * y⁻¹, ?_, by rw [fst_mul_mul_inv, hw1]⟩
  rw [mul_assoc, MulAut.mul_apply, hw, conj_hermitianUnipotentPSU]

end Coordinates

section Membership

variable [CharP K 2]

omit [CharP K 2] in
theorem conj_mem_rootCenterAut {r : ProjectiveSpecialUnitaryMatrixGroup J}
    (hr : r ∈ unitaryCoverRoot J hJ) :
    MulAut.conj r ∈ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) := by
  refine ⟨map_conj_of_mem hr, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨y, rfl⟩ := hr
  rw [conj_hermitianUnipotentPSU, ← mul_comm_of_fst_eq_zero J hz y, mul_inv_cancel_right]

omit [CharP K 2] in
theorem diagAut_mem_rootCenterAut (c : normOne J) :
    diagAut J hJ c ∈ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) := by
  refine ⟨Subgroup.ext fun x => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨diagCoord J c z, (diagAut_hermitianUnipotentPSU J hJ c z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨hermitianUnipotentPSU J hJ (diagCoord J c⁻¹ z), ⟨_, rfl⟩, ?_⟩
    change diagAut J hJ c (hermitianUnipotentPSU J hJ (diagCoord J c⁻¹ z)) = _
    rw [diagAut_hermitianUnipotentPSU, diagCoord_diagCoord_inv]
  · rintro _ ⟨z, hz, rfl⟩
    rw [diagAut_hermitianUnipotentPSU]
    congr 1
    exact coord_ext (by rw [fst_diagCoord, show z.1.1 = 0 from hz, zero_mul]) rfl

theorem barAut_mem_rootCenterAut :
    barAut J hJ ∈ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) := by
  refine ⟨Subgroup.ext fun x => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨rootTau J z, (barAut_hermitianUnipotentPSU J hJ z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨hermitianUnipotentPSU J hJ (rootTau J z), ⟨_, rfl⟩, ?_⟩
    change barAut J hJ (hermitianUnipotentPSU J hJ (rootTau J z)) = _
    rw [barAut_hermitianUnipotentPSU, rootTau_rootTau]
  · rintro _ ⟨z, hz, rfl⟩
    rw [barAut_hermitianUnipotentPSU]
    congr 1
    exact coord_ext (by rw [fst_rootTau, show z.1.1 = 0 from hz, map_zero])
      (conj_snd_of_fst_eq_zero J hz)

theorem conj_diag_bar_mem_rootCenterAut {r : ProjectiveSpecialUnitaryMatrixGroup J}
    (hr : r ∈ unitaryCoverRoot J hJ) (c : normOne J) (ε : ℕ) :
    MulAut.conj r * diagAut J hJ c * barAut J hJ ^ ε ∈
      rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (conj_mem_rootCenterAut J hJ hr)
    (diagAut_mem_rootCenterAut J hJ c)) (Subgroup.pow_mem _ (barAut_mem_rootCenterAut J hJ) ε)

end Membership

section Structure

variable [Finite K] (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
  (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)

include hcard in
theorem charP_two_of_card : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)

include hf hcard hfixed

theorem unitaryRoot_injOn_conj :
    Set.InjOn MulAut.conj
      (unitaryCoverRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  obtain ⟨-, -, -, -, -, rho, hrho, -, -, h2tr, hstabα, -⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryIsotropicPoints J) :=
    MulAction.compHom _ rho
  have : FaithfulSMul (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryIsotropicPoints J) :=
    ⟨fun h => hrho (Equiv.ext h)⟩
  have : MulAction.IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J)
      (unitaryIsotropicPoints J) := ⟨fun b d => by
    by_cases hbd : b = d
    · exact ⟨1, by rw [hbd, one_smul]⟩
    · obtain ⟨g, hg, -⟩ := h2tr b d d b hbd (Ne.symm hbd)
      exact ⟨g, hg⟩⟩
  have hstab : MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J)
      (unitaryOuterIsotropicPoint J hJ 0 (by decide)) =
      (MulAction.stabilizer (Equiv.Perm (unitaryIsotropicPoints J))
        (unitaryOuterIsotropicPoint J hJ 0 (by decide))).comap rho :=
    Subgroup.ext fun _ => Iff.rfl
  refine injOn_conj_of_le_stabilizer (ξ := unitaryOuterIsotropicPoint J hJ 0 (by decide)) ?_
  rw [hstab, hstabα]
  exact unitary_entire_root_fixes_first_coordinate J hJ

omit hf in
theorem mem_unitaryRootCenter_iff {x : ProjectiveSpecialUnitaryMatrixGroup J} :
    x ∈ unitaryRootCenter J hJ ↔ x ∈ unitaryCoverRoot J hJ ∧ ∀ y ∈ unitaryCoverRoot J hJ,
      x * y = y * x := by
  have : CharP K 2 := charP_two_of_card f hcard
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, rfl⟩, ?_⟩
    rintro _ ⟨w, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm_of_fst_eq_zero J hz w]
  · rintro ⟨⟨z, rfl⟩, hc⟩
    refine ⟨z, ?_, rfl⟩
    have hz : z ∈ Subgroup.center (hermitianUnipotentCoord J) := Subgroup.mem_center_iff.2
      fun w => CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ (by
        rw [map_mul, map_mul]
        exact (hc _ ⟨w, rfl⟩).symm)
    rwa [center_eq_ker_firstCoord J (2 ^ f) hcard hfixed] at hz

theorem exists_eq_conj_diag_bar {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : γ ∈ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ)) :
    ∃ r ∈ unitaryCoverRoot J hJ, ∃ c : normOne J, ∃ ε : Fin 2,
      γ = MulAut.conj r * diagAut J hJ c * barAut J hJ ^ (ε : ℕ) := by
  have : CharP K 2 := charP_two_of_card f hcard
  obtain ⟨hγR, hγU⟩ := hγ
  set φ := unitaryCoverRootEquiv J hJ
  let γR : MulAut (unitaryCoverRoot J hJ) := restrictMulAut γ _ hγR
  have hfix : ∀ v ∈ rootCenter J φ, γR v = v := by
    intro v hv
    apply Subtype.ext
    refine hγU _ ⟨φ.symm v, hv, ?_⟩
    rw [← unitaryCoverRootEquiv_val, MulEquiv.apply_symm_apply]
  obtain ⟨c, hc, hσ⟩ := root_aut_fst_eq J φ (2 ^ f) hcard hfixed γR hfix
  obtain ⟨ε, hε⟩ : ∃ ε : Fin 2, ∀ v,
      (φ.symm (γR v)).1.1 = c * (J.conj ^ (ε : ℕ)) (φ.symm v).1.1 := by
    rcases hσ with h | h
    · exact ⟨0, fun v => by simpa using h v⟩
    · exact ⟨1, fun v => by simpa using h v⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hc
    exact zero_ne_one hc
  let d : normOne J := ⟨Units.mk0 (J.conj c) ((map_ne_zero _).2 hc0), by
    change J.conj c * J.conj (J.conj c) = 1
    rw [J.conj_involutive, mul_comm]
    exact hc⟩
  have hd : J.conj ((d : Kˣ) : K) = c := J.conj_involutive c
  set β := diagAut J hJ d * barAut J hJ ^ (ε : ℕ) with hβ
  have hβA : β ∈ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) :=
    Subgroup.mul_mem _ (diagAut_mem_rootCenterAut J hJ d)
      (Subgroup.pow_mem _ (barAut_mem_rootCenterAut J hJ) _)
  have hγA : γ ∈ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) := ⟨hγR, hγU⟩
  have hγ'A := Subgroup.mul_mem _ hγA (Subgroup.inv_mem _ hβA)
  have hγ'RV : ∀ x ∈ unitaryCoverRoot J hJ, x⁻¹ * (γ * β⁻¹) x ∈ unitaryRootCenter J hJ := by
    intro x hx
    have hy : β⁻¹ x ∈ unitaryCoverRoot J hJ := by
      rw [← (Subgroup.inv_mem _ hβA).1]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨z, hz⟩ := hy
    have hx' : x = β (hermitianUnipotentPSU J hJ z) := by
      rw [hz, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    obtain ⟨w₁, hw₁, hw₁1⟩ := exists_diag_bar_apply J hJ d ε z
    have hγz : γ (hermitianUnipotentPSU J hJ z) =
        hermitianUnipotentPSU J hJ (φ.symm (γR (φ z))) := by
      have h1 : (φ (φ.symm (γR (φ z))) : ProjectiveSpecialUnitaryMatrixGroup J) =
          hermitianUnipotentPSU J hJ (φ.symm (γR (φ z))) := unitaryCoverRootEquiv_val J hJ _
      have h2 : (φ z : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianUnipotentPSU J hJ z :=
        unitaryCoverRootEquiv_val J hJ z
      rw [← h1, MulEquiv.apply_symm_apply, ← h2]
      rfl
    have hw₂1 := hε (φ z)
    rw [MulEquiv.symm_apply_apply] at hw₂1
    rw [MulAut.mul_apply, ← hz, hγz, hx', hw₁, ← map_inv, ← map_mul]
    refine ⟨_, ?_, rfl⟩
    change (w₁⁻¹ * φ.symm (γR (φ z))).1.1 = 0
    rw [fst_mul, fst_inv, hw₁1, hw₂1, hd]
    ring
  obtain ⟨b, hb, hγb⟩ := unitaryRoot_layer_kernel J f hf hcard hfixed hJ (γ * β⁻¹) hγ'A.1
    hγ'A.2 hγ'RV
  refine ⟨b, hb, d, ε, ?_⟩
  rw [mul_assoc, ← hβ, ← hγb, inv_mul_cancel_right]

theorem eq_of_conj_diag_bar_eq {r r' : ProjectiveSpecialUnitaryMatrixGroup J}
    (hr : r ∈ unitaryCoverRoot J hJ) (hr' : r' ∈ unitaryCoverRoot J hJ) {c c' : normOne J}
    {ε ε' : Fin 2}
    (h : MulAut.conj r * diagAut J hJ c * barAut J hJ ^ (ε : ℕ) =
      MulAut.conj r' * diagAut J hJ c' * barAut J hJ ^ (ε' : ℕ)) :
    r = r' ∧ c = c' ∧ ε = ε' := by
  have : CharP K 2 := charP_two_of_card f hcard
  obtain ⟨y, rfl⟩ := hr
  obtain ⟨y', rfl⟩ := hr'
  have hfst : ∀ z : hermitianUnipotentCoord J,
      (J.conj ^ (ε : ℕ)) z.1.1 * J.conj ((c : Kˣ) : K) =
        (J.conj ^ (ε' : ℕ)) z.1.1 * J.conj ((c' : Kˣ) : K) := fun z => by
    obtain ⟨w, hw, hw1⟩ := exists_conj_diag_bar_apply J hJ y c ε z
    obtain ⟨w', hw', hw'1⟩ := exists_conj_diag_bar_apply J hJ y' c' ε' z
    rw [h, hw'] at hw
    rw [← hw1, ← hw'1, CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ hw]
  obtain ⟨o, ho⟩ := exists_fst_eq J (2 ^ f) hcard hfixed 1
  have hcc : c = c' := by
    have h1 := hfst o
    simp only [ho, map_one, one_mul] at h1
    exact Subtype.ext (Units.ext (J.conj.injective h1))
  subst hcc
  have hc0 : J.conj ((c : Kˣ) : K) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
  have hεε : ε = ε' := by
    obtain ⟨ξ, hξ⟩ := exists_conj_ne J (2 ^ f) hcard hfixed
    obtain ⟨x, hx⟩ := exists_fst_eq J (2 ^ f) hcard hfixed ξ
    have h1 := mul_right_cancel₀ hc0 (hfst x)
    rw [hx] at h1
    fin_cases ε <;> fin_cases ε'
    · rfl
    · exact absurd (by simpa using h1.symm) hξ
    · exact absurd (by simpa using h1) hξ
    · rfl
  subst hεε
  refine ⟨unitaryRoot_injOn_conj J hJ f hf hcard hfixed ⟨y, rfl⟩ ⟨y', rfl⟩
    (mul_right_cancel (mul_right_cancel h)), rfl, rfl⟩

end Structure

end CFSG.ProperTwoGeneratedCore.RootCenter

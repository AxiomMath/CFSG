module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.Par
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxDefs
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL3Heis
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL3Pairs
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofD4
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusLayerAux

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open CFSG.RankThree.PartTwo.Sec19
open CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.RankThree.PartTwo.Sec11 (d4ThreeASL3Model_holds)
open CFSG.RankThree.PartTwo.Sec11.Item1118Res2Proof (IsSL3Model isSL3Model_comap)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.Classical2 (unitarySet)
open scoped commutatorElement MatrixGroups

variable {ℓ f : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

section Leaves

theorem layer_rep_odd (P : D4ParOdd ℓ f X σ) {x : C0 σ} (hx : IsClassX σ x) :
    ∃ (L : Type) (_ : Field L) (ρ : cenX σ x →* Matrix.SpecialLinearGroup (Fin 3) L),
      IsSL3Model ρ := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hv3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hv1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  obtain ⟨L, _, ρ₀, hρ₀⟩ :=
    d4ThreeASL3Model_holds X (ℓ ^ f) σ P.card P.frob P.not_three_dvd (g * x * g⁻¹) hg hv3 hv1
  obtain ⟨ρ, hρ⟩ := isSL3Model_comap (MulAut.conj g) (v := x) (ρ₀ := ρ₀) hρ₀
  exact ⟨L, _, ρ, hρ⟩

theorem centralizer_layer_le_cenX_odd {x : C0 σ} (hxD : x ∈ layerSub σ x) :
    Subgroup.centralizer (layerSub σ x : Set (C0 σ)) ≤ cenX σ x := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff] at hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hz x hxD).symm

theorem layer_centralizer_scalar_odd (P : D4ParOdd ℓ f X σ) {x : C0 σ} (hx : IsClassX σ x)
    (hZD : ∀ w ∈ layerSub σ x, (∀ d ∈ layerSub σ x, w * d = d * w) → w ∈ Subgroup.zpowers x)
    (hH : ∃ y ∈ layerSub σ x, ∃ p ∈ layerSub σ x,
      p * y * p⁻¹ * y⁻¹ ≠ 1 ∧ (p * y * p⁻¹ * y⁻¹) ^ 3 = 1 ∧
        ∀ d ∈ layerSub σ x, (p * y * p⁻¹ * y⁻¹) * d = d * (p * y * p⁻¹ * y⁻¹)) :
    ∃ (L : Type) (_ : Field L) (ρ : cenX σ x →* Matrix.SpecialLinearGroup (Fin 3) L),
      IsSL3Model ρ ∧ ∀ z : cenX σ x, (z : C0 σ) ∈ Subgroup.centralizer (layerSub σ x : Set (C0 σ)) →
        ρ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L) := by
  obtain ⟨L, _, ρ, hρ⟩ := layer_rep_odd P hx
  refine ⟨L, _, ρ, hρ, ?_⟩
  obtain ⟨y, hy, p, hp, hu1, hu3, huc⟩ := hH
  have hyC : y ∈ cenX σ x := layerSub_le_self (cenX σ x) hy
  have hu : p * y * p⁻¹ * y⁻¹ ∈ layerSub σ x := by
    have := Subgroup.commutator_mono (layerSub_le_self (cenX σ x)) (le_refl (cenX σ x))
      (Subgroup.commutator_mem_commutator hp hyC)
    rwa [commutatorElement_def] at this
  obtain ⟨u, hup⟩ : ∃ u, p * y * p⁻¹ * y⁻¹ = u := ⟨_, rfl⟩
  rw [hup] at hu hu1 hu3 huc
  have hux : u ∈ Subgroup.zpowers x := hZD u hu huc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hux
  have hDC : layerSub σ x ≤ cenX σ x := layerSub_le_self _
  have hx3 : x ^ 3 = 1 := hx.1
  set y' : cenX σ x := ⟨y, hDC hy⟩ with hy'
  set p' : cenX σ x := ⟨p, hDC hp⟩ with hp'
  set u' : cenX σ x := ⟨u, hDC hu⟩ with hu'
  set x' : cenX σ x := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hx'
  have hux' : u' = x' ^ k := Subtype.ext (by simp [hu', hx', hk])
  have hcomm : p' * y' * p'⁻¹ * y'⁻¹ = u' := Subtype.ext (by simpa [hy', hp', hu'] using hup)
  have hρu : ρ u' ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L) := by
    rw [hux', map_zpow]
    exact Subgroup.zpow_mem _ hρ.1 k
  have hu3' : ∃ m : ℕ, u' ^ 3 ^ m = 1 :=
    ⟨1, Subtype.ext (by simpa [hu'] using hu3)⟩
  have hρu1 : ρ u' ≠ 1 := by
    intro h1
    apply hu1
    have := hρ.eq_one hx3 hu3' h1
    simpa [hu'] using congrArg Subtype.val this
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hρu
  have hc1 : c ≠ 1 := by
    intro h1
    apply hρu1
    apply Subtype.ext
    rw [← hc, h1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hrel : ρ p' * ρ y' = ρ u' * (ρ y' * ρ p') := by
    calc ρ p' * ρ y' = (ρ p' * ρ y' * (ρ p')⁻¹ * (ρ y')⁻¹) * (ρ y' * ρ p') := by group
      _ = ρ u' * (ρ y' * ρ p') := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hcomm]
  have hrelm : ((ρ p' : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
      ((ρ y' : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      c • (((ρ y' : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
        ((ρ p' : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) := by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) L =>
      (g : Matrix (Fin 3) (Fin 3) L)) hrel
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    rw [this, ← hc, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hunit : ∀ A : Matrix.SpecialLinearGroup (Fin 3) L,
      IsUnit (A : Matrix (Fin 3) (Fin 3) L) := fun A =>
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [A.2]; exact isUnit_one)
  intro z hz
  have hz' := Subgroup.mem_centralizer_iff.mp hz
  have hzy : ρ z * ρ y' = ρ y' * ρ z := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hz' y (SetLike.mem_coe.mpr hy)).symm
  have hzp : ρ z * ρ p' = ρ p' * ρ z := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hz' p (SetLike.mem_coe.mpr hp)).symm
  obtain ⟨r, hr⟩ := heis_scalar (hunit _) (hunit _) hc1 hrelm
    (g := ((ρ z : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L))
    (by simpa only [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L)) hzy)
    (by simpa only [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L)) hzp)
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨r, ?_, hr.symm ▸ rfl⟩
  have hdet := (ρ z).2
  rw [hr, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  rw [Fintype.card_fin]
  exact hdet

theorem layer_center_facts_odd (P : D4ParOdd ℓ f X σ) {x : C0 σ} (hx : IsClassX σ x)
    (hxD : x ∈ layerSub σ x)
    (hZD : ∀ w ∈ layerSub σ x, (∀ d ∈ layerSub σ x, w * d = d * w) → w ∈ Subgroup.zpowers x)
    (hH : ∃ y ∈ layerSub σ x, ∃ p ∈ layerSub σ x,
      p * y * p⁻¹ * y⁻¹ ≠ 1 ∧ (p * y * p⁻¹ * y⁻¹) ^ 3 = 1 ∧
        ∀ d ∈ layerSub σ x, (p * y * p⁻¹ * y⁻¹) * d = d * (p * y * p⁻¹ * y⁻¹)) :
    (∀ a ∈ Subgroup.centralizer (layerSub σ x : Set (C0 σ)),
      ∀ b ∈ Subgroup.centralizer (layerSub σ x : Set (C0 σ)), a * b = b * a) ∧
    (∀ z ∈ Subgroup.centralizer (layerSub σ x : Set (C0 σ)), (∃ k : ℕ, z ^ (3 ^ k) = 1) →
      z ∈ Subgroup.zpowers x) := by
  obtain ⟨L, _, ρ, hρ, hscal⟩ := layer_centralizer_scalar_odd P hx hZD hH
  have hx3 : x ^ 3 = 1 := hx.1
  have hcube : ∀ w ∈ layerSub σ x, (∀ d ∈ layerSub σ x, w * d = d * w) → w ^ 3 = 1 := by
    intro w hw hwc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hZD w hw hwc)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  refine ⟨fun a ha b hb => ?_, fun z hz hz3 => ?_⟩
  · have haC : a ∈ cenX σ x := centralizer_layer_le_cenX_odd hxD ha
    have hbC : b ∈ cenX σ x := centralizer_layer_le_cenX_odd hxD hb
    set a' : cenX σ x := ⟨a, haC⟩ with ha'
    set b' : cenX σ x := ⟨b, hbC⟩ with hb'
    have hcD : a * b * a⁻¹ * b⁻¹ ∈ layerSub σ x := by
      have := Subgroup.commutator_mem_commutator haC hbC
      rwa [commutatorElement_def] at this
    have hcZ : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (layerSub σ x : Set (C0 σ)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
        (Subgroup.inv_mem _ hb)
    have hcc : ∀ d ∈ layerSub σ x, (a * b * a⁻¹ * b⁻¹) * d = d * (a * b * a⁻¹ * b⁻¹) := by
      intro d hd
      exact ((Subgroup.mem_centralizer_iff.mp hcZ) d (SetLike.mem_coe.mpr hd)).symm
    have hc3 : (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 := hcube _ hcD hcc
    have hρ1 : ρ (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
      have hB := hscal b' hb
      have hcomm : ρ a' * ρ b' = ρ b' * ρ a' := Subgroup.mem_center_iff.mp hB (ρ a')
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h3' : ∃ m : ℕ, (a' * b' * a'⁻¹ * b'⁻¹) ^ 3 ^ m = 1 :=
      ⟨1, Subtype.ext (by simpa [ha', hb'] using hc3)⟩
    have h1 := hρ.eq_one hx3 h3' hρ1
    have h2 : a * b * a⁻¹ * b⁻¹ = 1 := by simpa [ha', hb'] using congrArg Subtype.val h1
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h2, one_mul]
  · have hzC : z ∈ cenX σ x := centralizer_layer_le_cenX_odd hxD hz
    have h3' : ∃ k : ℕ, (⟨z, hzC⟩ : cenX σ x) ^ 3 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hz3
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    exact hρ.2.2.1 ⟨z, hzC⟩ h3' (hscal ⟨z, hzC⟩ hz)

end Leaves

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

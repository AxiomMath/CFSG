module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.L5U5.Models
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (quotientAutHom)

variable {p f : ℕ} {F : Type} [Field F]

theorem map_mul_σ (σ : F ≃+* F) {m n o : Type} [Fintype n] (M : Matrix m n F) (N : Matrix n o F) :
    (M * N).map σ = M.map σ * N.map σ :=
  Matrix.map_mul (f := (σ : F →+* F))

theorem map_one_σ (σ : F ≃+* F) {m : Type} [DecidableEq m] [Fintype m] :
    (1 : Matrix m m F).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

theorem map_bar_bar (h : UnitaryFieldData p f F) {m n : Type} (M : Matrix m n F) :
    (M.map h.bar).map h.bar = M := by
  ext i j
  simp [h.bar_bar]

theorem eq_of_inv_mul_mem_center {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (a b : G →* H) (hab : ∀ g, (a g)⁻¹ * b g ∈ Subgroup.center H) : a = b := by
  let χ : G →* Subgroup.center H :=
    { toFun := fun g => ⟨(a g)⁻¹ * b g, hab g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g g' => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (hab g)
        have hc' : (a g')⁻¹ * ((a g)⁻¹ * b g) = ((a g)⁻¹ * b g) * (a g')⁻¹ := hc ((a g')⁻¹)
        change (a (g * g'))⁻¹ * b (g * g') = (a g)⁻¹ * b g * ((a g')⁻¹ * b g')
        rw [map_mul, map_mul, _root_.mul_inv_rev]
        calc (a g')⁻¹ * (a g)⁻¹ * (b g * b g') = ((a g')⁻¹ * ((a g)⁻¹ * b g)) * b g' := by
              simp only [mul_assoc]
          _ = ((a g)⁻¹ * b g) * (a g')⁻¹ * b g' := by rw [hc']
          _ = (a g)⁻¹ * b g * ((a g')⁻¹ * b g') := by simp only [mul_assoc] }
  have hker : _root_.commutator G ≤ χ.ker := Abelianization.commutator_subset_ker χ
  have htop : _root_.commutator G = ⊤ := Group.IsPerfect.commutator_eq_top
  refine MonoidHom.ext fun g => ?_
  have hg : g ∈ χ.ker := hker (htop ▸ Subgroup.mem_top g)
  have h1 : (a g)⁻¹ * b g = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
  exact inv_mul_eq_one.1 h1

abbrev HI : Type := HypIndex 2 0

abbrev IsTr (h : UnitaryFieldData p f F) (R : Matrix (Fin 4) HI F) : Prop :=
  IsHypTransport (r := 2) (ε := 0) h R

noncomputable abbrev tInv (h : UnitaryFieldData p f F) (R : Matrix (Fin 4) HI F) :
    Matrix HI (Fin 4) F :=
  transportInv (r := 2) (ε := 0) h R

theorem tInv_mul {h : UnitaryFieldData p f F} {R : Matrix (Fin 4) HI F} (hR : IsTr h R) :
    tInv h R * R = 1 := transportInv_mul hR

theorem mul_tInv {h : UnitaryFieldData p f F} {R : Matrix (Fin 4) HI F} (hR : IsTr h R) :
    R * tInv h R = 1 := mul_transportInv hR

theorem tInv_def (h : UnitaryFieldData p f F) (R : Matrix (Fin 4) HI F) :
    tInv h R = hypGram 2 0 F * (R.map h.bar)ᵀ := rfl

theorem hypGram_map_bar (h : UnitaryFieldData p f F) :
    (hypGram 2 0 F).map h.bar = hypGram 2 0 F := hypGram_map (h.bar : F →+* F)

theorem tInv_unitary {h : UnitaryFieldData p f F} {R : Matrix (Fin 4) HI F} (hR : IsTr h R) :
    ((tInv h R).map h.bar)ᵀ * hypGram 2 0 F * tInv h R = 1 := by
  have hJJ : hypGram 2 0 F * hypGram 2 0 F = 1 := hypGram_mul_self
  have h1 : ((tInv h R).map h.bar)ᵀ = R * hypGram 2 0 F := by
    rw [tInv_def, Matrix.map_mul, hypGram_map_bar, ← Matrix.transpose_map, map_bar_bar,
      Matrix.transpose_mul, Matrix.transpose_transpose, hypGram_transpose]
  rw [h1, Matrix.mul_assoc R, hJJ, Matrix.mul_one]
  exact mul_tInv hR

@[expose] noncomputable def natMat (h : UnitaryFieldData p f F) {R : Matrix (Fin 4) HI F}
    (hR : IsTr h R) (A : GL HI F) (σ : F ≃+* F) : GL (Fin 4) F where
  val := R * (A : Matrix HI HI F) * (tInv h R).map σ
  inv := R.map σ * ((A⁻¹ : GL HI F) : Matrix HI HI F) * tInv h R
  val_inv := by
    have h1 : (tInv h R).map σ * R.map σ = 1 := by
      rw [← map_mul_σ, tInv_mul hR, map_one_σ]
    have h2 : (A : Matrix HI HI F) * ((A⁻¹ : GL HI F) : Matrix HI HI F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc R * (A : Matrix HI HI F) * (tInv h R).map σ *
        (R.map σ * ((A⁻¹ : GL HI F) : Matrix HI HI F) * tInv h R)
        = R * (A : Matrix HI HI F) * ((tInv h R).map σ * R.map σ) *
          ((A⁻¹ : GL HI F) : Matrix HI HI F) * tInv h R := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [h1, Matrix.mul_one, Matrix.mul_assoc R, h2, Matrix.mul_one, mul_tInv hR]
  inv_val := by
    have h1 : R.map σ * (tInv h R).map σ = 1 := by
      rw [← map_mul_σ, mul_tInv hR, map_one_σ]
    have h2 : ((A⁻¹ : GL HI F) : Matrix HI HI F) * (A : Matrix HI HI F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc R.map σ * ((A⁻¹ : GL HI F) : Matrix HI HI F) * tInv h R *
        (R * (A : Matrix HI HI F) * (tInv h R).map σ)
        = R.map σ * ((A⁻¹ : GL HI F) : Matrix HI HI F) *
          (tInv h R * R) * (A : Matrix HI HI F) * (tInv h R).map σ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [tInv_mul hR, Matrix.mul_one, Matrix.mul_assoc (R.map σ), h2, Matrix.mul_one, h1]

theorem natMat_val (h : UnitaryFieldData p f F) {R : Matrix (Fin 4) HI F} (hR : IsTr h R)
    (A : GL HI F) (σ : F ≃+* F) :
    ((natMat h hR A σ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      R * (A : Matrix HI HI F) * (tInv h R).map σ := rfl

theorem natMat_inv_val (h : UnitaryFieldData p f F) {R : Matrix (Fin 4) HI F} (hR : IsTr h R)
    (A : GL HI F) (σ : F ≃+* F) :
    (((natMat h hR A σ)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      R.map σ * ((A⁻¹ : GL HI F) : Matrix HI HI F) * tInv h R := rfl

theorem tInv_unitary_map {h : UnitaryFieldData p f F} {R : Matrix (Fin 4) HI F} (hR : IsTr h R)
    {σ : F ≃+* F} (hσ : σ = RingEquiv.refl F ∨ ∀ c, σ c = h.bar c) :
    (((tInv h R).map σ).map h.bar)ᵀ * hypGram 2 0 F * (tInv h R).map σ = 1 := by
  rcases hσ with rfl | hσ
  · exact tInv_unitary hR
  · have hmap : (tInv h R).map σ = (tInv h R).map h.bar := Matrix.ext fun i j => hσ _
    rw [hmap]
    have h2 := congrArg (fun M => M.map h.bar) (tInv_unitary hR)
    simp only [Matrix.map_mul, Matrix.transpose_map, map_bar_bar, hypGram_map_bar] at h2
    rw [map_bar_bar]
    simpa [map_one_σ] using h2

theorem natMat_unitary {h : UnitaryFieldData p f F} {R : Matrix (Fin 4) HI F} (hR : IsTr h R)
    {A : GL HI F} (hA : A ∈ hypUnitary h 2 0) {σ : F ≃+* F}
    (hσ : σ = RingEquiv.refl F ∨ ∀ c, σ c = h.bar c) :
    (((natMat h hR A σ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map h.bar)ᵀ *
      ((natMat h hR A σ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  have hA' : ((A : Matrix HI HI F).map h.bar)ᵀ * hypGram 2 0 F * (A : Matrix HI HI F) =
      hypGram 2 0 F := mem_hypUnitary.1 hA
  have hRJ : (R.map h.bar)ᵀ * R = hypGram 2 0 F := hR
  rw [natMat_val, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  calc (((tInv h R).map σ).map h.bar)ᵀ * (((A : Matrix HI HI F).map h.bar)ᵀ *
        (R.map h.bar)ᵀ) * (R * (A : Matrix HI HI F) * (tInv h R).map σ)
      = (((tInv h R).map σ).map h.bar)ᵀ * (((A : Matrix HI HI F).map h.bar)ᵀ *
        ((R.map h.bar)ᵀ * R) * (A : Matrix HI HI F)) * (tInv h R).map σ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hRJ, hA', tInv_unitary_map hR hσ]

theorem natMat_sq_of_refl {h : UnitaryFieldData p f F} {R : Matrix (Fin 4) HI F} (hR : IsTr h R)
    {A : GL HI F} {c : F} (hAA : (A : Matrix HI HI F) * (A : Matrix HI HI F) = c • 1) :
    ((natMat h hR A (RingEquiv.refl F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((natMat h hR A (RingEquiv.refl F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        c • 1 := by
  have hRi : (tInv h R).map (RingEquiv.refl F) = tInv h R := rfl
  rw [natMat_val, hRi]
  calc R * (A : Matrix HI HI F) * tInv h R * (R * (A : Matrix HI HI F) * tInv h R)
      = R * ((A : Matrix HI HI F) * ((tInv h R * R) * (A : Matrix HI HI F))) * tInv h R := by
        simp only [Matrix.mul_assoc]
    _ = c • 1 := by
      rw [tInv_mul hR, Matrix.one_mul, hAA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        mul_tInv hR]

theorem natMat_mul_map_of_bar {h : UnitaryFieldData p f F} {R : Matrix (Fin 4) HI F}
    (hR : IsTr h R) {A : GL HI F} {σ : F ≃+* F} (hσ : ∀ c, σ c = h.bar c) {c : F}
    (hAA : (A : Matrix HI HI F) * (A : Matrix HI HI F).map h.bar = c • 1) :
    ((natMat h hR A σ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((natMat h hR A σ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map h.bar = c • 1 := by
  have hmap : (tInv h R).map σ = (tInv h R).map h.bar := Matrix.ext fun i j => hσ _
  have hbb : ((tInv h R).map h.bar).map h.bar = tInv h R := map_bar_bar h _
  rw [natMat_val, hmap, Matrix.map_mul, Matrix.map_mul, hbb]
  calc R * (A : Matrix HI HI F) * (tInv h R).map h.bar *
        (R.map h.bar * (A : Matrix HI HI F).map h.bar * tInv h R)
      = R * ((A : Matrix HI HI F) * (((tInv h R).map h.bar * R.map h.bar) *
          (A : Matrix HI HI F).map h.bar)) * tInv h R := by simp only [Matrix.mul_assoc]
    _ = c • 1 := by
      have h1 : (tInv h R).map h.bar * R.map h.bar = 1 := by
        rw [← Matrix.map_mul, tInv_mul hR, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
      rw [h1, Matrix.one_mul, hAA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, mul_tInv hR]

theorem natMat_conj {h : UnitaryFieldData p f F} {R : Matrix (Fin 4) HI F} (hR : IsTr h R)
    (A : GL HI F) (σ : F ≃+* F) (k : Matrix (Fin 4) (Fin 4) F) :
    R * ((A : Matrix HI HI F) * (tInv h R * k * R).map σ *
      ((A⁻¹ : GL HI F) : Matrix HI HI F)) * tInv h R =
      ((natMat h hR A σ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * k.map σ *
        (((natMat h hR A σ)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rw [natMat_val, natMat_inv_val, map_mul_σ, map_mul_σ]
  simp only [Matrix.mul_assoc]

theorem aut_form_uni (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (α : MulAut ↥(StatedSU 4 (p ^ f) F)) (hα : α * α = 1) (hα1 : α ≠ 1) :
    ∃ (A : GL (Fin 4) F) (σ : F ≃+* F),
      (σ = RingEquiv.refl F ∨ ∀ c, σ c = h.bar c) ∧
      ((A : Matrix (Fin 4) (Fin 4) F).map h.bar)ᵀ * (A : Matrix (Fin 4) (Fin 4) F) = 1 ∧
      (∀ k : ↥(StatedSU 4 (p ^ f) F), ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
        A * glAut σ (k : GL (Fin 4) F) * A⁻¹) ∧
      (σ = RingEquiv.refl F → ∃ c : F, c ≠ 0 ∧
        (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) = c • 1) ∧
      ((∀ c, σ c = h.bar c) → ∃ c : F, c ≠ 0 ∧
        (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F).map h.bar = c • 1) := by
  classical
  have hfin : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  obtain ⟨hqs, hcenter⟩ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := p) (f := f)
      (n := 4) hF (by norm_num) (fun h => by simp at h)
  have hperf : Group.IsPerfect ↥(StatedSU 4 (p ^ f) F) := hqs.1
  have hZ : unitaryScalars h 4 = Subgroup.center ↥(StatedSU 4 (p ^ f) F) :=
    (unitaryScalars_eq h (by norm_num)).trans hcenter.symm
  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin 4) HI F, IsTr h R :=
    exists_isHypTransport (r := 2) (ε := 0) h
  let e : hypSU h 2 0 ≃* ↥(StatedSU 4 (p ^ f) F) := hypTransport h hR
  have hZhyp : hypScalars h 2 0 = Subgroup.center (hypSU h 2 0) := by
    ext z
    rw [mem_hypScalars_iff_transport hR z, ← mem_center_iff_of_mulEquiv e z]
    change e z ∈ unitaryScalars h 4 ↔ e z ∈ _
    rw [hZ]
  let α' : MulAut (hypSU h 2 0) := MulAut.congr e.symm α
  have hα'e : ∀ g, e (α' g) = α (e g) := fun g => by simp [α', MulAut.congr_apply]
  have hpres : ∀ (σ : MulAut (hypSU h 2 0)), ∀ z ∈ hypScalars h 2 0,
      (MonoidHom.id (MulAut (hypSU h 2 0))) σ z ∈ hypScalars h 2 0 := by
    intro σ z hz
    rw [hZhyp] at hz ⊢
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have h1 := congrArg σ (hz (σ.symm g))
    simpa [map_mul] using h1
  let β : MulAut (hypPSU h 2 0) :=
    quotientAutHom (MonoidHom.id (MulAut (hypSU h 2 0))) (hypScalars h 2 0) hpres α'
  have hβmk : ∀ g, β (hypProj h 2 0 g) = hypProj h 2 0 (α' g) := fun g => rfl
  have hcenter_of : ∀ (τ : ↥(StatedSU 4 (p ^ f) F) →* ↥(StatedSU 4 (p ^ f) F))
      (τ' : hypSU h 2 0 →* hypSU h 2 0), (∀ k, τ k = e (τ' (e.symm k))) →
      (∀ g, hypProj h 2 0 (α' g) = hypProj h 2 0 (τ' g)) →
      ∀ k, (α k)⁻¹ * τ k ∈ Subgroup.center ↥(StatedSU 4 (p ^ f) F) := by
    intro τ τ' hτ hproj k
    have h2 : (α' (e.symm k))⁻¹ * τ' (e.symm k) ∈ hypScalars h 2 0 :=
      QuotientGroup.eq.1 (hproj (e.symm k))
    have h3 := (mem_hypScalars_iff_transport hR _).1 h2
    rw [map_mul, map_inv, hα'e, MulEquiv.apply_symm_apply] at h3
    rw [hτ k, ← hZ]
    exact h3
  have hβ2 : β * β = 1 := by
    have h1 : α' * α' = 1 := by
      change MulAut.congr e.symm α * MulAut.congr e.symm α = 1
      rw [← map_mul, hα, map_one]
    have : β * β = quotientAutHom (MonoidHom.id (MulAut (hypSU h 2 0))) (hypScalars h 2 0) hpres
        (α' * α') := (map_mul _ _ _).symm
    rw [this, h1, map_one]
  have hβ1 : β ≠ 1 := by
    intro hb
    apply hα1
    have := eq_of_inv_mul_mem_center α.toMonoidHom (MonoidHom.id _)
      (hcenter_of (MonoidHom.id _) (MonoidHom.id _) (fun k => by simp) (fun g => by
        rw [← hβmk, hb]; rfl))
    refine MulEquiv.ext fun k => ?_
    exact congrArg (fun φ : ↥(StatedSU 4 (p ^ f) F) →* ↥(StatedSU 4 (p ^ f) F) => φ k) this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf β = 2 := orderOf_eq_prime (by rw [pow_two]; exact hβ2) hβ1
  obtain ⟨hΦapply, -, -, hrep⟩ := odd_unitary_automorphism_semilinear_representation h hp2
    (r := 2) (ε := 0) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨A, σ, hx, hA, hΦ, hσ, hid, hbar⟩ := hrep β hord
  let τ0 : GL HI F →* GL HI F := (MulAut.conj A).toMonoidHom.comp (glAut σ).toMonoidHom
  let τ' : hypSU h 2 0 →* hypSU h 2 0 :=
    (τ0.comp (hypSU h 2 0).subtype).codRestrict (hypSU h 2 0) (fun g => conj_mem_hypSU hx g)
  have hτ' : ∀ g : hypSU h 2 0, ((τ' g : hypSU h 2 0) : GL HI F) =
      A * glAut σ (g : GL HI F) * A⁻¹ := fun g => rfl
  have hkey : ∀ g : hypSU h 2 0, hypProj h 2 0 (α' g) = hypProj h 2 0 (τ' g) := by
    intro g
    have h1 := hΦapply ⟨⟨A, σ⟩, hx⟩ g
    rw [hΦ] at h1
    exact h1
  let τ : ↥(StatedSU 4 (p ^ f) F) →* ↥(StatedSU 4 (p ^ f) F) :=
    e.toMonoidHom.comp (τ'.comp e.symm.toMonoidHom)
  have hτe : ∀ k, τ k = e (τ' (e.symm k)) := fun k => rfl
  have hατ : α.toMonoidHom = τ := eq_of_inv_mul_mem_center _ _ (hcenter_of τ τ' hτe hkey)
  refine ⟨natMat h hR A σ, σ, hσ, natMat_unitary hR hA hσ, ?_, ?_, ?_⟩
  · intro k
    have h1 : ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
        ((τ k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) :=
      congrArg (fun φ : ↥(StatedSU 4 (p ^ f) F) →* ↥(StatedSU 4 (p ^ f) F) =>
        ((φ k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F)) hατ
    rw [h1]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glAut, ← natMat_conj hR A σ]
    change R * (((τ' (e.symm k) : hypSU h 2 0) : GL HI F) : Matrix HI HI F) * tInv h R = _
    rw [hτ', Units.val_mul, Units.val_mul, coe_glAut]
    change R * ((A : Matrix HI HI F) * ((((e.symm k : hypSU h 2 0) : GL HI F) :
      Matrix HI HI F)).map σ * ((A⁻¹ : GL HI F) : Matrix HI HI F)) * tInv h R = _
    rw [coe_hypTransport_symm hR k]
  · intro hσ1
    have h1 := hid hσ1
    have h2 : (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h 2 0) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h 2 0)
      rwa [h1] at this
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
    obtain ⟨c, -, -, hc⟩ := h2
    have hAc : A * A = GeneralLinearGroup.scalar HI c := by
      rw [← hc, sq]
      rfl
    refine ⟨(c : F), c.ne_zero, ?_⟩
    subst hσ1
    have hAA : (A : Matrix HI HI F) * (A : Matrix HI HI F) = (c : F) • 1 := by
      have := congrArg (fun g : GL HI F => (g : Matrix HI HI F)) hAc
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at this
      rw [this, scalar_apply, smul_one_eq_diagonal]
    exact natMat_sq_of_refl hR hAA
  · intro hσ1
    obtain ⟨c, hc0, hAA⟩ := hbar hσ1
    exact ⟨c, hc0, natMat_mul_map_of_bar hR hσ1 hAA⟩

end CFSG.GH74.Generic.S1.Uni

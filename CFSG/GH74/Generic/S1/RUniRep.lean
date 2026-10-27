module

public import CFSG.GH74.Generic.S1.UniForm

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (quotientAutHom)
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F]

theorem rrep_comm_bar (h : UnitaryFieldData p f F) (σ : F ≃+* F) (c : F) :
    σ (h.bar c) = h.bar (σ c) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]

theorem rrep_isTr_map (h : UnitaryFieldData p f F) {R : Matrix (Fin 4) HI F} (hR : IsTr h R)
    (σ : F ≃+* F) : IsTr h (R.map σ) := by
  have hRJ : (R.map h.bar)ᵀ * R = hypGram 2 0 F := hR
  have h2 : (R.map h.bar).map σ = (R.map σ).map h.bar := by
    ext i j
    simp [rrep_comm_bar h σ]
  have h3 : (hypGram 2 0 F).map σ = hypGram 2 0 F := hypGram_map (σ : F →+* F)
  show ((R.map σ).map h.bar)ᵀ * R.map σ = hypGram 2 0 F
  rw [← h2, ← Matrix.transpose_map, ← map_mul_σ, hRJ, h3]

theorem rrep_tInv_map (h : UnitaryFieldData p f F) (R : Matrix (Fin 4) HI F) (σ : F ≃+* F) :
    (tInv h R).map σ = tInv h (R.map σ) := by
  have h2 : (R.map h.bar).map σ = (R.map σ).map h.bar := by
    ext i j
    simp [rrep_comm_bar h σ]
  have h3 : (hypGram 2 0 F).map σ = hypGram 2 0 F := hypGram_map (σ : F →+* F)
  rw [tInv_def, tInv_def, map_mul_σ, h3, ← h2, Matrix.transpose_map]

theorem rrep_tInv_unitary_map {h : UnitaryFieldData p f F} {R : Matrix (Fin 4) HI F} (hR : IsTr h R)
    (σ : F ≃+* F) :
    (((tInv h R).map σ).map h.bar)ᵀ * hypGram 2 0 F * (tInv h R).map σ = 1 := by
  rw [rrep_tInv_map]
  exact tInv_unitary (rrep_isTr_map h hR σ)

theorem rrep_natMat_unitary {h : UnitaryFieldData p f F} {R : Matrix (Fin 4) HI F} (hR : IsTr h R)
    {A : GL HI F} (hA : A ∈ hypUnitary h 2 0) (σ : F ≃+* F) :
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
    _ = 1 := by rw [hRJ, hA', rrep_tInv_unitary_map hR σ]


theorem uni_aut_rep (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (α : MulAut ↥(StatedSU 4 (p ^ f) F)) :
    ∃ (N : GL (Fin 4) F) (σ : F ≃+* F),
      ((N : Matrix (Fin 4) (Fin 4) F).map h.bar)ᵀ * (N : Matrix (Fin 4) (Fin 4) F) = 1 ∧
      ∀ k : ↥(StatedSU 4 (p ^ f) F), ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
        N * glAut σ (k : GL (Fin 4) F) * N⁻¹ := by
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
  obtain ⟨hΦapply, hsurj, -, -⟩ := odd_unitary_automorphism_semilinear_representation h hp2
    (r := 2) (ε := 0) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨x₀, hx₀⟩ := hsurj β
  obtain ⟨x, hxΦ, -, hxU⟩ := exists_unitary_rep h (r := 2) (ε := 0) (by norm_num) (by norm_num)
    (by norm_num) x₀
  rw [hx₀] at hxΦ
  obtain ⟨⟨A, σ⟩, hx⟩ := x
  change A ∈ hypUnitary h 2 0 at hxU
  let τ0 : GL HI F →* GL HI F := (MulAut.conj A).toMonoidHom.comp (glAut σ).toMonoidHom
  let τ' : hypSU h 2 0 →* hypSU h 2 0 :=
    (τ0.comp (hypSU h 2 0).subtype).codRestrict (hypSU h 2 0) (fun g => conj_mem_hypSU hx g)
  have hτ' : ∀ g : hypSU h 2 0, ((τ' g : hypSU h 2 0) : GL HI F) =
      A * glAut σ (g : GL HI F) * A⁻¹ := fun g => rfl
  have hkey : ∀ g : hypSU h 2 0, hypProj h 2 0 (α' g) = hypProj h 2 0 (τ' g) := by
    intro g
    have h1 := hΦapply ⟨⟨A, σ⟩, hx⟩ g
    rw [hxΦ] at h1
    exact h1
  let τ : ↥(StatedSU 4 (p ^ f) F) →* ↥(StatedSU 4 (p ^ f) F) :=
    e.toMonoidHom.comp (τ'.comp e.symm.toMonoidHom)
  have hτe : ∀ k, τ k = e (τ' (e.symm k)) := fun k => rfl
  have hατ : α.toMonoidHom = τ := eq_of_inv_mul_mem_center _ _ (hcenter_of τ τ' hτe hkey)
  refine ⟨natMat h hR A σ, σ, rrep_natMat_unitary hR hxU σ, ?_⟩
  intro k
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

end CFSG.GH74.Generic.S1.Uni

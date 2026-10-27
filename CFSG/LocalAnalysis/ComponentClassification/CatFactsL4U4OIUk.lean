module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUj
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUi

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank LinearFlag
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem phi_fix_y {δ : h.fixedFieldˣ} (h2 : (2 : h.fixedField) ≠ 0) {A P : GL (Fin 4) K}
    (y : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)) →* unitarySU p f K 4)
    (hy : ∀ g, ((y g : unitarySU p f K 4) : GL (Fin 4) K) =
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹)
    (hAP : (A : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K).map h.bar = P)
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField))) :
    (((y g : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) *
        (((y g : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
  have hmem : ∀ g, P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹ ∈
      unitarySU p f K 4 := fun g => by rw [← hy]; exact (y g).2
  have h1 := yHom_real h h2 P hmem hAP g
  have hyg : ((yHom h h2 P hmem g : unitarySU p f K 4) : GL (Fin 4) K) = y g := by
    rw [coe_yHom, hy]
  rw [hyg] at h1
  have h3 := congrArg Units.val h1
  rw [Units.val_mul, Units.val_mul] at h3
  exact h3.symm

theorem outer_cent_U4 (hp2 : p ≠ 2) {φ : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    (hφ2 : φ ^ 2 = 1) {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hrow : SelectorRowOU h φ J') (ψ' : MulAut (StatedProj (StatedSU 4 (p ^ f) K)))
    (hψ : ∀ x ∈ J', ψ' x = x) : ψ' ∈ Subgroup.zpowers φ := by
  classical
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : CharP h.fixedField p := Subfield.charP h.fixedField p
  obtain ⟨A, hAu, -, δ, hδ, h2, -, P, y, hφA, hAP, -, hy, hJ⟩ := hrow
  have hfixy : ∀ g, ψ' (thU p f K (y g)) = thU p f K (y g) := fun g =>
    hψ _ (by rw [hJ]; exact ⟨g, rfl⟩)
  have hker : (thU p f K).ker ≤ Subgroup.center (unitarySU p f K 4) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    exact mem_center_of_mem_scal hz
  obtain ⟨B, τ, hB, hBu, hlift, -⟩ := CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp2
    (d := 4) (by norm_num) (thU p f K) thU_surjective hker ψ'
  have hBU : B ∈ uMat h 4 := (mem_uMat h).2 hBu
  set T := (unitarySU p f K 4).subtype.comp
    ((ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom B τ hB).comp y) with hT
  have hTapp : ∀ g, T g = B * glAut τ ((y g : unitarySU p f K 4) : GL (Fin 4) K) * B⁻¹ :=
    fun g => rfl
  have hunip : ∀ u : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)),
      u ^ p = 1 → T u = y u := by
    intro u hu
    have hyp : y u ^ p = 1 := by rw [← map_pow, hu, map_one]
    set w := ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom B τ hB (y u) with hw
    have hwp : w ^ p = 1 := by rw [hw, ← map_pow, hyp, map_one]
    have h1 : thU p f K w = thU p f K (y u) := by rw [hw, hlift, hfixy]
    have h3 := OCU.eq_of_thU_eq h hp2 hyp hwp h1
    exact congrArg Subtype.val h3
  have hgt : ∀ t : extension (δ : h.fixedField),
      T (OIL.uE (δ : h.fixedField) (t - 1) * OIL.lE (δ : h.fixedField) 1 *
        OIL.uE (δ : h.fixedField) (-1)) =
      y (OIL.uE (δ : h.fixedField) (t - 1) * OIL.lE (δ : h.fixedField) 1 *
        OIL.uE (δ : h.fixedField) (-1)) := fun t => by
    rw [map_mul, map_mul, hunip _ (OIL.uE_pow_char _ _), hunip _ (OIL.lE_pow_char _ _),
      hunip _ (OIL.uE_pow_char _ _), map_mul, map_mul]
    rfl
  have htrace : ∀ g, ((((y g : unitarySU p f K 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)).trace =
        ((Umat δ h2 g : Matrix (Fin 4) (Fin 4) h.fixedField).trace : K) := by
    intro g
    rw [hy, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul]
    exact (AddMonoidHom.map_trace h.fixedField.subtype _).symm
  have hτk : ∀ x ∈ h.fixedField, τ x = x := by
    intro x hx
    have : Fintype h.fixedField := Fintype.ofFinite _
    have hq : Fintype.card h.fixedField % 2 = 1 := by
      rw [← Nat.card_eq_fintype_card, h.card_fixedField]
      exact Nat.odd_iff.mp (h.prime.odd_of_ne_two hp2).pow
    obtain ⟨a, b, hab⟩ := OFL.exists_norm_eq hq δ.ne_zero ⟨x, hx⟩
    set t : extension (δ : h.fixedField) := ⟨a, b⟩
    set gt := OIL.uE (δ : h.fixedField) (t - 1) * OIL.lE (δ : h.fixedField) 1 *
      OIL.uE (δ : h.fixedField) (-1) with hgtdef
    have hN : (Umat δ h2 gt : Matrix (Fin 4) (Fin 4) h.fixedField).trace = ⟨x, hx⟩ := by
      rw [hgtdef, OIL.trace_rowOHom_gT δ h2 _ t]
      exact hab
    have h1 := congrArg (fun X : GL (Fin 4) K => (X : Matrix (Fin 4) (Fin 4) K).trace) (hgt t)
    rw [hTapp, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul, coe_glAut, ← AddMonoidHom.map_trace,
      ← hgtdef, htrace, hN] at h1
    exact h1
  rcases eq_id_or_eq_bar h hp2 τ hτk with hτ1 | hτb
  ·
    have hgl : ∀ X : GL (Fin 4) K, glAut τ X = X := fun X => by
      ext i j
      exact hτ1 _
    have hcu : IsCU h B ψ' := ⟨hBU, fun g g' hg => by
      rw [← hlift g]
      congr 1
      apply Subtype.ext
      rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, hgl, hg]⟩
    rw [eq_one_of_isCU_fix h hp2 h2 P y hy hcu hfixy]
    exact one_mem _
  ·
    have hgl : ∀ X : GL (Fin 4) K, ((glAut τ X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (X : Matrix (Fin 4) (Fin 4) K).map h.bar := fun X => by
      ext i j
      exact hτb _
    have hAU : A ∈ uMat h 4 := (mem_uMat h).2 hAu
    have hcu : IsCU h (A * glAut τ B) (φ * ψ') := by
      refine ⟨mul_mem hAU (glAut_mem_uMat h τ hBU), fun g g' hg => ?_⟩
      rw [MulAut.mul_apply, ← hlift g]
      apply hφA
      rw [ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, hg, Units.val_mul,
        Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hgl, hgl, Matrix.map_mul,
        Matrix.map_mul, Matrix.map_map]
      have hbb : (h.bar ∘ h.bar) = id := funext fun c => h.bar_bar c
      rw [hbb, Matrix.map_id]
      have hinv : ((↑B⁻¹ : Matrix (Fin 4) (Fin 4) K)).map h.bar =
          ((GeneralLinearGroup.map h.bar B)⁻¹ : GL (Fin 4) K) := by
        rw [← map_inv]
        rfl
      have hinv' : (↑(A * glAut τ B)⁻¹ : Matrix (Fin 4) (Fin 4) K) =
          ((glAut τ B)⁻¹ : GL (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        rw [_root_.mul_inv_rev, Units.val_mul]
      have hglB : glAut τ B = GeneralLinearGroup.map h.bar B :=
        Units.ext (by rw [hgl]; rfl)
      rw [hinv', hinv, hglB]
      simp only [Matrix.mul_assoc]
    have hfix1 : ∀ g, (φ * ψ') (thU p f K (y g)) = thU p f K (y g) := by
      intro g
      rw [MulAut.mul_apply, hfixy]
      exact hφA _ _ (phi_fix_y h h2 y hy hAP g)
    have h1 := eq_one_of_isCU_fix h hp2 h2 P y hy hcu hfix1
    have h3 : ψ' = φ⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hφinv : φ⁻¹ = φ := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, hφ2]
    rw [h3, hφinv]
    exact Subgroup.mem_zpowers φ

end OIU

end CFSG.ComponentClassification.CatFactsL4U4

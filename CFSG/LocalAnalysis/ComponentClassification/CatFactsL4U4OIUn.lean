module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUm
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUk
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUl

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank LinearFlag
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem outer_fus_U4 (hp2 : p ≠ 2) {φ : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))} (hrow : SelectorRowOU h φ J')
    (ζ : StatedProj (StatedSU 4 (p ^ f) K)) (hζ : ζ ∈ J') (hζ2 : orderOf ζ = 2) :
    ∃ γ : StatedProj (StatedSU 4 (p ^ f) K),
      (MulAut.conj γ)⁻¹ * φ * MulAut.conj γ = φ * MulAut.conj ζ := by
  classical
  have : Finite K := h.finite
  obtain ⟨A, hAu, -, δ, hδ, h2, d, P, y, hφA, hAP, hPP, hy, hJ⟩ := hrow
  have : Fact (¬ IsSquare (δ : h.fixedField)) := ⟨hδ⟩
  rw [hJ] at hζ
  obtain ⟨g, rfl⟩ := hζ
  rw [MonoidHom.comp_apply] at hζ2 ⊢
  have hgg := mul_self_eq_neg_one_of_involution h hp2 hδ h2 P y hy g hζ2
  have : Fintype h.fixedField := Fintype.ofFinite _
  have hq : Fintype.card h.fixedField % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, h.card_fixedField]
    exact Nat.odd_iff.mp (h.prime.odd_of_ne_two hp2).pow
  obtain ⟨a, ha⟩ := OIL.exists_conj_g0 hq h2 hδ g hgg
  obtain ⟨j, hj0, hjb⟩ := exists_bar_neg h
  have hj2 : j ^ 2 ∈ h.fixedField := by rw [h.mem_fixedField, map_pow, hjb, neg_sq]
  have hj2ne : (⟨j ^ 2, hj2⟩ : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg Subtype.val h0
    exact pow_ne_zero 2 hj0 h1
  obtain ⟨a₀, b₀, hab₀⟩ := OIL.exists_sq_add_sq hq (-(⟨j ^ 2, hj2⟩ : h.fixedField)⁻¹)
  have hab : (((a₀ : h.fixedField) : K) ^ 2 + ((b₀ : h.fixedField) : K) ^ 2) * j ^ 2 = -1 := by
    have h1 : ((a₀ : h.fixedField) : K) ^ 2 + ((b₀ : h.fixedField) : K) ^ 2 = -(j ^ 2)⁻¹ := by
      have h3 := congrArg (fun x : h.fixedField => (x : K)) hab₀
      push_cast at h3
      exact h3
    rw [h1]
    field_simp
  obtain ⟨hXbar, hXG, hXdet⟩ := fusion_matrix h hp2 ((δ : h.fixedField) : K) hjb
    (h.mem_fixedField.mp a₀.2) (h.mem_fixedField.mp b₀.2) hab
  set X₀ := OIL.mD ((a₀ : K) * j) ((b₀ : K) * j) 2⁻¹ with hX₀
  set ι := h.fixedField.subtype with hι
  set Uk := (GeneralLinearGroup.map ι).comp (Umat δ h2) with hUk
  set X0 : GL (Fin 4) K := Matrix.SpecialLinearGroup.toGL ⟨X₀, hXdet⟩ with hX0
  set X : GL (Fin 4) K := Uk a * X0 * (Uk a)⁻¹ with hX
  set γ' : GL (Fin 4) K := P * X * P⁻¹ with hγ'
  have hreal : ∀ u, GeneralLinearGroup.map h.bar (Uk u) = Uk u := fun u =>
    Units.ext (map_bar_real h _)
  have hG : (gramQ (δ : h.fixedField)).map ι = gramQ ((δ : h.fixedField) : K) := map_gramQ ι _
  have hUG : ((Uk a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
      gramQ ((δ : h.fixedField) : K) * (Uk a : GL (Fin 4) K) =
        gramQ ((δ : h.fixedField) : K) := by
    rw [← hG]
    change ((Umat δ h2 a : Matrix (Fin 4) (Fin 4) h.fixedField).map ι)ᵀ *
      (gramQ (δ : h.fixedField)).map ι * (Umat δ h2 a : Matrix (Fin 4) (Fin 4) h.fixedField).map ι
        = _
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, Umat_gram]
  have hXu : uStar h (X : Matrix (Fin 4) (Fin 4) K) * gramQ ((δ : h.fixedField) : K) *
      (X : Matrix (Fin 4) (Fin 4) K) = gramQ ((δ : h.fixedField) : K) :=
    uStar_gram_conj h (map_bar_real h _) hUG hXG
  have hγmem : γ' ∈ unitarySU p f K 4 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · rw [hγ', hX, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, det_mul, det_mul,
        det_mul, det_mul]
      have e1 : (P : Matrix (Fin 4) (Fin 4) K).det * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K).det = 1 := by
        rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
      have e2 : ((Uk a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det *
          (↑(Uk a)⁻¹ : Matrix (Fin 4) (Fin 4) K).det = 1 := by
        rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
      have e3 : (X0 : Matrix (Fin 4) (Fin 4) K).det = 1 := hXdet
      calc _ = ((P : Matrix (Fin 4) (Fin 4) K).det * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K).det) *
              (((Uk a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det *
                (↑(Uk a)⁻¹ : Matrix (Fin 4) (Fin 4) K).det) *
              (X0 : Matrix (Fin 4) (Fin 4) K).det := by ring
        _ = 1 := by rw [e1, e2, e3, one_mul, one_mul]
    · have hPP' : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
          ((d : h.fixedField) : K) • gramQ ((δ : h.fixedField) : K) := by rw [hPP, hG]
      exact uStar_conj_gram h hPP' hXu
  have hAP' : A * GeneralLinearGroup.map h.bar P = P := Units.ext hAP
  have hX0b : GeneralLinearGroup.map h.bar X0 = X0 * Uk (OIL.g0 (δ : h.fixedField)) := by
    apply Units.ext
    rw [Units.val_mul]
    change X₀.map h.bar = X₀ * (Umat δ h2 (OIL.g0 (δ : h.fixedField)) :
      Matrix (Fin 4) (Fin 4) h.fixedField).map ι
    rw [Umat_g0, map_mU0, hXbar]
  have hga : a * OIL.g0 (δ : h.fixedField) * a⁻¹ = g := by rw [ha]; group
  have hZ : γ'⁻¹ * A * GeneralLinearGroup.map h.bar γ' = (y g : GL (Fin 4) K) * A := by
    have hyg : ((y g : unitarySU p f K 4) : GL (Fin 4) K) = P * Uk g * P⁻¹ := hy g
    have hA : A = P * (GeneralLinearGroup.map h.bar P)⁻¹ := by
      calc A = A * GeneralLinearGroup.map h.bar P * (GeneralLinearGroup.map h.bar P)⁻¹ := by
            group
        _ = P * (GeneralLinearGroup.map h.bar P)⁻¹ := by rw [hAP']
    rw [hyg, hγ', hX, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hreal, hX0b, ← hga,
      map_mul, map_mul, map_inv]
    rw [hA]
    group
  have hyA : A * GeneralLinearGroup.map h.bar (y g : GL (Fin 4) K) = (y g : GL (Fin 4) K) * A := by
    have h1 := phi_fix_y h h2 y hy hAP g
    have h3 : (y g : GL (Fin 4) K) = A * GeneralLinearGroup.map h.bar (y g : GL (Fin 4) K) * A⁻¹ :=
      Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h1)
    calc A * GeneralLinearGroup.map h.bar (y g : GL (Fin 4) K)
        = A * GeneralLinearGroup.map h.bar (y g : GL (Fin 4) K) * A⁻¹ * A := by group
      _ = _ := by rw [← h3]
  have hAU : A ∈ uMat h 4 := (mem_uMat h).2 hAu
  refine ⟨thU p f K ⟨γ', hγmem⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨w, rfl⟩ := thU_surjective x
  set γs : unitarySU p f K 4 := ⟨γ', hγmem⟩
  set w₁ : unitarySU p f K 4 := γs * w * γs⁻¹ with hw₁
  set w₂ : unitarySU p f K 4 :=
    ⟨A * GeneralLinearGroup.map h.bar (w₁ : GL (Fin 4) K) * A⁻¹, bar_conj_mem_SU h hAU w₁⟩
    with hw₂
  set w₃ : unitarySU p f K 4 := y g * w * (y g)⁻¹ with hw₃
  set w₄ : unitarySU p f K 4 :=
    ⟨A * GeneralLinearGroup.map h.bar (w₃ : GL (Fin 4) K) * A⁻¹, bar_conj_mem_SU h hAU w₃⟩
    with hw₄
  have hφ₁ : φ (thU p f K w₁) = thU p f K w₂ :=
    hφA w₁ w₂ (by rw [hw₂]; simp only [Units.val_mul]; rfl)
  have hφ₃ : φ (thU p f K w₃) = thU p f K w₄ :=
    hφA w₃ w₄ (by rw [hw₄]; simp only [Units.val_mul]; rfl)
  have hkey : γs⁻¹ * w₂ * γs = w₄ := by
    apply Subtype.ext
    change γ'⁻¹ * (A * GeneralLinearGroup.map h.bar (γ' * (w : GL (Fin 4) K) * γ'⁻¹) * A⁻¹) *
        γ' = A * GeneralLinearGroup.map h.bar ((y g : GL (Fin 4) K) * (w : GL (Fin 4) K) *
          (y g : GL (Fin 4) K)⁻¹) * A⁻¹
    calc γ'⁻¹ * (A * GeneralLinearGroup.map h.bar (γ' * (w : GL (Fin 4) K) * γ'⁻¹) * A⁻¹) * γ'
        = (γ'⁻¹ * A * GeneralLinearGroup.map h.bar γ') *
            GeneralLinearGroup.map h.bar (w : GL (Fin 4) K) *
            (γ'⁻¹ * A * GeneralLinearGroup.map h.bar γ')⁻¹ := by
          rw [map_mul, map_mul, map_inv]; group
      _ = ((y g : GL (Fin 4) K) * A) * GeneralLinearGroup.map h.bar (w : GL (Fin 4) K) *
            ((y g : GL (Fin 4) K) * A)⁻¹ := by rw [hZ]
      _ = (A * GeneralLinearGroup.map h.bar (y g : GL (Fin 4) K)) *
            GeneralLinearGroup.map h.bar (w : GL (Fin 4) K) *
            (A * GeneralLinearGroup.map h.bar (y g : GL (Fin 4) K))⁻¹ := by rw [hyA]
      _ = _ := by rw [map_mul, map_mul, map_inv]; group
  have e1 : MulAut.conj (thU p f K γs) (thU p f K w) = thU p f K w₁ := by
    rw [MulAut.conj_apply, hw₁, map_mul, map_mul, map_inv]
  have e3 : (MulAut.conj (thU p f K γs))⁻¹ (thU p f K w₂) = thU p f K (γs⁻¹ * w₂ * γs) := by
    rw [← map_inv, MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv]
  have e4 : MulAut.conj (thU p f K (y g)) (thU p f K w) = thU p f K w₃ := by
    rw [MulAut.conj_apply, hw₃, map_mul, map_mul, map_inv]
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, e1, hφ₁, e3, hkey, e4, hφ₃]

theorem outerInvCentU4 : OutInv.OuterInvCentU4 := by
  intro K _ p f h hp2 φ hφ2 hφ J' hJφ hJ hJm
  have hrow := selectorRowOU_of_component h hp2 hφ2 hφ hJφ hJ hJm
  exact ⟨fun ψ' _ hψ _ => outer_cent_U4 h hp2 hφ2 hrow ψ' hψ,
    fun ζ hζ hζ2 => outer_fus_U4 h hp2 hrow ζ hζ hζ2⟩

end OIU

end CFSG.ComponentClassification.CatFactsL4U4

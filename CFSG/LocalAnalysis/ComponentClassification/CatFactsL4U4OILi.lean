module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILh
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILf

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIL

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit OutInv

variable {k : Type} [Field k]

theorem conj_beta_eq (R D h : GL (Fin 4) k)
    (hD : (D : Matrix (Fin 4) (Fin 4) k)ᵀ * R * D = (h : Matrix (Fin 4) (Fin 4) k)ᵀ * R) :
    (conjAut 4 k D)⁻¹ * (conjAut 4 k R⁻¹ * dualAut 4 k) * conjAut 4 k D =
      conjAut 4 k R⁻¹ * dualAut 4 k * conjAut 4 k h := by
  have hD' : (GeneralLinearGroup.inverseTranspose D)⁻¹ * R * D =
      (GeneralLinearGroup.inverseTranspose h)⁻¹ * R := Units.ext (by
    simp only [Units.val_mul]
    rw [coe_inverseTranspose_inv, coe_inverseTranspose_inv]
    exact hD)
  have key : D⁻¹ * R⁻¹ * GeneralLinearGroup.inverseTranspose D =
      R⁻¹ * GeneralLinearGroup.inverseTranspose h := by
    have h1 := congrArg (·⁻¹) hD'
    simp only [_root_.mul_inv_rev, inv_inv] at h1
    rw [← mul_assoc] at h1
    exact h1
  calc (conjAut 4 k D)⁻¹ * (conjAut 4 k R⁻¹ * dualAut 4 k) * conjAut 4 k D
      = conjAut 4 k D⁻¹ * conjAut 4 k R⁻¹ * (dualAut 4 k * conjAut 4 k D) := by
        rw [map_inv (conjAut 4 k) D]; group
    _ = conjAut 4 k (D⁻¹ * R⁻¹ * GeneralLinearGroup.inverseTranspose D) * dualAut 4 k := by
        rw [LinearFlag.dualAut_mul_conjAut, map_mul, map_mul]; group
    _ = conjAut 4 k (R⁻¹ * GeneralLinearGroup.inverseTranspose h) * dualAut 4 k := by rw [key]
    _ = _ := by rw [map_mul, mul_assoc, ← LinearFlag.dualAut_mul_conjAut, mul_assoc]

theorem exists_sl_conj [Fintype k] (hq : Fintype.card k % 2 = 1) (h2 : (2 : k) ≠ 0) (δ : kˣ)
    (hδ : ¬ IsSquare (δ : k)) (ψ : (Fin 4 → k) ≃ₗ[k] hermitianSubmodule (δ : k))
    (R : GL (Fin 4) k) (hRT : (R : Matrix (Fin 4) (Fin 4) k)ᵀ = R)
    (hRf : ∀ v : Fin 4 → k,
      v ⬝ᵥ ((R : Matrix (Fin 4) (Fin 4) k) *ᵥ v) = hermitianForm (δ : k) (ψ v))
    (hiso : (rowOHom δ ψ).range ≤ CatalogueBGraphForm.isometryGroup 4 k R)
    (g : SpecialLinearGroup (Fin 2) (extension (δ : k))) (hg : g * g = -1) :
    ∃ D : SpecialLinearGroup (Fin 4) k, (D : Matrix (Fin 4) (Fin 4) k)ᵀ * R * D =
      (rowOHom δ ψ g : Matrix (Fin 4) (Fin 4) k)ᵀ * R := by
  obtain ⟨a, ha⟩ := exists_conj_g0 hq h2 hδ g hg
  have hga : g = a * g0 (δ : k) * a⁻¹ := by rw [ha]; group
  obtain ⟨a₀, b₀, hab⟩ := exists_sq_add_sq hq (-1)
  obtain ⟨D₀, hD₀⟩ := exists_isometry_g0 δ h2 ψ R hRT hRf hab
  set A := rowOHom δ ψ a with hA
  have hAR : (A : Matrix (Fin 4) (Fin 4) k)ᵀ * R * A = R :=
    (CatalogueBGraphForm.mem_isometryGroup 4 k R A).mp (hiso ⟨a, rfl⟩)
  set Am := (A : Matrix (Fin 4) (Fin 4) k) with hAm
  set Ai := ((A⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) with hAi
  have hAAi : Am * Ai = 1 := by rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiA : Ai * Am = 1 := by rw [hAm, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set Rm := (R : Matrix (Fin 4) (Fin 4) k) with hRm
  set H₀ := (rowOHom δ ψ (g0 (δ : k)) : Matrix (Fin 4) (Fin 4) k) with hH₀
  set Dm := (D₀ : Matrix (Fin 4) (Fin 4) k) with hDm
  have hARi : Amᵀ * Rm = Rm * Ai := by
    calc Amᵀ * Rm = Amᵀ * Rm * (Am * Ai) := by rw [hAAi, Matrix.mul_one]
      _ = Amᵀ * Rm * Am * Ai := by simp only [Matrix.mul_assoc]
      _ = Rm * Ai := by rw [hAR]
  have hdet : (Am * Dm * Ai).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hAiA,
      Matrix.det_one, one_mul]
    exact D₀.2
  refine ⟨⟨Am * Dm * Ai, hdet⟩, ?_⟩
  have hgm : (rowOHom δ ψ g : Matrix (Fin 4) (Fin 4) k) = Am * H₀ * Ai := by
    rw [hga, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  change (Am * Dm * Ai)ᵀ * Rm * (Am * Dm * Ai) = _
  rw [hgm]
  calc (Am * Dm * Ai)ᵀ * Rm * (Am * Dm * Ai)
      = Aiᵀ * (Dmᵀ * (Amᵀ * Rm * Am) * Dm) * Ai := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Aiᵀ * (Dmᵀ * Rm * Dm) * Ai := by rw [hAR]
    _ = Aiᵀ * (H₀ᵀ * Rm) * Ai := by rw [hD₀]
    _ = Aiᵀ * H₀ᵀ * (Amᵀ * Rm) := by rw [hARi]; simp only [Matrix.mul_assoc]
    _ = (Am * H₀ * Ai)ᵀ * Rm := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem outer_fus_L4 (F : Type) [Field F] [Fintype F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hF : Fintype.card F = p ^ f) {φ : MulAut (projectiveSL 4 F)} (hφ2 : φ ^ 2 = 1)
    (hφ : φ ∉ (conjAut 4 F).range) {J' : Subgroup (projectiveSL 4 F)} (hJφ : J' ≤ fixSub φ)
    (hJ : IsComponent (J'.subgroupOf (fixSub φ)))
    (hJm : Blueprint.LieModel (↥J' ⧸ center ↥J') .PSL 2 p (2 * f)) (ζ : projectiveSL 4 F)
    (hζ : ζ ∈ J') (hζ2 : orderOf ζ = 2) :
    ∃ γ : projectiveSL 4 F, (MulAut.conj γ)⁻¹ * φ * MulAut.conj γ = φ * MulAut.conj ζ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_card_eq_prime_pow hF
  have hk : Nat.card F = p ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have hq : Fintype.card F % 2 = 1 := by
    rw [hF]
    exact Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  obtain ⟨δ, hδ, ψ, R, C, hRT, hRf, hφC, -, -, hL, hiso, hker, -⟩ :=
    selectorRowO_of_component hp hp2 hf hk hφ2 hφ hJφ hJ hJm
  rw [MonoidHom.id_apply] at hφC
  rw [Subgroup.map_id] at hL
  set χ := conjAut 4 F C with hχ
  have hmem : MulAut.conj ζ ∈
      J'.map (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)) := ⟨ζ, hζ, rfl⟩
  rw [hL] at hmem
  obtain ⟨r, ⟨g, rfl⟩, hr⟩ := hmem
  change χ * conjAut 4 F (rowOHom δ ψ g) * χ⁻¹ = MulAut.conj ζ at hr
  have hζsq : ζ ^ 2 = 1 := by rw [← hζ2]; exact pow_orderOf_eq_one ζ
  have hr2 : conjAut 4 F (rowOHom δ ψ g) ^ 2 = 1 := by
    have h1 : (χ * conjAut 4 F (rowOHom δ ψ g) * χ⁻¹) ^ 2 = 1 := by
      rw [hr, ← map_pow, hζsq, map_one]
    rw [conj_pow] at h1
    calc conjAut 4 F (rowOHom δ ψ g) ^ 2
        = χ⁻¹ * (χ * conjAut 4 F (rowOHom δ ψ g) ^ 2 * χ⁻¹) * χ := by group
      _ = 1 := by rw [h1]; group
  have hr1 : conjAut 4 F (rowOHom δ ψ g) ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hr
    have hz : ζ = 1 := CSL.conj_injective (by rw [← hr, map_one])
    rw [hz, orderOf_one] at hζ2
    exact absurd hζ2 (by norm_num)
  have hg := mul_self_eq_neg_one_of_conjAut h2 hδ ψ hker g hr2 hr1
  obtain ⟨D, hD⟩ := exists_sl_conj hq h2 δ hδ ψ R hRT hRf hiso g hg
  have hβ := conj_beta_eq R (SpecialLinearGroup.toGL D) (rowOHom δ ψ g) hD
  rw [conjAut_toGL] at hβ
  refine ⟨χ (proj 4 F D), ?_⟩
  rw [← CSL.mul_conj_mul_inv, hφC, ← hr]
  calc (χ * MulAut.conj (proj 4 F D) * χ⁻¹)⁻¹ * (χ * (conjAut 4 F R⁻¹ * dualAut 4 F) * χ⁻¹) *
        (χ * MulAut.conj (proj 4 F D) * χ⁻¹)
      = χ * ((MulAut.conj (proj 4 F D))⁻¹ * (conjAut 4 F R⁻¹ * dualAut 4 F) *
          MulAut.conj (proj 4 F D)) * χ⁻¹ := by group
    _ = _ := by rw [hβ]; group

theorem outerInvCentL4 : OuterInvCentL4 := by
  intro F _ _ p f hp hp2 hf hF φ hφ2 hφ J' hJφ hJ hJm
  exact ⟨fun ψ' _ hψ _ => outer_cent_L4 F hp hp2 hf hF hφ2 hφ hJφ hJ hJm ψ' hψ,
    fun ζ hζ hζ2 => outer_fus_L4 F hp hp2 hf hF hφ2 hφ hJφ hJ hJm ζ hζ hζ2⟩

end OIL

end CFSG.ComponentClassification.CatFactsL4U4

module

public import CFSG.GH74.Generic.BProg.B3.S3OuterField
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3OuterGF

open CFSG CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag Matrix Subgroup
  S3OuterCore S3OuterField
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] noncomputable def Phi (σ : F ≃+* F) : SL(3, F) →* SL(3, F) :=
  (SpecialLinearGroup.map σ.toRingHom).comp (CatalogueBGraphForm.slGraphAut 3 F).toMonoidHom

theorem Phi_apply (σ : F ≃+* F) (g : SL(3, F)) :
    ((Phi σ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ).map σ := rfl

theorem fieldAut_dualAut_proj (σ : F ≃+* F) (g : SL(3, F)) :
    (fieldAut 3 F σ * dualAut 3 F) (LinearFlag.proj 3 F g) = LinearFlag.proj 3 F (Phi σ g) := by
  rw [MulAut.mul_apply, dualAut_proj, fieldAut_proj]
  rfl

theorem Phi_eq_iff (σ : F ≃+* F) (hσσ : ∀ a, σ (σ a) = a) (M : SL(3, F)) :
    Phi σ M = M ↔
      ((M : Matrix (Fin 3) (Fin 3) F).map σ)ᵀ * (M : Matrix (Fin 3) (Fin 3) F) = 1 := by
  set Mm : Matrix (Fin 3) (Fin 3) F := (M : Matrix (Fin 3) (Fin 3) F) with hMm
  set Mi : Matrix (Fin 3) (Fin 3) F := ((M⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) with hMi
  have hiM : Mi * Mm = 1 := by
    rw [hMm, hMi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hMi' : Mm * Mi = 1 := by
    rw [hMm, hMi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hmapmap : ∀ X : Matrix (Fin 3) (Fin 3) F, (X.map σ).map σ = X := by
    intro X
    ext i j
    simp [hσσ]
  constructor
  · intro h
    have h1 : (Miᵀ).map σ = Mm := by
      have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) h
      simpa [Phi_apply, hMi, hMm] using this
    have h2 : Miᵀ = Mm.map σ := by rw [← h1, hmapmap]
    have h3 : (Mm.map σ)ᵀ = Mi := by rw [← h2, Matrix.transpose_transpose]
    rw [h3, hiM]
  · intro h
    have h1 : (Mm.map σ)ᵀ = Mi := by
      calc (Mm.map σ)ᵀ = (Mm.map σ)ᵀ * (Mm * Mi) := by rw [hMi', Matrix.mul_one]
        _ = ((Mm.map σ)ᵀ * Mm) * Mi := (Matrix.mul_assoc _ _ _).symm
        _ = Mi := by rw [h, Matrix.one_mul]
    have h2 : Miᵀ = Mm.map σ := by rw [← h1, Matrix.transpose_transpose]
    apply Subtype.ext
    change ((Phi σ M : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = Mm
    rw [Phi_apply, h2, hmapmap]

theorem Phi_eq_of (σ : F ≃+* F) (hσσ : ∀ a, σ (σ a) = a) (k T : SL(3, F)) (hTT : T * T = 1)
    (hTt : (T : Matrix (Fin 3) (Fin 3) F)ᵀ = T) (hTσ : (T : Matrix (Fin 3) (Fin 3) F).map σ = T)
    (hk : (k : Matrix (Fin 3) (Fin 3) F) * ((k : Matrix (Fin 3) (Fin 3) F).map σ)ᵀ = T) :
    Phi σ k = T * k := by
  set K : Matrix (Fin 3) (Fin 3) F := (k : Matrix (Fin 3) (Fin 3) F) with hK
  set Mi : Matrix (Fin 3) (Fin 3) F := ((k⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) with hMi
  set Tm : Matrix (Fin 3) (Fin 3) F := (T : Matrix (Fin 3) (Fin 3) F) with hTm
  have hiK : Mi * K = 1 := by
    rw [hK, hMi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hTT' : Tm * Tm = 1 := by
    have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) hTT
    simpa [hTm] using this
  have hmapmap : ∀ X : Matrix (Fin 3) (Fin 3) F, (X.map σ).map σ = X := by
    intro X
    ext i j
    simp [hσσ]
  have h1 : (K.map σ)ᵀ = Mi * Tm := by
    calc (K.map σ)ᵀ = Mi * (K * (K.map σ)ᵀ) := by rw [← Matrix.mul_assoc, hiK, Matrix.one_mul]
      _ = Mi * Tm := by rw [hk]
  have h2 : K.map σ = Tm * Miᵀ := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_transpose, Matrix.transpose_mul, hTt] at this
    exact this
  have h3 : K = Tm * (Miᵀ).map σ := by
    have := congrArg (fun X : Matrix (Fin 3) (Fin 3) F => X.map σ) h2
    simp only [hmapmap] at this
    rw [this, Matrix.map_mul, hTσ]
  apply Subtype.ext
  change ((Phi σ k : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = Tm * K
  rw [Phi_apply]
  calc (Miᵀ).map σ = (Tm * Tm) * (Miᵀ).map σ := by rw [hTT', Matrix.one_mul]
    _ = Tm * (Tm * (Miᵀ).map σ) := Matrix.mul_assoc _ _ _
    _ = Tm * K := by rw [← h3]

theorem outerCore_graphField {p f : ℕ} (hud : UnitaryFieldData p f F) (hp2 : p ≠ 2) {σ : F ≃+* F}
    (hσ : ∀ a, σ a = hud.bar a) : OuterCore (fieldAut 3 F σ * dualAut 3 F) := by
  classical
  have : Finite F := hud.finite
  have : Fact p.Prime := ⟨hud.prime⟩
  have hσσ : ∀ a, σ (σ a) = a := fun a => by rw [hσ, hσ, hud.bar_bar]
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hc := hud.charP
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 (by exact_mod_cast h)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
    · exact hud.prime.one_lt.ne' h1
    · exact hp2 h1
  have hp3 : 3 ≤ p := by
    have := hud.prime.two_le
    omega
  have hpf : 3 ≤ p ^ f := le_trans hp3 (Nat.le_self_pow (by have := hud.one_le; omega) p)
  have hqU : IsQuasisimple (unitarySU p f F 3) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hud.card_eq_sq (le_refl 3)
      (by intro h; have := congrArg Prod.snd h; simp at this; omega)).1
  set R : Subgroup SL(3, F) := (unitarySU p f F 3).comap SpecialLinearGroup.toGL with hR
  have hRmem : ∀ M : SL(3, F), M ∈ R ↔ Phi σ M = M := by
    intro M
    rw [Phi_eq_iff σ hσσ]
    change SpecialLinearGroup.toGL M ∈ unitarySU p f F 3 ↔ _
    rw [mem_unitarySU_iff hud]
    have hbar : (⇑hud.bar : F → F) = ⇑σ := funext fun a => (hσ a).symm
    constructor
    · rintro ⟨-, h⟩
      simpa [hbar] using h
    · intro h
      refine ⟨by simp, ?_⟩
      simpa [hbar] using h
  have hmap : R.map SpecialLinearGroup.toGL = unitarySU p f F 3 := by
    rw [hR, Subgroup.map_comap_eq]
    refine inf_eq_right.2 fun A hA => ?_
    have hdet := ((mem_unitarySU_iff hud).1 hA).1
    exact ⟨⟨(A : Matrix (Fin 3) (Fin 3) F), hdet⟩, Units.ext rfl⟩
  have hqR : IsQuasisimple ↥R :=
    LocalCores.isQuasisimple_of_mulEquiv
      ((R.equivMapOfInjective _ SpecialLinearGroup.toGL_injective).trans
        (MulEquiv.subgroupCongr hmap)).symm hqU
  have hd0R : d0 F ∈ R := by
    rw [hRmem, Phi_eq_iff σ hσσ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  have hb1R : b1 F ∈ R := by
    rw [hRmem, Phi_eq_iff σ hσσ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  refine ⟨R.map (LinearFlag.proj 3 F),
    LocalCores.isQuasisimple_map hqR (LinearFlag.proj 3 F) ?_, ?_, ?_, ?_,
    LinearFlag.proj 3 F (d0 F), ⟨d0 F, hd0R, rfl⟩, ?_, ?_, ?_⟩
  · intro hle
    exact d0_not_mem_scalars h2 (by simpa using hle hd0R)
  · exact two_le_pRank_of_b1_d0 h2 ⟨b1 F, hb1R, rfl⟩ ⟨d0 F, hd0R, rfl⟩
  · rintro _ ⟨M, hM, rfl⟩
    rw [fieldAut_dualAut_proj]
    congr 1
    exact (hRmem M).1 hM
  · intro x hx
    obtain ⟨xt, rfl⟩ := LinearFlag.proj_surjective 3 F x
    rw [fieldAut_dualAut_proj] at hx
    have hz := LinearFlag.proj_eq_proj_iff.1 hx
    set z : SL(3, F) := (Phi σ xt)⁻¹ * xt with hzdef
    have hzc : ∀ M : SL(3, F), M * z = z * M := fun M =>
      mem_center_iff.1 (LinearFlag.scalars_le_center 3 F hz) M
    have hxσ : Phi σ xt = xt * z⁻¹ := by
      rw [hzdef]
      group
    rintro _ ⟨M, hM, rfl⟩
    have hM' : M ∈ R := hM
    refine ⟨xt * M * xt⁻¹, SetLike.mem_coe.2 ?_, by simp⟩
    rw [hRmem, map_mul, map_mul, map_inv, hxσ, (hRmem M).1 hM']
    have hzc' : ∀ M : SL(3, F), M * z⁻¹ = z⁻¹ * M := fun M => by
      have := hzc M
      calc M * z⁻¹ = z⁻¹ * (z * M) * z⁻¹ := by group
        _ = z⁻¹ * (M * z) * z⁻¹ := by rw [this]
        _ = z⁻¹ * M := by group
    calc xt * z⁻¹ * M * (xt * z⁻¹)⁻¹ = xt * (z⁻¹ * M * z) * xt⁻¹ := by group
      _ = xt * M * xt⁻¹ := by rw [← hzc' M]; group
  · rw [← map_mul, d0_mul_self, map_one]
  · intro h
    exact d0_not_mem_scalars h2 (LinearFlag.proj_eq_one_iff.1 h)
  ·
    obtain ⟨ζ, hζ⟩ : ∃ ζ : F, hud.norm ζ = -1 := by
      obtain ⟨c, hc⟩ := hud.normHom_surjective ⟨-1, by simp⟩
      exact ⟨c, by simpa using congrArg Subtype.val hc⟩
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      simp [UnitaryFieldData.norm] at hζ
    have hN : ζ * σ ζ = -1 := by rw [hσ]; exact hζ
    have hσζ0 : σ ζ ≠ 0 := by rwa [Ne, map_eq_zero_iff σ σ.injective]
    refine ⟨LinearFlag.proj 3 F (kz ζ hζ0), ?_⟩
    have hk : Phi σ (kz ζ hζ0) = d0 F * kz ζ hζ0 := by
      refine Phi_eq_of σ hσσ _ _ d0_mul_self ?_ ?_ ?_
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
      · ext i j
        fin_cases i <;> fin_cases j <;> simp
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
        all_goals first
          | exact hN
          | (rw [show ζ⁻¹ * ζ⁻¹ * ((σ ζ)⁻¹ * (σ ζ)⁻¹) = ((ζ * σ ζ)⁻¹) ^ 2 by rw [mul_inv]; ring, hN]
             norm_num)
    rw [fieldAut_dualAut_proj, hk, map_mul, mul_inv_cancel_right]

end S3OuterGF

end CFSG.GH74.Generic.BProg.B3

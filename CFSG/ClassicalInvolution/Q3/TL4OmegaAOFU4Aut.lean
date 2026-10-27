module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFU4G
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFBase
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSpLevi
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Top

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.U4

open Matrix CFSG CFSG.Blueprint CFSG.ClassicalInvolution.Q3.Q3MFOU4
  CFSG.ClassicalInvolution.Q3.Q3PP CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups

section Statements

@[expose] def PSUDiagStatement : Prop :=
  ∀ (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4))) (α : Su F9 3 1 4 →* Su F9 3 1 4),
    ρ * ρ = 1 → (∀ x : Su F9 3 1 4, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x)) →
    α.comp α = MonoidHom.id _ → ∀ {G Gi : Matrix (Fin 4) (Fin 4) F9}, Gi * G = 1 →
    (∀ x, suMat (α x) = G * suMat x * Gi) → (G.map σ9)ᵀ * G = 1 →
    ∀ c : F9, G * G = c • (1 : Matrix (Fin 4) (Fin 4) F9) → c * c = -1 →
    oddCoreIn (fixedSubgroup ρ) = ⊥

@[expose] def PSUOrthStatement : Prop :=
  ∀ (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4))) (α : Su F9 3 1 4 →* Su F9 3 1 4),
    ρ * ρ = 1 → (∀ x : Su F9 3 1 4, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x)) →
    α.comp α = MonoidHom.id _ → ∀ {G Gi : Matrix (Fin 4) (Fin 4) F9}, Gi * G = 1 →
    (∀ x, suMat (α x) = G * σ9.mapMatrix (suMat x) * Gi) → (G.map σ9)ᵀ * G = 1 →
    G * G.map σ9 = 1 → oddCoreIn (fixedSubgroup ρ) = ⊥

end Statements

section Scalars

variable {G Gi : Matrix (Fin 4) (Fin 4) F9} {c : F9}

theorem norm_of_sq (hgu : (G.map σ9)ᵀ * G = 1)
    (hc : G * G = c • (1 : Matrix (Fin 4) (Fin 4) F9)) : σ9 c * c = 1 := by
  have h1 : (G.map σ9)ᵀ * (G.map σ9)ᵀ * (G * G) = 1 := by
    calc (G.map σ9)ᵀ * (G.map σ9)ᵀ * (G * G) = (G.map σ9)ᵀ * ((G.map σ9)ᵀ * G) * G := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hgu, Matrix.mul_one, hgu]
  have h2 : (G.map σ9)ᵀ * (G.map σ9)ᵀ = σ9 c • (1 : Matrix (Fin 4) (Fin 4) F9) := by
    have h := congrArg (fun M => (M.map σ9)ᵀ) hc
    simp only [Matrix.map_mul, map_smul_σ9, Matrix.map_one _ (map_zero σ9) (map_one σ9),
      Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_one] at h
    exact h
  rw [h2, hc, Matrix.smul_mul, Matrix.one_mul, smul_smul] at h1
  have h3 := congrFun (congrFun h1 0) 0
  simpa using h3

theorem fixed_of_sq_bar (hGiG : Gi * G = 1)
    (hc : G * G.map σ9 = c • (1 : Matrix (Fin 4) (Fin 4) F9)) : σ9 c = c := by
  have h1 : G.map σ9 * G = σ9 c • (1 : Matrix (Fin 4) (Fin 4) F9) := by
    have h := congrArg (fun M => M.map σ9) hc
    simp only [Matrix.map_mul, map_map_σ9, map_smul_σ9,
      Matrix.map_one _ (map_zero σ9) (map_one σ9)] at h
    exact h
  have h2 : σ9 c • G = c • G := by
    calc σ9 c • G = G * (G.map σ9 * G) := by rw [h1, Matrix.mul_smul, Matrix.mul_one]
      _ = G * G.map σ9 * G := by rw [Matrix.mul_assoc]
      _ = c • G := by rw [hc, Matrix.smul_mul, Matrix.one_mul]
  have h3 : σ9 c • (1 : Matrix (Fin 4) (Fin 4) F9) = c • 1 := by
    have h := congrArg (fun M => Gi * M) h2
    simp only [Matrix.mul_smul, hGiG] at h
    exact h
  have h4 := congrFun (congrFun h3 0) 0
  simpa using h4

theorem alt_of_sq_bar (hgu : (G.map σ9)ᵀ * G = 1)
    (hc : G * G.map σ9 = (-1 : F9) • (1 : Matrix (Fin 4) (Fin 4) F9)) : Gᵀ = -G := by
  have hU : G.map σ9 = -(G.map σ9)ᵀ := by
    have h1 : (G.map σ9)ᵀ * (G * G.map σ9) =
        (G.map σ9)ᵀ * ((-1 : F9) • (1 : Matrix (Fin 4) (Fin 4) F9)) := by rw [hc]
    rw [← Matrix.mul_assoc, hgu, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
      neg_one_smul] at h1
    exact h1
  ext i j
  have h := congrFun (congrFun hU j) i
  simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply] at h
  have h' := congrArg σ9 h
  rw [σ9_σ9, map_neg, σ9_σ9] at h'
  rw [Matrix.transpose_apply, Matrix.neg_apply]
  exact h'

theorem sq_bar_ne_zero (hGiG : Gi * G = 1) (hgu : (G.map σ9)ᵀ * G = 1)
    (hc : G * G.map σ9 = c • (1 : Matrix (Fin 4) (Fin 4) F9)) : c ≠ 0 := by
  intro h0
  have h1 : G.map σ9 = 0 := by
    have h := congrArg (fun M => Gi * M) hc
    simp only [h0, zero_smul, Matrix.mul_zero, ← Matrix.mul_assoc, hGiG, Matrix.one_mul] at h
    exact h
  rw [h1, Matrix.transpose_zero, Matrix.zero_mul] at hgu
  have h2 := congrFun (congrFun hgu 0) 0
  simp at h2

end Scalars

section Cases

theorem oddCoreIn_fixed_conj_of_sq (hq : CFSG.Open.IsQuasisimple (Su F9 3 1 4))
    (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4))) (α : Su F9 3 1 4 →* Su F9 3 1 4)
    (hρmk : ∀ x : Su F9 3 1 4, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x))
    {G Gi : Matrix (Fin 4) (Fin 4) F9} (hGiG : Gi * G = 1)
    (hα : ∀ x, suMat (α x) = G * suMat x * Gi) (hgu : (G.map σ9)ᵀ * G = 1) {a c : F9}
    (hc : G * G = c • (1 : Matrix (Fin 4) (Fin 4) F9)) (hac : a * a * c = 1)
    (hNa : σ9 a * a = 1) : oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  classical
  have hZ := isPGroup_center_su4
  have hc0 : c ≠ 0 := fun h => by rw [h, mul_zero] at hac; exact zero_ne_one hac
  have hGi : Gi = c⁻¹ • G := Q3MFOU4.inv_eq_smul_of_sq hGiG hc0 hc
  have haa : a * a = c⁻¹ := eq_inv_of_mul_eq_one_left hac
  have hDD' : (a • G) * (a • G) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, smul_smul, hac, one_smul]
  obtain ⟨Dg, hDgc⟩ : ∃ Dg : GL (Fin 4) F9, (Dg : Matrix (Fin 4) (Fin 4) F9) = a • G :=
    ⟨⟨a • G, a • G, hDD', hDD'⟩, rfl⟩
  have hDD : Dg * Dg = 1 := Units.ext (by rw [Units.val_mul, hDgc, hDD', Units.val_one])
  have hDg : cT σ9 (Dg : Matrix (Fin 4) (Fin 4) F9) * 1 * (Dg : Matrix (Fin 4) (Fin 4) F9) = 1 := by
    rw [hDgc, Matrix.mul_one, cT, map_smul_σ9, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hgu, hNa, one_smul]
  have hαconj : ∀ x : Su F9 3 1 4,
      α x = conjAut (SUid σ9 4) Dg (mem_normalizer_SUid hDg) x := by
    intro x
    apply suMat_injective
    show suMat (α x) =
      ((Dg * (x : GL (Fin 4) F9) * Dg⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)
    rw [hα x, Units.val_mul, Units.val_mul, inv_eq_of_mul_eq_one_right hDD, hDgc, hGi, ← haa]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rfl
  have hρeq : ρ = autToCentralQuotient (SUid σ9 4)
      (conjAut (SUid σ9 4) Dg (mem_normalizer_SUid hDg)) := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [autToCentralQuotient_mk, hρmk, hαconj]
  by_cases hone : conjAut (SUid σ9 4) Dg (mem_normalizer_SUid hDg) = 1
  · have hρ1 : ρ = 1 := by rw [hρeq, hone, map_one]
    have hTop : oddCoreIn (⊤ : Subgroup (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4))) = ⊥ := by
      have h := oddCoreIn_range_eq_bot_of_isQuasisimple
        (QuotientGroup.mk' (Subgroup.center (Su F9 3 1 4))) hq hZ
        (by rw [QuotientGroup.ker_mk'])
      rwa [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    have hfx : fixedSubgroup (1 : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4))) = ⊤ := by
      ext x
      simp [mem_fixedSubgroup_iff]
    rw [hρ1, hfx]
    exact hTop
  · rw [hρeq]
    exact oddCoreIn_fixed_conjSUid_eq_bot card_F9 hZ Dg hDD hDg hone

theorem oddCoreIn_fixed_su4_of (hUa : PSUDiagStatement) (hUc : PSUOrthStatement)
    (hq : CFSG.Open.IsQuasisimple (Su F9 3 1 4)) (hSp : CFSG.Open.IsQuasisimple (StatedSp 2 F3))
    (hSpZ : IsPGroup 2 (Subgroup.center (StatedSp 2 F3)))
    (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4))) (hρ2 : ρ * ρ = 1) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  classical
  have hρ2' : ∀ x, ρ (ρ x) = x := fun x => by
    have := congrArg (fun f : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)) => f x) hρ2
    simpa using this
  obtain ⟨α, g, φ, hθ, hα, hgu, hφ⟩ := su4_lift
    (QuotientGroup.mk' (Subgroup.center (Su F9 3 1 4))) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) ρ
  obtain ⟨hφ', hαα⟩ := hφ hρ2'
  have hρmk : ∀ x : Su F9 3 1 4, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
    fun x => (hθ x).symm
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin 4) (Fin 4) F9, G = (g : Matrix (Fin 4) (Fin 4) F9) :=
    ⟨_, rfl⟩
  obtain ⟨Gi, hGi⟩ : ∃ Gi : Matrix (Fin 4) (Fin 4) F9,
      Gi = ((g⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) := ⟨_, rfl⟩
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hα' : ∀ x, suMat (α x) = G * φ.mapMatrix (suMat x) * Gi := fun x => by
    rw [hG, hGi]
    exact hα x
  have hgu' : (G.map σ9)ᵀ * G = 1 := by
    rw [hG]
    exact hgu
  rcases hφ' with rfl | rfl
  ·
    have hα1 : ∀ x, suMat (α x) = G * suMat x * Gi := fun x => by
      rw [hα', ModelFacts.Orth15.OuterU4.mapMatrix_refl_four]
    obtain ⟨c, hc⟩ := sq_scalar α hαα (RingEquiv.refl F9) (fun c => rfl) hGiG hα'
    rw [ModelFacts.Orth15.OuterU4.mapMatrix_refl_four] at hc
    have hNc := norm_of_sq hgu' hc
    rw [σ9_apply] at hNc
    have hc4 : (c * c - 1) * (c * c + 1) = 0 := by linear_combination hNc
    rcases mul_eq_zero.mp hc4 with h | h
    · have h' : (c - 1) * (c + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h1 | h1
      ·
        have hc1 : c = 1 := sub_eq_zero.mp h1
        exact oddCoreIn_fixed_conj_of_sq hq ρ α hρmk hGiG hα1 hgu' (a := 1) hc
          (by rw [hc1]; ring) (by rw [map_one, one_mul])
      ·
        have hc1 : c = -1 := eq_neg_of_add_eq_zero_left h1
        obtain ⟨ι, hι, hιb⟩ := exists_iota
        exact oddCoreIn_fixed_conj_of_sq hq ρ α hρmk hGiG hα1 hgu' (a := ι) hc
          (by rw [hc1, hι]; ring) (iota_norm hι hιb)
    ·
      exact hUa ρ α hρ2 hρmk hαα hGiG hα1 hgu' c hc (eq_neg_of_add_eq_zero_left h)
  ·
    obtain ⟨c, hc⟩ := sq_scalar α hαα σ9 σ9_σ9 hGiG hα'
    rw [RingEquiv.mapMatrix_apply] at hc
    rcases eq_of_σ9_fixed (fixed_of_sq_bar hGiG hc) with h0 | h1 | h1
    · exact absurd h0 (sq_bar_ne_zero hGiG hgu' hc)
    ·
      exact hUc ρ α hρ2 hρmk hαα hGiG hα' hgu' (by rw [hc, h1, one_smul])
    ·
      exact oddCoreIn_fixed_bar_alt hSp hSpZ ρ α hρmk hGiG hα' hgu'
        (alt_of_sq_bar hgu' (by rw [hc, h1]))

end Cases

section Model

open CFSG.ClassicalInvolution.Generic


theorem fixedOddFree_su4_of (hUa : PSUDiagStatement) (hUc : PSUOrthStatement) :
    FixedOddFree (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)) := by
  intro ρ hρ2
  have hadmSp : StatedLieAdmissible .PSp 2 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hSp : CFSG.Open.IsQuasisimple (StatedSp 2 (GaloisField 3 1)) :=
    (ModelFacts.modelClauseZero .PSp 2 3 1 Nat.prime_three trivial hadmSp).1
  have hF : Nat.card (GaloisField 3 1) = 3 := by simpa using GaloisField.card 3 1 one_ne_zero
  have hSpZ := SpL.isPGroup_center_statedSp (n := 2) hF
  have hq : CFSG.Open.IsQuasisimple (Su F9 3 1 4) :=
    open_isQuasisimple_su_of_three_le card_F9 (by norm_num) (by decide)
  exact oddCoreIn_fixed_su4_of hUa hUc hq hSp hSpZ ρ hρ2

theorem outerFixedOddFree_psu4_of (hUa : PSUDiagStatement) (hUc : PSUOrthStatement) :
    OuterFixedOddFree .PSU 4 := by
  intro S _ _ _ hS σ hσ _
  have hFT : IsFundTag StatedLieTag.PSU := trivial
  have hadm : StatedLieAdmissible .PSU 4 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover _ 4 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have : Group.IsPerfect (modelUniv .PSU 4 3 1 Nat.prime_three).K :=
    ⟨((ModelFacts.modelClauseZero .PSU 4 3 1 Nat.prime_three hFT hadm).1).1⟩
  obtain ⟨e₀, -⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  let E : (modelUniv .PSU 4 3 1 Nat.prime_three).K ⧸
      Subgroup.center (modelUniv .PSU 4 3 1 Nat.prime_three).K ≃*
      Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4) :=
    QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  let e : S ≃* Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4) :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (Q3NM.centralQuotientIso ψ hψ hker).symm).trans E
  have hρ2 : MulAut.congr e σ * MulAut.congr e σ = 1 := by rw [← map_mul, hσ, map_one]
  have h1 := Q3NM.oddCoreIn_fixed_congr_eq_bot' e.symm (MulAut.congr e σ)
    (fixedOddFree_su4_of hUa hUc _ hρ2)
  have h2 : MulAut.congr e.symm (MulAut.congr e σ) = σ := by
    ext x
    simp [MulAut.congr_apply]
  rwa [h2] at h1

end Model

end CFSG.ClassicalInvolution.Q3.TL4.U4

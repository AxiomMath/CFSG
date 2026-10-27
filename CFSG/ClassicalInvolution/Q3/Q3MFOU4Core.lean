module

public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Lift
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Shape
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Diag
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Graph
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOU4

open Matrix CFSG.ClassicalInvolution.Q3.Q3PP CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Helpers

theorem scalar_of_commute_su4 (B : Matrix (Fin 4) (Fin 4) F9)
    (hB : ∀ x : Su F9 3 1 4, B * suMat x = suMat x * B) :
    ∃ a : F9, B = a • (1 : Matrix (Fin 4) (Fin 4) F9) := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 F9 :=
    ⟨Fact.out, le_rfl, by rw [card_F9, ← pow_mul, mul_comm]⟩
  refine CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.eq_smul_one_of_commute h (by norm_num)
    (by norm_num : 3 ≤ 4) B fun y hy => ?_
  have hy' : y ∈ SUid σ9 4 := by
    rw [SUid_eq_statedSU card_F9]
    exact hy
  exact hB ⟨y, hy'⟩

theorem trace_conj_map (φ : F9 ≃+* F9) {G Gi : Matrix (Fin 4) (Fin 4) F9} (hGiG : Gi * G = 1)
    (Y : Matrix (Fin 4) (Fin 4) F9) :
    Matrix.trace (G * φ.mapMatrix Y * Gi) = φ (Matrix.trace Y) := by
  rw [Matrix.trace_mul_cycle, hGiG, Matrix.one_mul]
  simp [Matrix.trace, RingEquiv.mapMatrix_apply, map_sum]

theorem eq_of_trace_two (α : Su F9 3 1 4 →* Su F9 3 1 4) (φ : F9 ≃+* F9)
    {G Gi : Matrix (Fin 4) (Fin 4) F9} (hGiG : Gi * G = 1)
    (hα : ∀ x, suMat (α x) = G * φ.mapMatrix (suMat x) * Gi) {r : Su F9 3 1 4}
    (hr : (α r)⁻¹ * r ∈ Subgroup.center (Su F9 3 1 4))
    (htr : Matrix.trace (suMat r) = 2) : α r = r := by
  obtain ⟨u, hu0, hu⟩ := scalar_of_mem_center hr
  have h1 : suMat r = u • suMat (α r) := by
    have : suMat r = suMat (α r) * suMat ((α r)⁻¹ * r) := by
      rw [← suMat_mul, mul_inv_cancel_left]
    rw [this, hu, Matrix.mul_smul, Matrix.mul_one]
  have h2 : Matrix.trace (suMat (α r)) = 2 := by
    rw [hα, trace_conj_map φ hGiG, htr]
    exact map_ofNat φ 2
  have h3 : (2 : F9) = u * 2 := by
    have := congrArg Matrix.trace h1
    rwa [htr, Matrix.trace_smul, h2, smul_eq_mul] at this
  have hu1 : u = 1 := by
    apply mul_right_cancel₀ two_ne_zero_F9
    rw [one_mul]
    exact h3.symm
  rw [hu1, one_smul] at h1
  exact suMat_injective h1.symm

theorem key_rel (α : Su F9 3 1 4 →* Su F9 3 1 4) (φ : F9 ≃+* F9)
    {G Gi : Matrix (Fin 4) (Fin 4) F9} (hGiG : Gi * G = 1)
    (hα : ∀ x, suMat (α x) = G * φ.mapMatrix (suMat x) * Gi) {r : Su F9 3 1 4} (hr : α r = r)
    {R R' : Matrix (Fin 4) (Fin 4) F9} (hR : suMat r = R) (hR' : φ.mapMatrix R = R') :
    G * R' = R * G := by
  subst hR hR'
  have h := hα r
  rw [hr] at h
  calc G * φ.mapMatrix (suMat r) = G * φ.mapMatrix (suMat r) * (Gi * G) := by
        rw [hGiG, Matrix.mul_one]
    _ = (G * φ.mapMatrix (suMat r) * Gi) * G := by simp only [Matrix.mul_assoc]
    _ = suMat r * G := by rw [← h]

theorem sq_scalar (α : Su F9 3 1 4 →* Su F9 3 1 4) (hαα : α.comp α = MonoidHom.id _)
    (φ : F9 ≃+* F9) (hφφ : ∀ c, φ (φ c) = c) {G Gi : Matrix (Fin 4) (Fin 4) F9}
    (hGiG : Gi * G = 1)
    (hα : ∀ x, suMat (α x) = G * φ.mapMatrix (suMat x) * Gi) :
    ∃ c : F9, G * φ.mapMatrix G = c • (1 : Matrix (Fin 4) (Fin 4) F9) := by
  refine scalar_of_commute_su4 _ fun x => ?_
  have hx : suMat (α (α x)) = suMat x := by
    have := DFunLike.congr_fun hαα x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at this
    rw [this]
  rw [hα (α x), hα x, alpha_sq_matrix φ hφφ] at hx
  have hP := inv_sq_matrix φ G Gi hGiG
  have key : ∀ (P Pi X : Matrix (Fin 4) (Fin 4) F9), P * X * Pi = X → Pi * P = 1 →
      P * X = X * P := by
    intro P Pi X h1 h2
    calc P * X = P * X * (Pi * P) := by rw [h2, Matrix.mul_one]
      _ = (P * X * Pi) * P := by simp only [Matrix.mul_assoc]
      _ = X * P := by rw [h1]
  exact key _ _ _ hx hP

theorem inv_eq_smul_of_sq {G Gi : Matrix (Fin 4) (Fin 4) F9} (hGiG : Gi * G = 1) {s : F9}
    (hs : s ≠ 0) (h : G * G = s • (1 : Matrix (Fin 4) (Fin 4) F9)) : Gi = s⁻¹ • G := by
  have h1 : G = s • Gi := by
    calc G = (Gi * G) * G := by rw [hGiG, Matrix.one_mul]
      _ = Gi * (G * G) := by rw [Matrix.mul_assoc]
      _ = s • Gi := by rw [h, Matrix.mul_smul, Matrix.mul_one]
  rw [h1, smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem map_smul_σ9 (c : F9) (X : Matrix (Fin 4) (Fin 4) F9) :
    (c • X).map σ9 = σ9 c • X.map σ9 := Matrix.map_smul' _ _ _ (map_mul σ9)

end Helpers

section CaseId

theorem su4_case_id (hq : CFSG.Open.IsQuasisimple (Su F9 3 1 4))
    (hZ : IsPGroup 2 (Subgroup.center (Su F9 3 1 4)))
    (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4))) (α : Su F9 3 1 4 →* Su F9 3 1 4)
    (hρmk : ∀ x : Su F9 3 1 4, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x))
    (hαα : α.comp α = MonoidHom.id _) {G Gi : Matrix (Fin 4) (Fin 4) F9} (hGiG : Gi * G = 1)
    (hα : ∀ x, suMat (α x) = G * (RingEquiv.refl F9).mapMatrix (suMat x) * Gi)
    (hdet : G.det ≠ 0) (hgu : (G.map σ9)ᵀ * G = 1)
    (g01 : G 0 1 = 0) (g02 : G 0 2 = 0) (g03 : G 0 3 = 0) (g10 : G 1 0 = 0) (g20 : G 2 0 = 0)
    (g30 : G 3 0 = 0) (ha : G 0 0 ≠ 0) : oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  classical
  obtain ⟨c, hc⟩ := sq_scalar α hαα (RingEquiv.refl F9) (fun c => rfl) hGiG hα
  rw [mapMatrix_refl_four] at hc
  obtain ⟨a, hadef⟩ : ∃ a : F9, a = G 0 0 := ⟨_, rfl⟩
  rw [← hadef] at ha
  have hcc : c = a * a := by
    have h := congrFun (congrFun hc 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_four, g01, g02, g03] at h
    rw [hadef]
    exact h.symm
  have hN : σ9 a * a = 1 := by
    have h := congrFun (congrFun hgu 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.map_apply, g10,
      g20, g30] at h
    rw [hadef]
    exact h
  have hDdet : (a⁻¹ • G).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ha)) hdet
  obtain ⟨Dg, hDgc⟩ : ∃ Dg : GL (Fin 4) F9, (Dg : Matrix (Fin 4) (Fin 4) F9) = a⁻¹ • G :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hDdet, rfl⟩
  have hDD : Dg * Dg = 1 := by
    apply Units.ext
    rw [Units.val_mul, hDgc, Units.val_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, hcc,
      smul_smul]
    have : a⁻¹ * a⁻¹ * (a * a) = 1 := by field_simp
    rw [this, one_smul]
  have hDg : cT σ9 (Dg : Matrix (Fin 4) (Fin 4) F9) * 1 * (Dg : Matrix (Fin 4) (Fin 4) F9) = 1 := by
    have hn1 : σ9 a⁻¹ * a⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hN, inv_one]
    rw [hDgc, Matrix.mul_one, cT, map_smul_σ9, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hgu, hn1, one_smul]
  have hGi : Gi = (a * a)⁻¹ • G := by
    have h := inv_eq_smul_of_sq hGiG (s := c) (by rw [hcc]; exact mul_ne_zero ha ha) hc
    rw [h, hcc]
  have hαconj : ∀ x : Su F9 3 1 4,
      α x = conjAut (SUid σ9 4) Dg (mem_normalizer_SUid hDg) x := by
    intro x
    apply suMat_injective
    show suMat (α x) =
      ((Dg * (x : GL (Fin 4) F9) * Dg⁻¹ : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)
    rw [hα x, Units.val_mul, Units.val_mul, inv_eq_of_mul_eq_one_right hDD, hDgc,
      mapMatrix_refl_four, hGi]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv]
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

end CaseId

section CaseBar

theorem su4_case_bar (hSp : CFSG.Open.IsQuasisimple (StatedSp 2 F3))
    (hSpZ : IsPGroup 2 (Subgroup.center (StatedSp 2 F3)))
    (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4))) (α : Su F9 3 1 4 →* Su F9 3 1 4)
    (hρmk : ∀ x : Su F9 3 1 4, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x))
    (hαα : α.comp α = MonoidHom.id _) {G Gi : Matrix (Fin 4) (Fin 4) F9} (hGiG : Gi * G = 1)
    (hα : ∀ x, suMat (α x) = G * σ9.mapMatrix (suMat x) * Gi)
    (hgu : (G.map σ9)ᵀ * G = 1)
    (g00 : G 0 0 = 0) (g11 : G 1 1 = 0) (g10 : G 1 0 = -G 0 1) (g02 : G 0 2 = 0)
    (g03 : G 0 3 = 0) (g12 : G 1 2 = 0) (g13 : G 1 3 = 0) (g20 : G 2 0 = 0) (g21 : G 2 1 = 0)
    (g30 : G 3 0 = 0) (g31 : G 3 1 = 0) : oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  classical
  obtain ⟨c, hc⟩ := sq_scalar α hαα σ9 σ9_σ9 hGiG hα
  rw [RingEquiv.mapMatrix_apply] at hc
  have hm : σ9 (G 0 1) * G 0 1 = 1 := by
    have h := congrFun (congrFun hgu 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.map_apply, g11,
      g21, g31] at h
    exact h
  have hcc : c = -1 := by
    have h := congrFun (congrFun hc 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [g00, g02, g03, g10, g20, g30, map_zero, map_neg] at h
    linear_combination -h - hm
  have hsq : G * G.map σ9 = (-1 : F9) • (1 : Matrix (Fin 4) (Fin 4) F9) := by rw [hc, hcc]
  have hU : G.map σ9 = -(G.map σ9)ᵀ := by
    have h1 : (G.map σ9)ᵀ * (G * G.map σ9) =
        (G.map σ9)ᵀ * ((-1 : F9) • (1 : Matrix (Fin 4) (Fin 4) F9)) := by rw [hsq]
    rw [← Matrix.mul_assoc, hgu, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
      neg_one_smul] at h1
    exact h1
  have halt : ∀ i j, G i j = -G j i := by
    intro i j
    have h := congrFun (congrFun hU i) j
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply] at h
    have h' := congrArg σ9 h
    rwa [σ9_σ9, map_neg, σ9_σ9] at h'
  have hdiag : ∀ i, G i i = 0 := fun i => by
    have h : (2 : F9) * G i i = 0 := by linear_combination halt i i
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero_F9
  have g22 : G 2 2 = 0 := hdiag 2
  have g33 : G 3 3 = 0 := hdiag 3
  have g32 : G 3 2 = -G 2 3 := halt 3 2
  have hn : σ9 (G 2 3) * G 2 3 = 1 := by
    have h := congrFun (congrFun hgu 3) 3
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.map_apply, g03,
      g13, g33] at h
    exact h
  obtain ⟨ι, hι, hιb⟩ := exists_iota
  obtain ⟨ζ, hζ⟩ := exists_zeta
  obtain ⟨D, hD⟩ : ∃ D : GraphData, D = ⟨ι, ζ, G 0 1, G 2 3, hι, hιb, hζ, hm, hn⟩ := ⟨_, rfl⟩
  have hDG : D.G = G := by
    ext i j
    subst hD
    fin_cases i <;> fin_cases j <;>
      simp [GraphData.G, Gmat, g00, g11, g22, g33, g10, g32, g02, g03, g12, g13, g20, g21, g30,
        g31]
  have hαG : ∀ x, suMat (α x) * D.G = D.G * (suMat x).map σ9 := by
    intro x
    rw [hDG, hα x, RingEquiv.mapMatrix_apply]
    calc G * (suMat x).map σ9 * Gi * G = G * (suMat x).map σ9 * (Gi * G) := by
          simp only [Matrix.mul_assoc]
      _ = G * (suMat x).map σ9 := by rw [hGiG, Matrix.mul_one]
  exact oddCoreIn_fixed_graph_su4 D hSp hSpZ α hαG ρ hρmk

end CaseBar

section Main

theorem iota_norm {ι : F9} (hι : ι * ι = -1) (hιb : σ9 ι = -ι) : σ9 ι * ι = 1 := by
  rw [hιb]
  linear_combination (-1 : F9) * hι

theorem su4_core (hq : CFSG.Open.IsQuasisimple (Su F9 3 1 4))
    (hZ : IsPGroup 2 (Subgroup.center (Su F9 3 1 4)))
    (hSp : CFSG.Open.IsQuasisimple (StatedSp 2 F3))
    (hSpZ : IsPGroup 2 (Subgroup.center (StatedSp 2 F3)))
    (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4))) (hρ2 : ρ * ρ = 1)
    (hfix : ∀ r ∈ rootSU2 F9 3 1 (by norm_num : 2 ≤ 4),
      ρ (QuotientGroup.mk r) = QuotientGroup.mk r) :
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
  have hdet : G.det ≠ 0 := by
    rw [hG]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hα' : ∀ x, suMat (α x) = G * φ.mapMatrix (suMat x) * Gi := fun x => by
    rw [hG, hGi]
    exact hα x
  have hgu' : (G.map σ9)ᵀ * G = 1 := by
    rw [hG]
    exact hgu
  obtain ⟨ι, hι, hιb⟩ := exists_iota
  have ht : σ9 ι * ι = 1 := iota_norm hι hιb
  have ht' : σ9 (σ9 ι) = ι := σ9_σ9 ι
  have hι0 : ι ≠ 0 := by
    intro h
    rw [h] at hι
    simp at hι
  have hcen : ∀ r ∈ rootSU2 F9 3 1 (by norm_num : 2 ≤ 4),
      (α r)⁻¹ * r ∈ Subgroup.center (Su F9 3 1 4) := by
    intro r hr
    apply QuotientGroup.eq.mp
    rw [← hρmk]
    exact hfix r hr
  have hr1mem : blockEmb F9 3 1 4 2 0 (by norm_num) (dSU F9 3 1 ht ht') ∈
      rootSU2 F9 3 1 (by norm_num : 2 ≤ 4) := ⟨_, rfl⟩
  have hr2mem : blockEmb F9 3 1 4 2 0 (by norm_num) (jSU F9 3 1) ∈
      rootSU2 F9 3 1 (by norm_num : 2 ≤ 4) := ⟨_, rfl⟩
  have hmat1 : suMat (blockEmb F9 3 1 4 2 0 (by norm_num) (dSU F9 3 1 ht ht')) =
      !![ι, 0, 0, 0; 0, σ9 ι, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    rw [suMat_blockEmb_zero, suMat_dSU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hmat2 : suMat (blockEmb F9 3 1 4 2 0 (by norm_num) (jSU F9 3 1)) =
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    rw [suMat_blockEmb_zero, suMat_jSU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hr1 : α (blockEmb F9 3 1 4 2 0 (by norm_num) (dSU F9 3 1 ht ht')) =
      blockEmb F9 3 1 4 2 0 (by norm_num) (dSU F9 3 1 ht ht') := by
    refine eq_of_trace_two α φ hGiG hα' (hcen _ hr1mem) ?_
    rw [hmat1]
    have : Matrix.trace !![ι, 0, 0, 0; 0, σ9 ι, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
        ι + σ9 ι + 1 + 1 := by
      simp [Matrix.trace, Fin.sum_univ_four]
    rw [this, hιb]
    ring
  have hr2 : α (blockEmb F9 3 1 4 2 0 (by norm_num) (jSU F9 3 1)) =
      blockEmb F9 3 1 4 2 0 (by norm_num) (jSU F9 3 1) := by
    refine eq_of_trace_two α φ hGiG hα' (hcen _ hr2mem) ?_
    rw [hmat2]
    have : Matrix.trace !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
        (0 : F9) + 0 + 1 + 1 := by
      simp [Matrix.trace, Fin.sum_univ_four]
    rw [this]
    ring
  have hd1 := key_rel α φ hGiG hα' hr1 hmat1
    (R' := !![φ ι, 0, 0, 0; 0, φ (σ9 ι), 0, 0; 0, 0, 1, 0; 0, 0, 0, 1])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp)
  have hj1 := key_rel α φ hGiG hα' hr2 hmat2
    (R' := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp)
  have huv : ι * σ9 ι = 1 := by rw [mul_comm]; exact ht
  have hne : σ9 ι ≠ ι := by
    intro h
    rw [hιb] at h
    have h2 : (2 : F9) * ι = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact two_ne_zero_F9 h3
    · exact hι0 h3
  obtain ⟨⟨g02, g03, g12, g13, g20, g21, g30, g31⟩, hcase⟩ :=
    core4_one σ9 φ huv hne rfl ht' hφ' G hdet hd1 hj1
  rcases hcase with ⟨hφ1, g01, g10, g11, ha⟩ | ⟨hφ1, g00, g11, g10, g01⟩
  · subst hφ1
    exact su4_case_id hq hZ ρ α hρmk hαα hGiG hα' hdet hgu' g01 g02 g03 g10 g20 g30 ha
  · subst hφ1
    exact su4_case_bar hSp hSpZ ρ α hρmk hαα hGiG hα' hgu' g00 g11 g10 g02 g03 g12 g13 g20 g21
      g30 g31

end Main

end CFSG.ClassicalInvolution.Q3.Q3MFOU4

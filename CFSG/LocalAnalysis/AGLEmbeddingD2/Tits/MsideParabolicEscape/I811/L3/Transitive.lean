module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Orbits
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Parabolic

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {F : Type} [Field F]

theorem relIndex_P1_of_transitive {W : Subgroup (SL3 F)}
    (htr : ∀ v : Fin 3 → F, v ≠ 0 → InOrbit W v) :
    (P1 : Subgroup (SL3 F)).relIndex W = (P1 : Subgroup (SL3 F)).index := by
  set x : SL3 F ⧸ (P1 : Subgroup (SL3 F)) := ((1 : SL3 F) : SL3 F ⧸ P1)
  have hstab : MulAction.stabilizer W x = (P1 : Subgroup (SL3 F)).subgroupOf W := by
    ext w
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    have h := congrArg (fun H : Subgroup (SL3 F) => (w : SL3 F) ∈ H)
      (MulAction.stabilizer_quotient (P1 : Subgroup (SL3 F)))
    simp only [MulAction.mem_stabilizer_iff, eq_iff_iff] at h
    rw [← h]
    rfl
  have horbit : MulAction.orbit W x = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨w, hw, c, hc, hwc⟩ := htr ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ e0)
      (ne_zero_of_mulVec e0_ne_zero)
    refine ⟨⟨w, hw⟩, ?_⟩
    change ((w * 1 : SL3 F) : SL3 F ⧸ P1) = (g : SL3 F ⧸ P1)
    rw [mul_one, QuotientGroup.eq, mem_P1_iff_exists]
    refine ⟨c⁻¹, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    have : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ e0 = c⁻¹ • ((w : Matrix (Fin 3) (Fin 3) F) *ᵥ e0) := by
      rw [hwc, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this, Matrix.mulVec_smul, sl_inv_mulVec_mulVec]
  rw [Subgroup.relIndex, ← hstab, Subgroup.index,
    ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer W x), horbit, Nat.card_univ]
  rfl

theorem index_eq_relIndex_of_transitive [Finite F] {W : Subgroup (SL3 F)}
    (htr : ∀ v : Fin 3 → F, v ≠ 0 → InOrbit W v) : W.index = W.relIndex P1 := by
  have h1 := Subgroup.relIndex_mul_index (inf_le_left : W ⊓ P1 ≤ W)
  have h2 := Subgroup.relIndex_mul_index (inf_le_right : W ⊓ P1 ≤ P1)
  rw [Subgroup.inf_relIndex_left, relIndex_P1_of_transitive htr] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hpos : 0 < (P1 : Subgroup (SL3 F)).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [mul_comm, h1, ← h2]

theorem eq_top_of_Q1_le_of_transitive {W : Subgroup (SL3 F)}
    (htr : ∀ v : Fin 3 → F, v ≠ 0 → InOrbit W v) (hQ : (Q1 : Subgroup (SL3 F)) ≤ W) :
    W = ⊤ := by
  rw [eq_top_iff, ← closure_transvectionSet, Subgroup.closure_le]
  intro τ hτ
  obtain ⟨v, φ, hv, -, hφv, rfl⟩ := mem_transvectionSet.mp hτ
  obtain ⟨g, hg, c, hc, hgc⟩ := htr v hv
  have hgv : ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = c⁻¹ • e0 := by
    have : v = c⁻¹ • ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ e0) := by
      rw [hgc, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this, Matrix.mulVec_smul, sl_inv_mulVec_mulVec]
  have hconj : g⁻¹ * tv v φ * g⁻¹⁻¹ ∈ W := by
    rw [conj_tv, hgv, tv_smul_left]
    exact hQ (tv_mem_pointGroup _ _)
  have := W.mul_mem (W.mul_mem hg hconj) (W.inv_mem hg)
  simpa [mul_assoc] using this

theorem cMat_mul_cMat : (cMat : Matrix (Fin 2) (Fin 2) F) * cMat = -cMat - 1 := by
  have h := cMat_relation (F := F)
  rw [← sub_eq_zero, ← h]
  abel

theorem cGL_pow_three : (cGL (F := F)) ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, coe_cGL, Units.val_one, pow_three, cMat_mul_cMat,
    Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_one, cMat_mul_cMat]
  abel

theorem cGL_ne_one : (cGL (F := F)) ≠ 1 := by
  intro h
  have := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [coe_cGL, cMat] at this

theorem sq_comm_of_mem_Nt {X : GL (Fin 2) F} (hX : X ∈ (Nt : Subgroup (GL (Fin 2) F))) :
    X ^ 2 * cGL = cGL * X ^ 2 := by
  have h := (Subgroup.mem_normalizer_iff.mp hX cGL).mp (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have h3 : (cGL (F := F)) ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact cGL_pow_three
  rw [zpow_eq_zpow_emod k h3] at hk
  have hk' : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hconj : X * cGL * X⁻¹ = cGL ∨ X * cGL * X⁻¹ = cGL ^ 2 := by
    rcases hk' with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hk
      have : cGL = (1 : GL (Fin 2) F) := by
        have := congrArg (fun Y => X⁻¹ * Y * X) hk
        simpa [mul_assoc] using this.symm
      exact cGL_ne_one this
    · left
      rw [h1, zpow_one] at hk
      exact hk.symm
    · right
      rw [h2] at hk
      rw [← hk]
      rfl
  rcases hconj with hc | hc
  · have : X * cGL = cGL * X := by
      calc X * cGL = X * cGL * X⁻¹ * X := by group
        _ = cGL * X := by rw [hc]
    rw [pow_two, mul_assoc, this, ← mul_assoc, this, mul_assoc]
  · have h2 : X * cGL ^ 2 * X⁻¹ = cGL := by
      rw [← conj_pow, hc, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, cGL_pow_three,
        one_mul]
    have h2' : X * cGL ^ 2 = cGL * X := by
      calc X * cGL ^ 2 = X * cGL ^ 2 * X⁻¹ * X := by group
        _ = cGL * X := by rw [h2]
    calc X ^ 2 * cGL = X * (X * cGL * X⁻¹) * X := by rw [pow_two]; group
      _ = X * cGL ^ 2 * X := by rw [hc, mul_assoc]
      _ = cGL * X * X := by rw [h2']
      _ = cGL * X ^ 2 := by rw [pow_two, mul_assoc]

@[expose] noncomputable def scalGL (μ : F) (hμ : μ ≠ 0) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero (μ • (1 : Matrix (Fin 2) (Fin 2) F)) (by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact pow_ne_zero _ hμ)

theorem coe_scalGL (μ : F) (hμ : μ ≠ 0) :
    ((scalGL μ hμ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = μ • 1 :=
  rfl

theorem scalGL_comm (μ : F) (hμ : μ ≠ 0) :
    ((scalGL μ hμ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * cMat =
      cMat * ((scalGL μ hμ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  rw [coe_scalGL, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem lev_scal_mulVec_e0 (μ : F) (hμ : μ ≠ 0) :
    ((lev (scalGL μ hμ) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e0 = (μ ^ 2)⁻¹ • e0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [lev_mulVec_zero, coe_scalGL, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    simp
  · rw [lev_mulVec_succ, coe_scalGL]
    fin_cases j <;> simp

theorem lev_scal_mulVec_of_zero (μ : F) (hμ : μ ≠ 0) {v : Fin 3 → F} (hv : v 0 = 0) :
    ((lev (scalGL μ hμ) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = μ • v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [lev_mulVec_zero, hv]
    simp [hv]
  · rw [lev_mulVec_succ, coe_scalGL]
    fin_cases j <;> simp

theorem false_of_map_rho1_le_Nt (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0) {μ : F} (hμ0 : μ ≠ 0)
    (hμ6 : μ ^ 6 ≠ 1) {W : Subgroup (SL3 F)}
    (hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ W)
    (htr : ∀ v : Fin 3 → F, v ≠ 0 → InOrbit W v)
    (hY : ((W ⊓ P1).subgroupOf P1).map rho1 ≤ (Nt : Subgroup (GL (Fin 2) F))) : False := by
  set y := lev (scalGL μ hμ0)
  have hy : y ∈ W := hlev _ (scalGL_comm μ hμ0)
  have he1 : (e1 : Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  obtain ⟨w, hw, c, hc, hwc⟩ := htr e1 he1
  set n := w⁻¹ * y * w
  have hnW : n ∈ W := W.mul_mem (W.mul_mem (W.inv_mem hw) hy) hw
  have hwinv : ((w⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (c • e1) = e0 := by
    rw [← hwc, sl_inv_mulVec_mulVec]
  have hn : ∀ v : Fin 3 → F, ((n : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ((w⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ((y : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((w : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) := by
    intro v
    simp only [n, Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hne0 : ((n : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e0 = μ • e0 := by
    rw [hn, hwc, lev_scal_mulVec_of_zero μ hμ0 (by simp), Matrix.mulVec_smul, hwinv]
  have hnP : n ∈ P1 := mem_P1_iff_exists.mpr ⟨μ, hne0⟩
  set ρ := rho1 (⟨n, hnP⟩ : (P1 : Subgroup (SL3 F)))
  have hρ : ρ ∈ (Nt : Subgroup (GL (Fin 2) F)) :=
    hY ⟨⟨n, hnP⟩, Subgroup.mem_subgroupOf.mpr ⟨hnW, hnP⟩, rfl⟩
  set x := ((w⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e0
  set z := ((w⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e2
  have hnx : ((n : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = (μ ^ 2)⁻¹ • x := by
    rw [hn, sl_mulVec_inv_mulVec, lev_scal_mulVec_e0, Matrix.mulVec_smul]
  have hnz : ((n : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z = μ • z := by
    rw [hn, sl_mulVec_inv_mulVec, lev_scal_mulVec_of_zero μ hμ0 (by simp), Matrix.mulVec_smul]
  have hxt : (fun j : Fin 2 => x j.succ) ≠ 0 := by
    intro ht
    have hx : x = x 0 • e0 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · have := congrFun ht j
        simp only [Pi.zero_apply] at this
        simp [this]
    have h1 : ((w : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = e0 := sl_mulVec_inv_mulVec w e0
    rw [hx, Matrix.mulVec_smul, hwc] at h1
    have := congrFun h1 0
    simp at this
  have hzt : (fun j : Fin 2 => z j.succ) ≠ 0 := by
    intro ht
    have hz : z = z 0 • e0 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · have := congrFun ht j
        simp only [Pi.zero_apply] at this
        simp [this]
    have h1 : ((w : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z = e2 := sl_mulVec_inv_mulVec w e2
    rw [hz, Matrix.mulVec_smul, hwc] at h1
    have := congrFun h1 2
    simp at this
  have hρx : (ρ : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun j => x j.succ) =
      (μ ^ 2)⁻¹ • (fun j => x j.succ) := by
    rw [rho1_mulVec]
    funext j
    simp only
    rw [hnx]
    rfl
  have hρz : (ρ : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun j => z j.succ) = μ • (fun j => z j.succ) := by
    rw [rho1_mulVec]
    funext j
    simp only
    rw [hnz]
    rfl
  have hsq := sq_comm_of_mem_Nt hρ
  have hsq' : ((ρ ^ 2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * cMat =
      cMat * ((ρ ^ 2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg Units.val hsq
    rwa [Units.val_mul, Units.val_mul, coe_cGL] at this
  have hρ2 : ((ρ ^ 2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (ρ : Matrix (Fin 2) (Fin 2) F) * (ρ : Matrix (Fin 2) (Fin 2) F) := by
    rw [pow_two, Units.val_mul]
  have hρ2z : ((ρ ^ 2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun j => z j.succ) =
      (μ ^ 2) • (fun j => z j.succ) := by
    rw [hρ2, ← Matrix.mulVec_mulVec, hρz, Matrix.mulVec_smul, hρz, smul_smul, pow_two]
  have hscal := eq_smul_one_of_comm_of_mulVec_eq hroot cMat_relation hsq' hzt hρ2z
  have hρ2x : ((ρ ^ 2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun j => x j.succ) =
      ((μ ^ 2)⁻¹ * (μ ^ 2)⁻¹) • (fun j => x j.succ) := by
    rw [hρ2, ← Matrix.mulVec_mulVec, hρx, Matrix.mulVec_smul, hρx, smul_smul]
  rw [hscal, Matrix.smul_mulVec, Matrix.one_mulVec] at hρ2x
  have hsub : (μ ^ 2 - (μ ^ 2)⁻¹ * (μ ^ 2)⁻¹) • (fun j : Fin 2 => x j.succ) = 0 := by
    rw [sub_smul, hρ2x, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · apply hμ6
    have hμ2 : μ ^ 2 ≠ 0 := pow_ne_zero _ hμ0
    have : μ ^ 2 = (μ ^ 2)⁻¹ * (μ ^ 2)⁻¹ := sub_eq_zero.mp h
    field_simp at this
    calc μ ^ 6 = μ ^ 2 * (μ ^ 2 * μ ^ 2) := by ring
      _ = 1 := by linear_combination this
  · exact hxt h

theorem eq_top_or_index_of_transitive [Finite F] (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hcube : ∀ x : F, ∃ y : F, y ^ 3 = x) (h3 : (3 : F) ≠ 0) (hmax : GL2NonsplitMax F)
    {μ : F} (hμ0 : μ ≠ 0) (hμ6 : μ ^ 6 ≠ 1) {W : Subgroup (SL3 F)}
    (hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W)
    (htr : ∀ v : Fin 3 → F, v ≠ 0 → InOrbit W v) :
    W = ⊤ ∨ W.index = Nat.card F ^ 2 := by
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ W :=
    fun X hX => hNW (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  have hlevY : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) →
        lev X ∈ W ⊓ P1 :=
    fun X hX => ⟨hlev X hX, lev_mem_P1 X⟩
  rcases inf_Q1_eq_bot_or_le hroot hcube hlevY with hb | hle
  · right
    have hNtY : (Nt : Subgroup (GL (Fin 2) F)) ≤ ((W ⊓ P1).subgroupOf P1).map rho1 := by
      intro X hX
      exact ⟨⟨lev X, lev_mem_P1 X⟩,
        Subgroup.mem_subgroupOf.mpr ⟨hNW (lev_mem_normalizer_A0 hX), lev_mem_P1 X⟩, rho1_lev X⟩
    rcases hmax _ hNtY with h | h
    · exact (false_of_map_rho1_le_Nt hroot hμ0 hμ6 hlev htr h.le).elim
    · have htop := map_rho1_eq_top hroot h3 hNtY h
      have hrel := relIndex_P1_eq htop
      rw [index_eq_relIndex_of_transitive htr, ← Subgroup.inf_relIndex_right, hrel,
        Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.mpr (disjoint_iff.mpr hb),
        Subgroup.index_bot, card_Q1]
  · left
    exact eq_top_of_Q1_le_of_transitive htr (hle.trans inf_le_left)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

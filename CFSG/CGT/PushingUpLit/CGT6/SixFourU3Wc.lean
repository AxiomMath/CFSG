module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Tv
public import CFSG.CGT.Timmesfeld75.CentralQuotient

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Wc

variable {s : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 s F)

@[expose] def a₀ : Fin 3 → F := ![1, 1, 0]

theorem sqNorm3_a₀ : sqNorm3 h (a₀ : Fin 3 → F) = 0 := by
  have h2 : (2 : F) = 0 := by
    have := h.charP
    exact CharP.cast_eq_zero F 2
  simp [sqNorm3, a₀, Fin.sum_univ_three]
  linear_combination h2

@[expose] noncomputable def tvG (a : Fin 3 → F) (ha : sqNorm3 h a = 0) (c : F)
    (hc : c + h.bar c = 0) : unitarySU 2 s F 3 :=
  ⟨tvGL h a ha c, tvGL_mem h a ha c hc⟩

theorem coe_tvG (a : Fin 3 → F) (ha : sqNorm3 h a = 0) (c : F) (hc : c + h.bar c = 0) :
    (((tvG h a ha c hc : unitarySU 2 s F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      tvM h a c := rfl

include h in
theorem two_eq_zero_of_h : (2 : F) = 0 := by
  have := h.charP
  exact CharP.cast_eq_zero F 2

include h in
theorem add_self_eq_zero_of_h (c : F) : c + c = 0 := by
  rw [← two_mul, two_eq_zero_of_h h, zero_mul]

@[expose] def TGsub (a : Fin 3 → F) (ha : sqNorm3 h a = 0) : Subgroup (unitarySU 2 s F 3) where
  carrier := {g | ∃ c : F, c + h.bar c = 0 ∧
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = tvM h a c}
  one_mem' := ⟨0, by simp, by simp [tvM_zero]⟩
  mul_mem' := by
    rintro g g' ⟨c, hc, hg⟩ ⟨c', hc', hg'⟩
    refine ⟨c + c', by rw [map_add]; linear_combination hc + hc', ?_⟩
    show (((g : GL (Fin 3) F) * (g' : GL (Fin 3) F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [Units.val_mul, hg, hg', tvM_mul h a ha]
  inv_mem' := by
    rintro g ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    have hmul : tvM h a c * tvM h a c = 1 := by
      rw [tvM_mul h a ha, add_self_eq_zero_of_h h, tvM_zero]
    show (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [Matrix.coe_units_inv, hg]
    exact Matrix.inv_eq_right_inv hmul

theorem tvG_mem_TGsub (a : Fin 3 → F) (ha : sqNorm3 h a = 0) (c : F) (hc : c + h.bar c = 0) :
    tvG h a ha c hc ∈ TGsub h a ha := ⟨c, hc, rfl⟩

@[expose] noncomputable def T0 : Subgroup (unitaryPSU h 3) :=
  (TGsub h (a₀ : Fin 3 → F) (sqNorm3_a₀ h)).map (unitaryProj h 3)

include h in
theorem tvM_sq (a : Fin 3 → F) (ha : sqNorm3 h a = 0) (c : F) : tvM h a c * tvM h a c = 1 := by
  rw [tvM_mul h a ha, add_self_eq_zero_of_h h, tvM_zero]

theorem multiple_of_tvM_commute (a' : Fin 3 → F) (ha' : sqNorm3 h a' = 0) (c c' : F) (hc0 : c ≠ 0)
    (hc'0 : c' ≠ 0)
    (hcomm : tvM h (a₀ : Fin 3 → F) c * tvM h a' c' = tvM h a' c' * tvM h (a₀ : Fin 3 → F) c) :
    ∃ lam : F, a' = lam • (a₀ : Fin 3 → F) := by
  have h2 := two_eq_zero_of_h h
  have hbar1 : h.bar 1 = 1 := map_one h.bar
  have hbar0 : h.bar 0 = 0 := map_zero h.bar
  have e0 := congrFun (congrFun hcomm 0) 0
  have e1 := congrFun (congrFun hcomm 1) 0
  have e2 := congrFun (congrFun hcomm 2) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, tvM_apply, a₀] at e0 e1 e2
  simp at e0 e1 e2
  have hcc : c * c' ≠ 0 := mul_ne_zero hc0 hc'0
  have E0 : a' 1 * h.bar (a' 0) = a' 0 * h.bar (a' 1) :=
    mul_left_cancel₀ hcc (by linear_combination e0)
  have E1 : a' 0 * h.bar (a' 0) = a' 1 * h.bar (a' 1) :=
    mul_left_cancel₀ hcc (by linear_combination e1)
  have hiso : h.bar (a' 0) * a' 0 + h.bar (a' 1) * a' 1 + h.bar (a' 2) * a' 2 = 0 := by
    simpa [sqNorm3, Fin.sum_univ_three] using ha'
  have hx2 : a' 2 = 0 := by
    have h3 : h.bar (a' 2) * a' 2 = 0 := by
      linear_combination hiso - (a' 0 * h.bar (a' 0)) * h2 + E1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact (h.bar_eq_zero_iff).mp h4
    · exact h4
  have hx01 : a' 1 = a' 0 := by
    by_cases h0 : a' 0 = 0
    · have h5 : a' 1 * h.bar (a' 1) = 0 := by rw [← E1, h0, zero_mul]
      rcases mul_eq_zero.mp h5 with h6 | h6
      · rw [h6, h0]
      · have := (h.bar_eq_zero_iff).mp h6
        rw [this, h0]
    · have hX0 : h.bar (a' 0) ≠ 0 := by rwa [Ne, h.bar_eq_zero_iff]
      have h5 : (a' 1 + a' 0) ^ 2 * h.bar (a' 0) = 0 := by
        linear_combination (a' 1) * E0 + (a' 0) * E1 +
          (a' 0 * a' 1 * (h.bar (a' 0) + h.bar (a' 1))) * h2
      rcases mul_eq_zero.mp h5 with h6 | h6
      · have h7 : a' 1 + a' 0 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h6
        linear_combination h7 - (a' 0) * h2
      · exact absurd h6 hX0
  refine ⟨a' 0, ?_⟩
  funext i
  fin_cases i
  · simp [a₀]
  · simp [a₀, hx01]
  · simp [a₀, hx2]

theorem tvM_commute_of_pi_commute (a a' : Fin 3 → F) (ha : sqNorm3 h a = 0) (ha' : sqNorm3 h a' = 0)
    (c c' : F) (hc : c + h.bar c = 0) (hc' : c' + h.bar c' = 0)
    (hcomm : unitaryProj h 3 (tvG h a ha c hc) * unitaryProj h 3 (tvG h a' ha' c' hc') =
      unitaryProj h 3 (tvG h a' ha' c' hc') * unitaryProj h 3 (tvG h a ha c hc)) :
    tvM h a c * tvM h a' c' = tvM h a' c' * tvM h a c := by
  set x := tvG h a ha c hc with hx
  set y := tvG h a' ha' c' hc' with hy
  have hxy : (QuotientGroup.mk (x * y) : unitaryPSU h 3) = QuotientGroup.mk (y * x) := by
    have := hcomm
    simp only [unitaryProj, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul] at this
    exact this
  obtain ⟨ζ, -, -, hζ⟩ := mem_unitaryScalars.mp (QuotientGroup.eq.mp hxy)
  have hGL : ((y * x : unitarySU 2 s F 3) : GL (Fin 3) F) =
      ((x * y : unitarySU 2 s F 3) : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) ζ := by
    rw [← hζ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hmat := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hGL
  simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    at hmat
  rw [← Matrix.smul_eq_mul_diagonal] at hmat
  have hmat' : tvM h a' c' * tvM h a c = (ζ : F) • (tvM h a c * tvM h a' c') := hmat
  clear hmat
  have hMsq := tvM_sq h a ha c
  have hM'sq := tvM_sq h a' ha' c'
  have h1 : tvM h a' c' * tvM h a c * tvM h a' c' = (ζ : F) • tvM h a c := by
    rw [hmat', smul_mul_assoc, Matrix.mul_assoc, hM'sq, Matrix.mul_one]
  have h2 : (tvM h a' c' * tvM h a c * tvM h a' c') * (tvM h a' c' * tvM h a c * tvM h a' c') = 1 := by
    calc (tvM h a' c' * tvM h a c * tvM h a' c') * (tvM h a' c' * tvM h a c * tvM h a' c')
        = tvM h a' c' * tvM h a c * (tvM h a' c' * tvM h a' c') * tvM h a c * tvM h a' c' := by
          simp only [Matrix.mul_assoc]
      _ = tvM h a' c' * (tvM h a c * tvM h a c) * tvM h a' c' := by
          rw [hM'sq, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMsq, Matrix.mul_one, hM'sq]
  rw [h1, smul_mul_smul_comm, hMsq] at h2
  have h3 := congrFun (congrFun h2 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h3
  have hζ1 : (ζ : F) = 1 := by
    have h4 : ((ζ : F) + 1) ^ 2 = 0 := by
      linear_combination h3 + ((ζ : F) + 1) * two_eq_zero_of_h h
    have h5 := pow_eq_zero_iff (two_ne_zero) |>.mp h4
    linear_combination h5 - two_eq_zero_of_h h
  rw [hζ1, one_smul] at hmat'
  exact hmat'.symm

theorem tvM_smul_center (lam : F) (a : Fin 3 → F) (c : F) :
    tvM h (lam • a) c = tvM h a ((lam * h.bar lam) * c) := by
  ext i j
  simp only [tvM_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem bar_norm (lam : F) : h.bar (lam * h.bar lam) = lam * h.bar lam := by
  rw [map_mul, h.bar_bar, mul_comm]

theorem unitary_of_mem (γ : unitarySU 2 s F 3) :
    (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
  ((mem_unitarySU_iff h).mp γ.2).2

theorem sqNorm3_mulVec (γ : unitarySU 2 s F 3) (a : Fin 3 → F) :
    sqNorm3 h (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ a) = sqNorm3 h a := by
  have := ((mem_unitarySU_iff_isometry h).mp γ.2).2 a a
  simpa [CFSG.LinearGroups.stdHermForm_apply, sqNorm3] using this

theorem tvG_eq_of_matrix (a : Fin 3 → F) (ha : sqNorm3 h a = 0) (c : F) (hc : c + h.bar c = 0)
    (g : unitarySU 2 s F 3)
    (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = tvM h a c) : g = tvG h a ha c hc :=
  Subtype.ext (Units.ext hg)

theorem conj_tvG (γ : unitarySU 2 s F 3) (a : Fin 3 → F) (ha : sqNorm3 h a = 0) (c : F)
    (hc : c + h.bar c = 0) :
    γ * tvG h a ha c hc * γ⁻¹ =
      tvG h (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ a)
        ((sqNorm3_mulVec h γ a).trans ha) c hc := by
  apply tvG_eq_of_matrix
  show (((γ : GL (Fin 3) F) * (tvGL h a ha c) * (γ : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) = _
  rw [Units.val_mul, Units.val_mul]
  exact conj_tvM h (γ : GL (Fin 3) F) (unitary_of_mem h γ) a c

theorem conj_TGsub_le (γ : unitarySU 2 s F 3) (lam : F)
    (hγ : ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (a₀ : Fin 3 → F) = lam • a₀) :
    CFSG.CGT.Timmesfeld75.conjSubgroup γ (TGsub h (a₀ : Fin 3 → F) (sqNorm3_a₀ h)) ≤
      TGsub h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) := by
  intro x hx
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hx
  obtain ⟨c, hc, hmat⟩ := hx
  have hxeq : x = γ * tvG h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) c hc * γ⁻¹ := by
    have : γ⁻¹ * x * γ = tvG h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) c hc := tvG_eq_of_matrix h _ _ c hc _ hmat
    calc x = γ * (γ⁻¹ * x * γ) * γ⁻¹ := by group
      _ = _ := by rw [this]
  rw [hxeq, conj_tvG]
  refine ⟨(lam * h.bar lam) * c, ?_, ?_⟩
  · rw [map_mul, bar_norm h, ← mul_add, hc, mul_zero]
  · show tvM h (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (a₀ : Fin 3 → F)) c = _
    rw [hγ, tvM_smul_center]

include h in
theorem isElemAbelian_TGsub :
    CFSG.Open.IsElemAbelian 2 (TGsub h (a₀ : Fin 3 → F) (sqNorm3_a₀ h)) := by
  refine ⟨⟨⟨fun g g' => ?_⟩⟩, fun g hg => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    obtain ⟨c, hc, hgc⟩ := g.2
    obtain ⟨c', hc', hgc'⟩ := g'.2
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hgc, hgc', tvM_mul h _ (sqNorm3_a₀ h), tvM_mul h _ (sqNorm3_a₀ h), add_comm]
  · obtain ⟨c, hc, hgc⟩ := hg
    apply Subtype.ext
    apply Units.ext
    show (((g : unitarySU 2 s F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 2 = 1
    rw [hgc, pow_two]
    exact tvM_sq h _ (sqNorm3_a₀ h) c

theorem T0_isWC : CFSG.CGT.Timmesfeld75.IsWC (T0 h) := by
  have hTG := isElemAbelian_TGsub h
  have hT0 : CFSG.Open.IsElemAbelian 2 (T0 h) :=
    CFSG.CGT.Timmesfeld75.isElemAbelian_map_of_hom hTG _
  refine ⟨hT0, fun t ht ht1 => ⟨?_, fun g hg => ?_⟩⟩
  · intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.CGT.Timmesfeld75.elemAbelian_mul_comm hT0 hu ht
  · obtain ⟨γ, rfl⟩ := unitaryProj_surjective h 3 g
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨c₀, hc₀, hmat₀⟩ := ht'
    have hc₀ne : c₀ ≠ 0 := by
      rintro rfl
      apply ht1
      have : t' = 1 := Subtype.ext (Units.ext (by rw [hmat₀, tvM_zero]; rfl))
      rw [this, map_one]
    obtain ⟨c₁, hc₁E, hc₁ne⟩ := h.exists_mem_traceZero_ne_zero
    have hc₁ : c₁ + h.bar c₁ = 0 := (h.mem_traceZero).mp hc₁E
    have hmem : unitaryProj h 3 (γ * tvG h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) c₁ hc₁ * γ⁻¹) ∈
        CFSG.CGT.Timmesfeld75.conjSubgroup (unitaryProj h 3 γ) (T0 h) := by
      rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      refine ⟨tvG h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) c₁ hc₁, tvG_mem_TGsub h _ _ c₁ hc₁, ?_⟩
      simp only [map_mul, map_inv]
      group
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hg hmem)
    rw [conj_tvG] at hcomm
    have ht'eq : t' = tvG h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) c₀ hc₀ :=
      tvG_eq_of_matrix h _ _ c₀ hc₀ t' hmat₀
    rw [ht'eq] at hcomm
    obtain ⟨lam, hlam⟩ := multiple_of_tvM_commute h
      (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (a₀ : Fin 3 → F))
      ((sqNorm3_mulVec h γ _).trans (sqNorm3_a₀ h)) c₀ c₁ hc₀ne hc₁ne
      (tvM_commute_of_pi_commute h _ _ (sqNorm3_a₀ h) ((sqNorm3_mulVec h γ _).trans (sqNorm3_a₀ h))
        c₀ c₁ hc₀ hc₁ hcomm.symm)
    have hle0 := conj_TGsub_le h γ lam hlam
    have hle : CFSG.CGT.Timmesfeld75.conjSubgroup (unitaryProj h 3 γ) (T0 h) ≤ T0 h := by
      unfold T0
      rw [← CFSG.CGT.Timmesfeld75.map_conjSubgroup]
      exact Subgroup.map_mono hle0
    have := h.finite
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    unfold CFSG.CGT.Timmesfeld75.conjSubgroup
    rw [Subgroup.card_map_of_injective (MulAut.conj (unitaryProj h 3 γ)).injective]

theorem conjSubgroup_TGsub (γ : unitarySU 2 s F 3) (a : Fin 3 → F) (ha : sqNorm3 h a = 0) :
    CFSG.CGT.Timmesfeld75.conjSubgroup γ (TGsub h a ha) =
      TGsub h (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ a)
        ((sqNorm3_mulVec h γ a).trans ha) := by
  ext x
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
  constructor
  · rintro ⟨c, hc, hmat⟩
    have hxeq : x = γ * tvG h a ha c hc * γ⁻¹ := by
      have : γ⁻¹ * x * γ = tvG h a ha c hc := tvG_eq_of_matrix h _ _ c hc _ hmat
      calc x = γ * (γ⁻¹ * x * γ) * γ⁻¹ := by group
        _ = _ := by rw [this]
    rw [hxeq, conj_tvG]
    exact tvG_mem_TGsub h _ _ c hc
  · rintro ⟨c, hc, hmat⟩
    have hx : x = γ * tvG h a ha c hc * γ⁻¹ := by
      rw [conj_tvG]
      exact tvG_eq_of_matrix h _ _ c hc x hmat
    have h2 : γ⁻¹ * x * γ = tvG h a ha c hc := by
      rw [hx]
      group
    exact ⟨c, hc, by rw [h2]; rfl⟩

theorem tvG_not_mem_scalars (c : F) (hc : c + h.bar c = 0) (hc0 : c ≠ 0) :
    tvG h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) c hc ∉ unitaryScalars h 3 := by
  intro hz
  obtain ⟨ζ, -, -, hζ⟩ := mem_unitaryScalars.mp hz
  have hmat := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hζ
  have e00 := congrFun (congrFun hmat 0) 0
  have e22 := congrFun (congrFun hmat 2) 2
  simp [coe_tvG, tvM_apply, a₀, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e00 e22
  apply hc0
  linear_combination e00 - e22

theorem T0_ne_bot : T0 h ≠ ⊥ := by
  obtain ⟨c₁, hc₁E, hc₁ne⟩ := h.exists_mem_traceZero_ne_zero
  have hc₁ : c₁ + h.bar c₁ = 0 := (h.mem_traceZero).mp hc₁E
  intro hbot
  have hmem : unitaryProj h 3 (tvG h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) c₁ hc₁) ∈ T0 h :=
    Subgroup.mem_map_of_mem _ (tvG_mem_TGsub h _ _ c₁ hc₁)
  rw [hbot, Subgroup.mem_bot] at hmem
  apply tvG_not_mem_scalars h c₁ hc₁ hc₁ne
  rw [← ker_unitaryProj, MonoidHom.mem_ker]
  exact hmem

end Wc

end CFSG.CGT.PushingUpLit.CGT6

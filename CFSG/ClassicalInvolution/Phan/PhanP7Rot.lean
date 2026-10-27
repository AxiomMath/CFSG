module

public import CFSG.ClassicalInvolution.Phan.PhanP6PlaneB

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.MF15
open scoped MatrixGroups Pointwise

section Basis

variable {F : Type} [Field F]

theorem jOp_vecA1 (ε : F) : jOp ε (vecA1 F) = (frame0 (F := F)).incl (Jm ε) := by
  rw [vecA1, jOp_incl, Matrix.one_mul]

theorem jOp_jOp_vecA1 (ε : F) : jOp ε (jOp ε (vecA1 F)) = (-ε) • vecA1 F := by
  rw [jOp_vecA1, jOp_incl, Jm_mul_Jm, vecA1, map_smul]

theorem jOp_vecB1 (ε : F) :
    jOp ε (vecB1 F) = (frame0 (F := F)).incl (!![1, 0; 0, -1] * Jm ε) := by
  rw [vecB1, jOp_incl]

theorem comb_eq_incl (X Y : Matrix (Fin 2) (Fin 2) F) (α β : F) :
    α • (frame0 (F := F)).incl X + β • (frame0 (F := F)).incl Y =
      (frame0 (F := F)).incl (α • X + β • Y) := by
  simp [map_add, map_smul]

theorem Q_comb_A (ε α β : F) :
    quadPlus 4 F (α • vecA1 F + β • jOp ε (vecA1 F)) = α ^ 2 + ε * β ^ 2 := by
  rw [jOp_vecA1, vecA1, comb_eq_incl, Frame.Q_incl]
  simp [Matrix.det_fin_two, Jm]
  ring

theorem Q_comb_B (ε α β : F) :
    quadPlus 4 F (α • vecB1 F + β • jOp ε (vecB1 F)) = -(α ^ 2 + ε * β ^ 2) := by
  rw [jOp_vecB1, vecB1, comb_eq_incl, Frame.Q_incl]
  simp [Matrix.det_fin_two, Jm]
  ring

theorem exists_comb_of_mem_planeA {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0} (h2 : (2 : F) ≠ 0)
    {x : Fin 4 ⊕ Fin 4 → F} (hx : x ∈ planeA ε hε h4) :
    ∃ α β : F, x = α • vecA1 F + β • jOp ε (vecA1 F) := by
  obtain ⟨hxx, hFJ⟩ := (mem_planeA_iff h2).1 hx
  refine ⟨(frame0 (F := F)).coords x 0 0, -(frame0 (F := F)).coords x 0 1, ?_⟩
  rw [jOp_vecA1, vecA1, comb_eq_incl]
  conv_lhs => rw [hxx]
  congr 1
  obtain ⟨h1, h2'⟩ := hFJ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jm, h1, h2']
  ring

theorem exists_comb_of_mem_planeB {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0} (h2 : (2 : F) ≠ 0)
    {x : Fin 4 ⊕ Fin 4 → F} (hx : x ∈ planeB ε hε h4) :
    ∃ α β : F, x = α • vecB1 F + β • jOp ε (vecB1 F) := by
  obtain ⟨hxx, hFJ⟩ := (mem_planeB_iff h2).1 hx
  refine ⟨(frame0 (F := F)).coords x 0 0, -(frame0 (F := F)).coords x 0 1, ?_⟩
  rw [jOp_vecB1, vecB1, comb_eq_incl]
  conv_lhs => rw [hxx]
  congr 1
  obtain ⟨h1, h2'⟩ := hFJ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jm, h1, h2']
  ring

theorem FJ.mul {ε : F} {M N : Matrix (Fin 2) (Fin 2) F} (hM : FJ ε M) (hN : FJ ε N) :
    FJ ε (M * N) := by
  obtain ⟨h1, h2⟩ := hM
  obtain ⟨h1', h2'⟩ := hN
  refine ⟨?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h1', h2'] <;> ring

theorem FJ.adjugate {ε : F} {M : Matrix (Fin 2) (Fin 2) F} (hM : FJ ε M) : FJ ε (M.adjugate) := by
  obtain ⟨h1, h2⟩ := hM
  refine ⟨?_, ?_⟩ <;> simp [Matrix.adjugate_fin_two, h1, h2]

theorem comb_A_inj {ε : F} (hε : ε ≠ 0) {α β α' β' : F}
    (h : α • vecA1 F + β • jOp ε (vecA1 F) = α' • vecA1 F + β' • jOp ε (vecA1 F)) :
    α = α' ∧ β = β' := by
  rw [jOp_vecA1, vecA1, comb_eq_incl, comb_eq_incl] at h
  have h1 := congrArg (frame0 (F := F)).coords h
  rw [Frame.coords_incl, Frame.coords_incl] at h1
  have e00 := congrFun (congrFun h1 0) 0
  have e10 := congrFun (congrFun h1 1) 0
  simp [Jm] at e00 e10
  refine ⟨e00, ?_⟩
  exact e10.resolve_right hε

end Basis

section Torus

variable {F K : Type} [Field F] [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
  [CharP K p] {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))} {ε : F} {hε : ε ≠ 0}
  {h4 : (4 : F) ≠ 0}

@[expose] def NSet (ε : F) : Type := {pr : F × F // pr.1 ^ 2 + ε * pr.2 ^ 2 = 1}

instance [Finite F] : Finite (NSet ε) := Subtype.finite

theorem exists_param_A (h2 : (2 : F) ≠ 0) {g : spinGroup (quadPlus 4 F)}
    (hg : g ∈ stabOf (spinAction (quadPlus 4 F)) (planeA ε hε h4)) :
    ∃ pr : NSet ε, spinAction (quadPlus 4 F) g (vecA1 F) =
      pr.1.1 • vecA1 F + pr.1.2 • jOp ε (vecA1 F) := by
  have hmem : spinAction (quadPlus 4 F) g (vecA1 F) ∈ planeA ε hε h4 :=
    (hg _).2 (vecA1_mem_planeA ε hε h4)
  obtain ⟨α, β, h⟩ := exists_comb_of_mem_planeA h2 hmem
  refine ⟨⟨(α, β), ?_⟩, h⟩
  have hQ := map_spinAction (quadPlus 4 F) g (vecA1 F)
  rw [h, Q_comb_A, Q_vecA1] at hQ
  exact hQ

theorem exists_param_B_of_mem (h2 : (2 : F) ≠ 0) {g : spinGroup (quadPlus 4 F)}
    (hmem : spinAction (quadPlus 4 F) g (vecB1 F) ∈ planeB ε hε h4) :
    ∃ pr : NSet ε, spinAction (quadPlus 4 F) g (vecB1 F) =
      pr.1.1 • vecB1 F + pr.1.2 • jOp ε (vecB1 F) := by
  obtain ⟨α, β, h⟩ := exists_comb_of_mem_planeB h2 hmem
  refine ⟨⟨(α, β), ?_⟩, h⟩
  have hQ := map_spinAction (quadPlus 4 F) g (vecB1 F)
  rw [h, Q_comb_B, Q_vecB1] at hQ
  exact neg_inj.1 hQ

theorem exists_param_B (h2 : (2 : F) ≠ 0) {g : spinGroup (quadPlus 4 F)}
    (hg : g ∈ stabOf (spinAction (quadPlus 4 F)) (planeB ε hε h4)) :
    ∃ pr : NSet ε, spinAction (quadPlus 4 F) g (vecB1 F) =
      pr.1.1 • vecB1 F + pr.1.2 • jOp ε (vecB1 F) :=
  exists_param_B_of_mem h2 ((hg _).2 (vecB1_mem_planeB ε hε h4))

theorem eq_of_rot_A (hS : ModelSpec S ε hε h4) {t t' : spinGroup (quadPlus 4 F)}
    (ht : t ∈ (S.ι 0).range) (ht' : t' ∈ (S.ι 0).range)
    (h : spinAction (quadPlus 4 F) t (vecA1 F) = spinAction (quadPlus 4 F) t' (vecA1 F)) :
    t = t' := by
  have hmem : t'⁻¹ * t ∈ (S.ι 0).range := mul_mem (inv_mem ht') ht
  have hr : spinAction (quadPlus 4 F) (t'⁻¹ * t) ∈ (stdFrames ε hε h4 0).La.range := by
    rw [← hS.map_range 0]
    exact ⟨_, hmem, rfl⟩
  obtain ⟨M, hM⟩ := hr
  have hfix : spinAction (quadPlus 4 F) (t'⁻¹ * t) (vecA1 F) = vecA1 F := by
    rw [map_mul, LinearEquiv.mul_apply, h, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel,
      map_one]
    rfl
  have hM1 : M = 1 := by
    refine La_eq_one_of_fix (frame0 (F := F)) (b := vecA1 F) ?_ ?_ ?_
    · rw [vecA1, Frame.coords_incl]
    · rw [Q_vecA1]
      exact one_ne_zero
    · show (stdFrames ε hε h4 0).La M (vecA1 F) = vecA1 F
      rw [hM]
      exact hfix
  have h1 : t'⁻¹ * t = 1 := hS.inj 0 _ hmem (by rw [← hM, hM1, map_one])
  exact (inv_mul_eq_one.1 h1).symm

theorem eq_of_rot_B (hS : ModelSpec S ε hε h4) (h2 : (2 : F) ≠ 0)
    {t t' : spinGroup (quadPlus 4 F)}
    (ht : t ∈ (S.ι 1).range) (ht' : t' ∈ (S.ι 1).range)
    (h : spinAction (quadPlus 4 F) t (vecB1 F) = spinAction (quadPlus 4 F) t' (vecB1 F)) :
    t = t' := by
  have hmem : t'⁻¹ * t ∈ (S.ι 1).range := mul_mem (inv_mem ht') ht
  have hr : spinAction (quadPlus 4 F) (t'⁻¹ * t) ∈ (stdFrames ε hε h4 1).La.range := by
    rw [← hS.map_range 1]
    exact ⟨_, hmem, rfl⟩
  obtain ⟨M, hM⟩ := hr
  have hfix : spinAction (quadPlus 4 F) (t'⁻¹ * t) (vecB1 F) = vecB1 F := by
    rw [map_mul, LinearEquiv.mul_apply, h, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel,
      map_one]
    rfl
  have hb1 : vecB1 F ∈ planeB ε hε h4 := vecB1_mem_planeB ε hε h4
  have hsp : vecB1 F = (frame1 ε hε h4).incl ((frame1 ε hε h4).coords (vecB1 F)) := by
    refine eq_incl_coords_of_La_neg_one h2 (frame1 ε hε h4) ?_
    have := hb1.2.1
    change (frame1 ε hε h4).La (-1) (vecB1 F) = (-1 : F) • vecB1 F at this
    simpa using this
  have hM1 : M = 1 := by
    refine La_eq_one_of_fix (frame1 ε hε h4) (b := vecB1 F) hsp ?_ ?_
    · rw [Q_vecB1]
      exact neg_ne_zero.2 one_ne_zero
    · show (stdFrames ε hε h4 1).La M (vecB1 F) = vecB1 F
      rw [hM]
      exact hfix
  have h1 : t'⁻¹ * t = 1 := hS.inj 1 _ hmem (by rw [← hM, hM1, map_one])
  exact (inv_mul_eq_one.1 h1).symm

theorem La_mem_planeA {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0} (h2 : (2 : F) ≠ 0) {M : SL(2, F)}
    (hM : FJ ε (M : Matrix (Fin 2) (Fin 2) F)) {x : Fin 4 ⊕ Fin 4 → F}
    (hx : x ∈ planeA ε hε h4) : (frame0 (F := F)).La M x ∈ planeA ε hε h4 := by
  obtain ⟨hxx, hFJ⟩ := (mem_planeA_iff h2).1 hx
  rw [hxx, Frame.La_apply_incl]
  exact incl_mem_planeA_of_FJ ε hε h4 (hM.mul hFJ)

theorem exists_tor_zero_of_param (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    (pr : NSet ε) :
    ∃ t ∈ (tor S 0).range, spinAction (quadPlus 4 F) t (vecA1 F) =
      pr.1.1 • vecA1 F + pr.1.2 • jOp ε (vecA1 F) := by
  obtain ⟨⟨α, β⟩, hpr⟩ := pr
  let M0 : Matrix (Fin 2) (Fin 2) F := !![α, -β; ε * β, α]
  have hdet : M0.det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hpr
  let M : SL(2, F) := ⟨M0, hdet⟩
  have hFJ : FJ ε (M : Matrix (Fin 2) (Fin 2) F) := ⟨by simp [M, M0], by simp [M, M0]⟩
  have hFJinv : FJ ε ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    exact hFJ.adjugate
  have hr : (frame0 (F := F)).La M ∈
      (S.ι 0).range.map (spinAction (quadPlus 4 F)) := by
    rw [hS.map_range 0]
    exact ⟨M, rfl⟩
  obtain ⟨ρ, hρ, hρM⟩ := hr
  have hstab : ρ ∈ stabOf (spinAction (quadPlus 4 F)) (planeA ε hε h4) := by
    intro x
    rw [hρM]
    refine ⟨fun hx => ?_, fun hx => La_mem_planeA h2 hFJ hx⟩
    have := La_mem_planeA (hε := hε) (h4 := h4) h2 hFJinv hx
    rwa [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
  refine ⟨ρ, mem_range_tor_zero_of_stab hK hg hS hq h2 h2K hρ hstab, ?_⟩
  rw [hρM]
  rw [vecA1, Frame.La_apply_incl, Matrix.mul_one, jOp_incl, comb_eq_incl]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, M0, Jm]
  ring

theorem tor_range_le_torusSub (j : Fin 4) : (tor S j).range ≤ torusSub S := by
  rintro _ ⟨x, rfl⟩
  exact tor_mem_torusSub S j x

theorem card_tor (hg : GoodFamily S) (j : Fin 4) :
    Nat.card (tor S j).range = Nat.card (normOne (unitaryInvolution K p f)) := by
  have hinj : Function.Injective (tor S j) := fun x y h => torusTwo_injective _ (hg.inj j h)
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem exists_tor_one_of_param [Finite F] (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    (pr : NSet ε) :
    ∃ t ∈ (tor S 1).range, spinAction (quadPlus 4 F) t (vecB1 F) =
      pr.1.1 • vecB1 F + pr.1.2 • jOp ε (vecB1 F) := by
  have hT0 : ∀ t : (tor S 0).range, ∃ q : NSet ε, spinAction (quadPlus 4 F) t.1 (vecA1 F) =
      q.1.1 • vecA1 F + q.1.2 • jOp ε (vecA1 F) := fun t =>
    exists_param_A h2 (torusSub_le_stabOf_eigSpace hK hg hS h2 h2K _ _ _
      (tor_range_le_torusSub 0 t.2))
  choose g0 hg0 using hT0
  have g0_inj : Function.Injective g0 := by
    intro t t' h
    have : spinAction (quadPlus 4 F) t.1 (vecA1 F) = spinAction (quadPlus 4 F) t'.1 (vecA1 F) := by
      rw [hg0, hg0, h]
    obtain ⟨x, hx⟩ := t.2
    obtain ⟨x', hx'⟩ := t'.2
    exact Subtype.ext (eq_of_rot_A hS ⟨_, hx⟩ ⟨_, hx'⟩ this)
  have g0_surj : Function.Surjective g0 := by
    intro q
    obtain ⟨t, ht, hq'⟩ := exists_tor_zero_of_param hK hg hS hq h2 h2K q
    refine ⟨⟨t, ht⟩, ?_⟩
    have := hg0 ⟨t, ht⟩
    rw [hq'] at this
    obtain ⟨h1, h3⟩ := comb_A_inj hε this
    exact Subtype.ext (Prod.ext h1.symm h3.symm)
  have hT1 : ∀ t : (tor S 1).range, ∃ q : NSet ε, spinAction (quadPlus 4 F) t.1 (vecB1 F) =
      q.1.1 • vecB1 F + q.1.2 • jOp ε (vecB1 F) := fun t =>
    exists_param_B h2 (torusSub_le_stabOf_eigSpace hK hg hS h2 h2K _ _ _
      (tor_range_le_torusSub 1 t.2))
  choose g1 hg1 using hT1
  have g1_inj : Function.Injective g1 := by
    intro t t' h
    have : spinAction (quadPlus 4 F) t.1 (vecB1 F) = spinAction (quadPlus 4 F) t'.1 (vecB1 F) := by
      rw [hg1, hg1, h]
    obtain ⟨x, hx⟩ := t.2
    obtain ⟨x', hx'⟩ := t'.2
    exact Subtype.ext (eq_of_rot_B hS h2 ⟨_, hx⟩ ⟨_, hx'⟩ this)
  have hcard : Nat.card (tor S 1).range = Nat.card (NSet ε) := by
    rw [card_tor hg 1, ← card_tor hg 0]
    exact Nat.card_congr (Equiv.ofBijective g0 ⟨g0_inj, g0_surj⟩)
  have g1_bij : Function.Bijective g1 :=
    g1_inj.bijective_of_nat_card_le hcard.ge
  obtain ⟨t, ht⟩ := g1_bij.2 pr
  refine ⟨t.1, t.2, ?_⟩
  rw [hg1, ht]

theorem La_FJ_apply_B {ε : F} {M : SL(2, F)} (hFJ : FJ ε (M : Matrix (Fin 2) (Fin 2) F))
    {X : Matrix (Fin 2) (Fin 2) F} (hX : FJ' ε X) :
    (frame0 (F := F)).La M ((frame0 (F := F)).incl X) =
      (M : Matrix (Fin 2) (Fin 2) F) 0 0 • (frame0 (F := F)).incl X -
        (-(M : Matrix (Fin 2) (Fin 2) F) 0 1) • jOp ε ((frame0 (F := F)).incl X) := by
  rw [Frame.La_apply_incl, jOp_incl, ← map_smul, ← map_smul, ← map_sub]
  congr 1
  obtain ⟨h1, h2'⟩ := hFJ
  obtain ⟨k1, k2⟩ := hX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Jm, h1, h2', k1, k2] <;> first | ring1 | (left; ring1)

theorem exists_regular_tor_zero (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0) :
    ∃ t₀ ∈ (tor S 0).range, ∃ a b : F, b ≠ 0 ∧ ∀ x ∈ planeB ε hε h4,
      spinAction (quadPlus 4 F) t₀ x = a • x - b • jOp ε x := by
  obtain ⟨x₀, hx₀⟩ := exists_normOne_sq_ne_one hK (by omega : 3 ≤ p ^ f)
  have ht₀R : tor S 0 x₀ ∈ (S.ι 0).range := ⟨_, rfl⟩
  have hst₀ : tor S 0 x₀ ∈ stabOf (spinAction (quadPlus 4 F)) (planeA ε hε h4) :=
    torusSub_le_stabOf_eigSpace hK hg hS h2 h2K (-1) 1 1 (tor_mem_torusSub S 0 x₀)
  obtain ⟨M, hM, hFJ⟩ := exists_FJ_of_mem_stab hS ht₀R hst₀
  refine ⟨tor S 0 x₀, ⟨x₀, rfl⟩, (M : Matrix (Fin 2) (Fin 2) F) 0 0,
    -(M : Matrix (Fin 2) (Fin 2) F) 0 1, ?_, ?_⟩
  · intro hb
    have hb' : (M : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := neg_eq_zero.1 hb
    obtain ⟨h1, h2'⟩ := hFJ
    have hdet : (M : Matrix (Fin 2) (Fin 2) F).det = 1 := M.2
    rw [Matrix.det_fin_two, h1, h2', hb'] at hdet
    have ha : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      linear_combination hdet
    have hM1 : M = 1 ∨ M = -1 := by
      have hsq : M * M = 1 := by
        refine Subtype.ext ?_
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2', hb', ha]
      exact sq_eq_one_sl2 h2 hsq
    rcases hM1 with rfl | rfl
    · have h1' : tor S 0 x₀ = 1 := by
        refine hS.inj 0 _ ht₀R ?_
        rw [← hM, map_one]
      have hx1 : x₀ = 1 := by
        apply torusTwo_injective (unitaryInvolution K p f)
        apply hg.inj 0
        rw [map_one, map_one]
        exact h1'
      exact hx₀ (by rw [hx1, one_mul])
    · have hs : tor S 0 x₀ = sInv S 0 := by
        have hmem : tor S 0 x₀ * (sInv S 0)⁻¹ ∈ (S.ι 0).range :=
          mul_mem ht₀R (inv_mem ⟨_, rfl⟩)
        have := hS.inj 0 _ hmem (by
          rw [map_mul, map_inv, ← hM, spinAction_sInv hg hS h2 h2K 0]
          simp [stdFrames])
        exact mul_inv_eq_one.1 this
      have hx1 : x₀ = negOne (unitaryInvolution K p f) := by
        apply torusTwo_injective (unitaryInvolution K p f)
        apply hg.inj 0
        exact hs
      exact hx₀ (by rw [hx1, negOne_mul_self])
  · intro x hx
    obtain ⟨hxx, hFJ'⟩ := (mem_planeB_iff h2).1 hx
    rw [← hM]
    show (frame0 (F := F)).La M x = _
    have key := La_FJ_apply_B (ε := ε) hFJ hFJ'
    rw [← hxx] at key
    exact key

end Torus

end CFSG.ClassicalInvolution.PhanP

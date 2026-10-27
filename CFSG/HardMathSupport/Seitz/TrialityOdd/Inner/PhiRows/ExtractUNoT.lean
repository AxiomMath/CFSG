module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ShortExtractNoT

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement

section ExtractUNoT


variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)

@[expose] def HasShortRoot (H : Subgroup (twistedGroup σ.toRingHom)) : Prop :=
  ∃ k : ℤ, (k = 5 ∨ k = 3) ∧ ∃ x ∈ hexGroup (twistedX σ.toRingHom) k, x ∈ H ∧ x ≠ 1

include hσ in
theorem exists_short_of_U_element_zero
    [Finite K]
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hlong : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    (a₀ : K) (c₁ c₃ c₅ : fixedField σ.toRingHom) (a₂ a₄ : K)
    (hy : d4X hσ 0 a₀ * d4X hσ 1 c₁ * d4X hσ 2 a₂ * d4X hσ 3 c₃ * d4X hσ 4 a₄ * d4X hσ 5 c₅ ∈ H)
    (h0 : a₀ ≠ 0) : HasShortRoot H := by
  have R := d4Rel_model hσ
  have hX5 : d4X hσ 5 (1 : fixedField σ.toRingHom) ∈ H :=
    hlong (root_le_longSub (k := 6) ⟨by norm_num, by norm_num⟩ (by norm_num)
      (d4X_mem_hexGroup' hσ 5 _ (by norm_num)))
  set x : twistedGroup σ.toRingHom := d4X hσ 5 (1 : fixedField σ.toRingHom) with hx
  have c55 : Commute (d4X hσ 5 c₅) x := by
    have h1 := d4X_add hσ 5 c₅ (1 : fixedField σ.toRingHom)
    have h2' := d4X_add hσ 5 (1 : fixedField σ.toRingHom) c₅
    exact (h1.symm.trans ((congrArg (d4X hσ 5) (add_comm _ _)).trans h2'))
  have hZ : Commute (d4X hσ 2 a₂ * (d4X hσ 3 c₃ * (d4X hσ 4 a₄ * d4X hσ 5 c₅))) x :=
    (R.c25 a₂ 1).mul_left ((R.c35 c₃ 1).mul_left ((R.c45 a₄ 1).mul_left c55))
  set Z : twistedGroup σ.toRingHom :=
    d4X hσ 2 a₂ * (d4X hσ 3 c₃ * (d4X hσ 4 a₄ * d4X hσ 5 c₅)) with hZdef
  have hy' : d4X hσ 0 a₀ * (d4X hσ 1 c₁ * Z) ∈ H := by
    have : d4X hσ 0 a₀ * (d4X hσ 1 c₁ * Z) =
        d4X hσ 0 a₀ * d4X hσ 1 c₁ * d4X hσ 2 a₂ * d4X hσ 3 c₃ * d4X hσ 4 a₄ * d4X hσ 5 c₅ := by
      rw [hZdef]; group
    rw [this]; exact hy
  have e1 : (d4X hσ 1 c₁ * Z) * x * (d4X hσ 1 c₁ * Z)⁻¹ = d4X hσ 3 (-(c₁ * 1)) * x := by
    have h1 : Z * x * Z⁻¹ = x := by rw [hZ.eq]; group
    calc (d4X hσ 1 c₁ * Z) * x * (d4X hσ 1 c₁ * Z)⁻¹
        = d4X hσ 1 c₁ * (Z * x * Z⁻¹) * (d4X hσ 1 c₁)⁻¹ := by group
      _ = d4X hσ 1 c₁ * x * (d4X hσ 1 c₁)⁻¹ := by rw [h1]
      _ = ⁅d4X hσ 1 c₁, x⁆ * x := by rw [commutatorElement_def]; group
      _ = d4X hσ 3 (-(c₁ * 1)) * x := by rw [hx, R.r15 c₁ 1]; rfl
  have e2 : (d4X hσ 0 a₀ * (d4X hσ 1 c₁ * Z)) * x * (d4X hσ 0 a₀ * (d4X hσ 1 c₁ * Z))⁻¹ * x⁻¹ =
      d4X hσ 3 (-(c₁ * 1)) * ⁅d4X hσ 0 a₀, x⁆ := by
    have h3 : d4X hσ 0 a₀ * d4X hσ 3 (-(c₁ * 1)) = d4X hσ 3 (-(c₁ * 1)) * d4X hσ 0 a₀ :=
      (R.c03 a₀ (-(c₁ * 1))).eq
    calc (d4X hσ 0 a₀ * (d4X hσ 1 c₁ * Z)) * x * (d4X hσ 0 a₀ * (d4X hσ 1 c₁ * Z))⁻¹ * x⁻¹
        = d4X hσ 0 a₀ * ((d4X hσ 1 c₁ * Z) * x * (d4X hσ 1 c₁ * Z)⁻¹) * (d4X hσ 0 a₀)⁻¹ * x⁻¹ := by
          group
      _ = d4X hσ 0 a₀ * (d4X hσ 3 (-(c₁ * 1)) * x) * (d4X hσ 0 a₀)⁻¹ * x⁻¹ := by rw [e1]
      _ = (d4X hσ 0 a₀ * d4X hσ 3 (-(c₁ * 1))) * x * (d4X hσ 0 a₀)⁻¹ * x⁻¹ := by group
      _ = d4X hσ 3 (-(c₁ * 1)) * (d4X hσ 0 a₀ * x * (d4X hσ 0 a₀)⁻¹ * x⁻¹) := by rw [h3]; group
      _ = d4X hσ 3 (-(c₁ * 1)) * ⁅d4X hσ 0 a₀, x⁆ := by rw [commutatorElement_def]
  have hw : d4X hσ 3 (-(c₁ * 1)) * ⁅d4X hσ 0 a₀, x⁆ ∈ H := by
    rw [← e2]
    exact H.mul_mem (H.mul_mem (H.mul_mem hy' hX5) (H.inv_mem hy')) (H.inv_mem hX5)
  have h05 := R.r05 a₀ 1
  have key : ∀ (e n m : fixedField σ.toRingHom) (s p : K),
      d4X hσ 3 e * (d4X hσ 1 n * d4X hσ 2 s * d4X hσ 3 m * d4X hσ 4 p) =
        d4X hσ 1 n * d4X hσ 2 s * d4X hσ 3 (e + m) * d4X hσ 4 p * d4X hσ 5 (0 : fixedField σ.toRingHom) := by
    intro e n m s p
    have h5 : d4X hσ 5 (0 : fixedField σ.toRingHom) = 1 := (d4X_eq_one_iff hσ).2 rfl
    have c1 : d4X hσ 3 e * d4X hσ 1 n = d4X hσ 1 n * d4X hσ 3 e := (R.c13 n e).eq.symm
    have c2 : d4X hσ 3 e * d4X hσ 2 s = d4X hσ 2 s * d4X hσ 3 e := (R.c23 s e).eq.symm
    have hadd : d4X hσ 3 (e + m) = d4X hσ 3 e * d4X hσ 3 m := d4X_add hσ 3 e m
    rw [h5, hadd]
    calc d4X hσ 3 e * (d4X hσ 1 n * d4X hσ 2 s * d4X hσ 3 m * d4X hσ 4 p)
        = (d4X hσ 3 e * d4X hσ 1 n) * d4X hσ 2 s * d4X hσ 3 m * d4X hσ 4 p := by group
      _ = d4X hσ 1 n * (d4X hσ 3 e * d4X hσ 2 s) * d4X hσ 3 m * d4X hσ 4 p := by rw [c1]; group
      _ = d4X hσ 1 n * d4X hσ 2 s * d4X hσ 3 e * d4X hσ 3 m * d4X hσ 4 p := by rw [c2]; group
      _ = _ := by group
  rw [← hx] at h05
  dsimp only at h05
  rw [h05] at hw
  have hw' := (key _ _ _ _ _) ▸ hw
  refine exists_short_of_Q_element hσ ha H hlong _ _ 0 _ _ hw' (Or.inr ?_)
  simp [h0]

include hσ in
theorem exists_short_of_posUnipotent_not_longSub
    [Finite K]
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hlong : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    {y : twistedGroup σ.toRingHom}
    (hyH : y ∈ H) (hyU : y ∈ posUnipotent (g2Shape (twistedX σ.toRingHom)))
    (hyL : y ∉ longSub 6 (hexGroup (twistedX σ.toRingHom))) : HasShortRoot H := by
  obtain ⟨c, rfl⟩ := (mem_posUnipotent_d4_iff hσ y).1 hyU
  have hy : d4X hσ 0 (c 0) * d4X hσ 1 (c 1) * d4X hσ 2 (c 2) * d4X hσ 3 (c 3) * d4X hσ 4 (c 4) *
      d4X hσ 5 (c 5) ∈ H := by
    have : prod6 (fun i => d4X hσ i (c i)) = d4X hσ 0 (c 0) * d4X hσ 1 (c 1) * d4X hσ 2 (c 2) *
        d4X hσ 3 (c 3) * d4X hσ 4 (c 4) * d4X hσ 5 (c 5) := by
      unfold prod6; group
    rw [← this]; exact hyH
  by_cases h0 : c 0 = 0
  · have e0 : d4X hσ 0 (c 0) = 1 := (d4X_eq_one_iff hσ).2 h0
    rw [e0, one_mul] at hy
    by_cases h24 : c 2 = 0 ∧ c 4 = 0
    · apply absurd _ hyL
      have e2 : d4X hσ 2 (c 2) = 1 := (d4X_eq_one_iff hσ).2 h24.1
      have e4 : d4X hσ 4 (c 4) = 1 := (d4X_eq_one_iff hσ).2 h24.2
      have hL : ∀ (i : Fin 6) (k : ℤ), (i : ℤ) + 1 = k → k % 2 = 0 → IsRoot 6 k →
          ∀ z : d43Par σ.toRingHom i, d4X hσ i z ∈ longSub 6 (hexGroup (twistedX σ.toRingHom)) :=
        fun i k hk hk2 hkr z => root_le_longSub hkr hk2 (d4X_mem_hexGroup' hσ i z hk)
      have h1 := hL 1 2 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩ (c 1)
      have h3 := hL 3 4 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩ (c 3)
      have h5 := hL 5 6 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩ (c 5)
      have : prod6 (fun i => d4X hσ i (c i)) = d4X hσ 1 (c 1) * d4X hσ 3 (c 3) * d4X hσ 5 (c 5) := by
        have e0' : d4X hσ 0 (c 0) = 1 := e0
        unfold prod6
        simp only [e0', e2, e4, one_mul]
        group
      rw [this]
      exact mul_mem (mul_mem h1 h3) h5
    · have hne : c 2 ≠ 0 ∨ c 4 ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact h24 hcon
      exact exists_short_of_Q_element hσ ha H hlong (c 1) (c 3) (c 5) (c 2) (c 4) hy hne
  · exact exists_short_of_U_element_zero hσ ha H hlong (c 0) (c 1) (c 3) (c 5) (c 2) (c 4) hy h0

end ExtractUNoT

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

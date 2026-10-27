module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ShortExtract
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.ThreeQ1Long

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement

section ShortExtractNoT


variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)

include hσ in
theorem exists_short_of_Q_element
    [Finite K]
    (ha : ∃ a : (fixedField σ.toRingHom)ˣ, (a : fixedField σ.toRingHom) ≠ 1)
    (H : Subgroup (twistedGroup σ.toRingHom))
    (hlong : longSub 6 (hexGroup (twistedX σ.toRingHom)) ≤ H)
    (c₁ c₃ c₅ : fixedField σ.toRingHom) (a₂ a₄ : K)
    (hy : d4X hσ 1 c₁ * d4X hσ 2 a₂ * d4X hσ 3 c₃ * d4X hσ 4 a₄ * d4X hσ 5 c₅ ∈ H)
    (hne : a₂ ≠ 0 ∨ a₄ ≠ 0) :
    ∃ k : ℤ, (k = 5 ∨ k = 3) ∧ ∃ x ∈ hexGroup (twistedX σ.toRingHom) k, x ∈ H ∧ x ≠ 1 := by
  have hlongX : ∀ (i : Fin 6) (c : d43Par σ.toRingHom i) (k : ℤ), (i : ℤ) + 1 = k →
      k % 2 = 0 → CFSG.GH74.BNPair.IsRoot 6 k → d4X hσ i c ∈ H := fun i c k hk hk2 hkr =>
    hlong (root_le_longSub hkr hk2 (d4X_mem_hexGroup' hσ i c hk))
  have hX1 : d4X hσ 1 c₁ ∈ H := hlongX 1 c₁ 2 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
  have hX3 : d4X hσ 3 c₃ ∈ H := hlongX 3 c₃ 4 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
  have hX5 : d4X hσ 5 c₅ ∈ H := hlongX 5 c₅ 6 (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
  have hc23 : d4X hσ 2 a₂ * d4X hσ 3 c₃ = d4X hσ 3 c₃ * d4X hσ 2 a₂ :=
    ((d4Rel_model hσ).c23 a₂ c₃).eq
  have hs : d4X hσ 2 a₂ * d4X hσ 4 a₄ ∈ H := by
    have e : d4X hσ 2 a₂ * d4X hσ 4 a₄ =
        (d4X hσ 3 c₃)⁻¹ * ((d4X hσ 1 c₁)⁻¹ *
          (d4X hσ 1 c₁ * d4X hσ 2 a₂ * d4X hσ 3 c₃ * d4X hσ 4 a₄ * d4X hσ 5 c₅) *
            (d4X hσ 5 c₅)⁻¹) := by
      have e1 : (d4X hσ 3 c₃)⁻¹ * ((d4X hσ 1 c₁)⁻¹ *
          (d4X hσ 1 c₁ * d4X hσ 2 a₂ * d4X hσ 3 c₃ * d4X hσ 4 a₄ * d4X hσ 5 c₅) *
            (d4X hσ 5 c₅)⁻¹) =
          (d4X hσ 3 c₃)⁻¹ * (d4X hσ 2 a₂ * d4X hσ 3 c₃) * d4X hσ 4 a₄ := by group
      rw [e1, hc23]; group
    rw [e]
    exact H.mul_mem (H.inv_mem hX3) (H.mul_mem (H.mul_mem (H.inv_mem hX1) hy) (H.inv_mem hX5))
  by_cases h0 : a₂ = 0
  · have ha4 : a₄ ≠ 0 := hne.resolve_left (by simpa using h0)
    have hX2 : d4X hσ 2 a₂ = 1 := (d4X_eq_one_iff hσ).2 h0
    rw [hX2, one_mul] at hs
    exact ⟨5, Or.inl rfl, _, d4X_mem_hexGroup' hσ 4 a₄ (by norm_num), hs,
      fun h => ha4 ((d4X_eq_one_iff hσ).1 h)⟩
  · obtain ⟨a, ha1⟩ := ha
    set aK : Kˣ := Units.map (fixedField σ.toRingHom).subtype.toMonoidHom a with haK_def
    have haK : Units.map σ.toRingHom.toMonoidHom aK = aK := fixed_unit_map_fix a
    have hτs : slShort σ.toRingHom hσ (HSL aK) ∈ H :=
      hlong (Coordinator.slShort_HSL_fixed_mem_longSub hσ a)
    have hτl : slLong σ.toRingHom hσ (HSL a) ∈ H :=
      hlong (Coordinator.slLong_HSL_mem_longSub hσ a)
    set τ := slShort σ.toRingHom hσ (HSL aK) * slLong σ.toRingHom hσ (HSL a) with hτ
    have hτH : τ ∈ H := H.mul_mem hτs hτl
    have hmul : ((aK⁻¹ : Kˣ) : K) * ((a : fixedField σ.toRingHom) : K) = 1 := by
      have : ((aK : Kˣ) : K) = ((a : fixedField σ.toRingHom) : K) := rfl
      rw [← this]; exact Units.inv_mul aK
    have w4 : ∀ u : K, τ * d4X hσ 4 u * τ⁻¹ = d4X hσ 4 u := by
      intro u
      have e : τ * d4X hσ 4 u * τ⁻¹ = slShort σ.toRingHom hσ (HSL aK) *
          (slLong σ.toRingHom hσ (HSL a) * d4X hσ 4 u * (slLong σ.toRingHom hσ (HSL a))⁻¹) *
            (slShort σ.toRingHom hσ (HSL aK))⁻¹ := by rw [hτ]; group
      rw [e, conj_slLong_pos4 hσ a u, conj_slShort_pos4 hσ aK haK,
        ← mul_assoc, hmul, one_mul]
    have w2 : ∀ u : K, τ * d4X hσ 2 u * τ⁻¹ = d4X hσ 2 (((aK : Kˣ) : K) * u) := by
      intro u
      have e : τ * d4X hσ 2 u * τ⁻¹ = slShort σ.toRingHom hσ (HSL aK) *
          (slLong σ.toRingHom hσ (HSL a) * d4X hσ 2 u * (slLong σ.toRingHom hσ (HSL a))⁻¹) *
            (slShort σ.toRingHom hσ (HSL aK))⁻¹ := by rw [hτ]; group
      rw [e, conj_slLong_pos2 hσ a u, conj_slShort_pos2 hσ aK haK]
    have hconj : τ * (d4X hσ 2 a₂ * d4X hσ 4 a₄) * τ⁻¹ =
        d4X hσ 2 (((aK : Kˣ) : K) * a₂) * d4X hσ 4 a₄ := by
      have e : τ * (d4X hσ 2 a₂ * d4X hσ 4 a₄) * τ⁻¹ =
          (τ * d4X hσ 2 a₂ * τ⁻¹) * (τ * d4X hσ 4 a₄ * τ⁻¹) := by group
      rw [e, w2, w4]
    have hw : d4X hσ 2 (((aK : Kˣ) : K) * a₂) * (d4X hσ 2 a₂)⁻¹ =
        d4X hσ 2 ((((aK : Kˣ) : K) - 1) * a₂) := by
      have h := d4X_add hσ (2 : Fin 6) ((((aK : Kˣ) : K) - 1) * a₂) a₂
      have e : (((aK : Kˣ) : K) - 1) * a₂ + a₂ = ((aK : Kˣ) : K) * a₂ := by ring
      have h' : d4X hσ 2 (((aK : Kˣ) : K) * a₂) =
          d4X hσ 2 ((((aK : Kˣ) : K) - 1) * a₂) * d4X hσ 2 a₂ :=
        (congrArg (fun c : K => d4X hσ 2 c) e.symm).trans h
      rw [h']; group
    have hmemw : d4X hσ 2 (((aK : Kˣ) : K) * a₂) * (d4X hσ 2 a₂)⁻¹ ∈ H := by
      have h1 : τ * (d4X hσ 2 a₂ * d4X hσ 4 a₄) * τ⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem hτH hs) (H.inv_mem hτH)
      rw [hconj] at h1
      have h2' := H.mul_mem h1 (H.inv_mem hs)
      have e : d4X hσ 2 (((aK : Kˣ) : K) * a₂) * d4X hσ 4 a₄ *
          (d4X hσ 2 a₂ * d4X hσ 4 a₄)⁻¹ =
          d4X hσ 2 (((aK : Kˣ) : K) * a₂) * (d4X hσ 2 a₂)⁻¹ := by group
      rwa [e] at h2'
    rw [hw] at hmemw
    have hne1 : (((aK : Kˣ) : K) - 1) * a₂ ≠ 0 := by
      refine mul_ne_zero (fun h => ha1 ?_) h0
      have : ((aK : Kˣ) : K) = 1 := sub_eq_zero.1 h
      exact Subtype.ext this
    exact ⟨3, Or.inr rfl, _, d4X_mem_hexGroup' hσ 2 _ (by norm_num), hmemw,
      fun h => hne1 ((d4X_eq_one_iff hσ).1 h)⟩


end ShortExtractNoT

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

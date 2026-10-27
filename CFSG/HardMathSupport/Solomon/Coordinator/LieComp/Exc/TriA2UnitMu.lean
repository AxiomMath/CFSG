module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnFinal
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Root
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.Stage2.Bender.Thm1

set_option linter.unusedSectionVars false

theorem norm_cond_of_eps_four {K : Type} [Field K] (ε : K ≃+* K)
    (hε4 : ∀ c, ε (ε (ε (ε c))) = c) (m : K) (hm : m ≠ 0) :
    (-(m * ε m)⁻¹) * ε ((-(m * ε m)⁻¹)⁻¹ * ε ((-(m * ε m)⁻¹) *
      ε ((-(m * ε m)⁻¹)⁻¹ * ε 1))) = 1 := by
  have h1 : ε m ≠ 0 := fun h => hm (ε.injective (by rw [h, map_zero]))
  have h2 : ε (ε m) ≠ 0 := fun h => h1 (ε.injective (by rw [h, map_zero]))
  have h3 : ε (ε (ε m)) ≠ 0 := fun h => h2 (ε.injective (by rw [h, map_zero]))
  have e4 := hε4 m
  simp only [map_one, mul_one, map_mul, map_neg, map_inv₀, map_mul, e4, inv_neg, inv_inv,
    mul_inv_rev]
  field_simp

theorem eps_restrict_frob {Q q₄ : ℕ} {K : Type} [Field K] [Finite K] {σ ε : K ≃+* K}
    (hq₄ : q₄ = Q ^ 4) (hσ : ∀ c, σ c = c ^ q₄) (hε : ∀ c, ε c = c ^ (Q ^ 9))
    (c : ↥(fixSubfield σ)) : fixSubfieldRestrict ε σ c = c ^ Q := by
  apply Subtype.ext
  show ε (c : K) = ((c : K)) ^ Q
  have hc : (c : K) ^ q₄ = (c : K) := by
    have := hσ (c : K)
    have hfix : σ (c : K) = c := (mem_fixSubfield σ).1 c.2
    rw [← this, hfix]
  rw [hε]
  have e9 : Q ^ 9 = (Q ^ 4) * (Q ^ 4) * Q := by ring
  rw [e9, pow_mul, pow_mul, ← hq₄, hc, hc]

theorem exists_mu_unitary {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    {σ ε : K ≃+* K} {b : Kˣ} {q₄ : ℕ} (hA : A2Core σ b q₄) (hq₄ : q₄ = (p ^ f) ^ 4)
    (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) (hεb : Units.map ε.toRingHom.toMonoidHom b = b⁻¹)
    (hε4 : ∀ c, ε (ε (ε (ε c))) = c) :
    ∃ μ : Kˣ, (b : K) * σ (μ : K) = μ ∧ (μ : K) * ε (μ : K) = -1 := by
  classical
  obtain ⟨μ₀, hμ₀⟩ := A2Core.a2Fix_exists_solution hA 1
  have hm₀ : (b : K) * σ (μ₀ : K) = μ₀ := by simpa using hμ₀
  have hεb' : ε (b : K) = ((b⁻¹ : Kˣ) : K) := congrArg Units.val hεb
  have hεbinv : ε ((b⁻¹ : Kˣ) : K) = (b : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hεb', Units.val_inv_eq_inv_val, inv_inv]
  have hbne : (b : K) ≠ 0 := b.ne_zero
  have hσμ : σ (μ₀ : K) = ((b⁻¹ : Kˣ) : K) * μ₀ := by
    have : σ (μ₀ : K) = ((b⁻¹ : Kˣ) : K) * ((b : K) * σ (μ₀ : K)) := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [this, hm₀]
  set F : Subfield K := fixSubfield σ with hFdef
  have hFcard : Nat.card F = q₄ :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hA.two_le hA.card hA.frob
  have hμ₀ne : (μ₀ : K) ≠ 0 := μ₀.ne_zero
  have hεμne : ε (μ₀ : K) ≠ 0 := fun h => hμ₀ne (ε.injective (by rw [h, map_zero]))
  have hκne : (μ₀ : K) * ε (μ₀ : K) ≠ 0 := mul_ne_zero hμ₀ne hεμne
  have hκσ : σ ((μ₀ : K) * ε (μ₀ : K)) = (μ₀ : K) * ε (μ₀ : K) := by
    have hcomm : σ (ε (μ₀ : K)) = ε (σ (μ₀ : K)) := apply_apply_comm_of_finite σ ε _
    rw [map_mul, hcomm, hσμ, map_mul, hεbinv]
    have hbinv : ((b⁻¹ : Kˣ) : K) = (b : K)⁻¹ := Units.val_inv_eq_inv_val b
    rw [hbinv]
    field_simp
  set νK : K := -((μ₀ : K) * ε (μ₀ : K))⁻¹ with hνK
  have hνKne : νK ≠ 0 := by
    rw [hνK]
    simpa using hκne
  have hνmem : νK ∈ F := by
    rw [hFdef, mem_fixSubfield, hνK, map_neg, map_inv₀, hκσ]
  let σQ : ↥F ≃+* ↥F := fixSubfieldRestrict ε σ
  have hσQ : ∀ c : ↥F, σQ c = c ^ (p ^ f) := by
    intro c
    apply Subtype.ext
    show ε (c : K) = ((c : K)) ^ (p ^ f)
    have hc : (c : K) ^ q₄ = (c : K) := by
      have := hA.frob (c : K)
      have hfix : σ (c : K) = c := (mem_fixSubfield σ).1 c.2
      rw [← this, hfix]
    rw [hε]
    have e9 : (p ^ f) ^ 9 = ((p ^ f) ^ 4) * ((p ^ f) ^ 4) * (p ^ f) := by ring
    rw [e9, pow_mul, pow_mul, ← hq₄, hc, hc]
  have hFk : Nat.card ↥F = (p ^ f) ^ 4 := by rw [hFcard, hq₄]
  let ν : (↥F)ˣ := Units.mk0 ⟨νK, hνmem⟩ (fun h => hνKne (congrArg Subtype.val h))
  have hνcoe : ((ν : ↥F) : K) = νK := rfl
  have hνinv : ((((ν⁻¹ : (↥F)ˣ) : ↥F)) : K) = νK⁻¹ := by
    rw [Units.val_inv_eq_inv_val]
    rfl
  have hN : (ν : ↥F) * σQ (((ν⁻¹ : (↥F)ˣ) : ↥F) * σQ ((ν : ↥F) *
      σQ (((ν⁻¹ : (↥F)ˣ) : ↥F) * σQ 1))) = 1 := by
    apply Subtype.ext
    have h : νK * ε (νK⁻¹ * ε (νK * ε (νK⁻¹ * ε 1))) = 1 :=
      norm_cond_of_eps_four ε hε4 (μ₀ : K) hμ₀ne
    show ((ν : ↥F) : K) * ε ((((ν⁻¹ : (↥F)ˣ) : ↥F) : K) * ε (((ν : ↥F) : K) *
      ε ((((ν⁻¹ : (↥F)ˣ) : ↥F) : K) * ε 1))) = 1
    rw [hνcoe, hνinv]
    exact h
  obtain ⟨t, ht⟩ := un_norm_solution (p := p) (f := f) (by omega) (k := ↥F) hFk σQ hσQ ν hN
  set tK : K := ((t : ↥F) : K) with htK
  have htσ : σ tK = tK := (mem_fixSubfield σ).1 t.1.2
  have htne : tK ≠ 0 := fun h => t.ne_zero (Subtype.ext h)
  have hnorm : tK * ε tK = νK := by
    have h1 : tK * (νK⁻¹ * ε tK) = 1 := by
      have h0 : ((((t : ↥F) * (((ν⁻¹ : (↥F)ˣ) : ↥F) * σQ (t : ↥F)) : ↥F)) : K) = 1 := by
        rw [ht]
        rfl
      change tK * ((((ν⁻¹ : (↥F)ˣ) : ↥F) : K) * ε tK) = 1 at h0
      rw [hνinv] at h0
      exact h0
    calc tK * ε tK = νK * (tK * (νK⁻¹ * ε tK)) := by field_simp
      _ = νK := by rw [h1, mul_one]
  refine ⟨μ₀ * Units.mk0 tK htne, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mk0, map_mul, htσ, ← mul_assoc, hm₀]
  · rw [Units.val_mul, Units.val_mk0, map_mul]
    calc (μ₀ : K) * tK * (ε (μ₀ : K) * ε tK) = ((μ₀ : K) * ε (μ₀ : K)) * (tK * ε tK) := by ring
      _ = -1 := by rw [hnorm, hνK]; field_simp

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

module

public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.IrreducibleDegreeDividesOrder

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Values

variable {L G : Type*} [Group G] {S : Set (L → ℂ)}

noncomputable def coherentVal (ν : Submodule.span ℤ S →+ virtualChars G) (χ : S) : G → ℂ :=
  (ν ⟨(χ : L → ℂ), Submodule.subset_span χ.2⟩ : G → ℂ)

theorem coherentVal_apply (ν : Submodule.span ℤ S →+ virtualChars G) (χ : S) :
    coherentVal ν χ = (ν ⟨(χ : L → ℂ), Submodule.subset_span χ.2⟩ : G → ℂ) := (rfl)

theorem coherentVal_mem_virtualChars (ν : Submodule.span ℤ S →+ virtualChars G) (χ : S) :
    coherentVal ν χ ∈ virtualChars G :=
  (ν ⟨(χ : L → ℂ), Submodule.subset_span χ.2⟩).2

end Values

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S : Set (L → ℂ)} {τ : charSpanZero S →+ virtualChars G}
  {ν : Submodule.span ℤ S →+ virtualChars G}

open scoped Classical in
theorem cfInner_coherentVal_coherentVal (hS : S ⊆ Irr L) (hν : IsCoherentWith S τ ν) (χ ψ : S) :
    cfInner (coherentVal ν χ) (coherentVal ν ψ) = if χ = ψ then 1 else 0 := by
  rw [coherentVal_apply, coherentVal_apply, hν.inner_eq,
    cfInner_eq_ite_of_mem_Irr (hS χ.2) (hS ψ.2)]
  simp [Subtype.ext_iff]

theorem cfInner_self_coherentVal (hS : S ⊆ Irr L) (hν : IsCoherentWith S τ ν) (χ : S) :
    cfInner (coherentVal ν χ) (coherentVal ν χ) = 1 := by
  simpa using cfInner_coherentVal_coherentVal hS hν χ χ

theorem coherentVal_mem_signedIrr (hS : S ⊆ Irr L) (hν : IsCoherentWith S τ ν) (χ : S) :
    coherentVal ν χ ∈ signedIrr G :=
  mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one
    (mem_virtualChars_iff.1 (coherentVal_mem_virtualChars ν χ)) (cfInner_self_coherentVal hS hν χ)

theorem coherentVal_injective (hν : IsCoherentWith S τ ν) :
    Function.Injective (coherentVal ν) := by
  intro χ ψ h
  rw [coherentVal_apply, coherentVal_apply] at h
  have h2 : (⟨(χ : L → ℂ), Submodule.subset_span χ.2⟩ : Submodule.span ℤ S)
      = ⟨(ψ : L → ℂ), Submodule.subset_span ψ.2⟩ := hν.injective (Subtype.ext h)
  exact Subtype.ext (congrArg (fun z : Submodule.span ℤ S => (z : L → ℂ)) h2)

theorem apply_one_mul_coherentVal_apply_one
    (hτ : ∀ f : charSpanZero S, (τ f : G → ℂ) 1 = 0) (hν : IsCoherentWith S τ ν)
    (χ ψ : S) {a b : ℤ} (ha : (χ : L → ℂ) 1 = (a : ℂ)) (hb : (ψ : L → ℂ) 1 = (b : ℂ)) :
    (b : ℂ) * coherentVal ν χ 1 = (a : ℂ) * coherentVal ν ψ 1 := by
  have hmem : (b • (χ : L → ℂ) - a • (ψ : L → ℂ)) ∈ charSpanZero S := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span χ.2))
      (Submodule.smul_mem _ _ (Submodule.subset_span ψ.2)), ?_⟩
    rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, ha, hb, zsmul_eq_mul, zsmul_eq_mul]
    ring
  set f : charSpanZero S := ⟨_, hmem⟩ with hf
  have hincl : Submodule.inclusion (charSpanZero_le S) f
      = b • (⟨(χ : L → ℂ), Submodule.subset_span χ.2⟩ : Submodule.span ℤ S)
        - a • (⟨(ψ : L → ℂ), Submodule.subset_span ψ.2⟩ : Submodule.span ℤ S) :=
    Subtype.ext (by simp [hf])
  have h0 : ((ν (Submodule.inclusion (charSpanZero_le S) f) : G → ℂ)) 1 = 0 := by
    rw [hν.eq_on_zero f]; exact hτ f
  rw [hincl, map_sub, map_zsmul, map_zsmul] at h0
  have h1 : (b : ℂ) * coherentVal ν χ 1 - (a : ℂ) * coherentVal ν ψ 1 = 0 := by
    simpa [coherentVal] using h0
  linear_combination h1

theorem exists_sign_and_degree_ratio_of_isCoherentWith (hS : S ⊆ Irr L) (hS2 : 2 ≤ S.ncard)
    (hτ : ∀ f : charSpanZero S, (τ f : G → ℂ) 1 = 0) (hν : IsCoherentWith S τ ν) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∃ c : ℝ, 0 < c ∧ ∃ η : S → (G → ℂ),
      Function.Injective η ∧ (∀ χ : S, η χ ∈ Irr G) ∧
      (∀ χ : S, coherentVal ν χ = ε • η χ) ∧
      ∀ χ : S, η χ 1 = (c : ℂ) * (χ : L → ℂ) 1 := by
  classical
  obtain ⟨y, hy⟩ : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  set χ₀ : S := ⟨y, hy⟩ with hχ₀
  choose ε hε η hηIrr hcoh using fun χ : S =>
    mem_signedIrr_iff_exists_sign.1 (coherentVal_mem_signedIrr hS hν χ)
  have hσex : ∀ χ : S, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (s : ℂ) = ε χ := by
    intro χ
    rcases hε χ with h | h
    · exact ⟨1, Or.inl rfl, by simp [h]⟩
    · exact ⟨-1, Or.inr rfl, by simp [h]⟩
  choose σ hσ hσc using hσex
  have haex : ∀ χ : S, ∃ n : ℕ, 0 < n ∧ (χ : L → ℂ) 1 = (n : ℂ) := by
    intro χ
    obtain ⟨n, hn, hn1, -⟩ := Irr.exists_degree (hS χ.2)
    exact ⟨n, hn, hn1⟩
  choose a ha ha1 using haex
  have hdex : ∀ χ : S, ∃ n : ℕ, 0 < n ∧ η χ 1 = (n : ℂ) := by
    intro χ
    obtain ⟨n, hn, hn1, -⟩ := Irr.exists_degree (hηIrr χ)
    exact ⟨n, hn, hn1⟩
  choose d hd hd1 using hdex
  have hu : ∀ ψ : S, coherentVal ν ψ 1 = ε ψ * (d ψ : ℂ) := by
    intro ψ; rw [hcoh ψ]; simp [hd1 ψ]
  have key : ∀ χ : S, (a χ₀ : ℤ) * σ χ * d χ = (a χ : ℤ) * σ χ₀ * d χ₀ := by
    intro χ
    have h := apply_one_mul_coherentVal_apply_one hτ hν χ χ₀
      (a := (a χ : ℤ)) (b := (a χ₀ : ℤ)) (by push_cast; exact ha1 χ) (by push_cast; exact ha1 χ₀)
    rw [hu χ, hu χ₀, ← hσc χ, ← hσc χ₀] at h
    have hc : (((a χ₀ : ℤ) * σ χ * d χ : ℤ) : ℂ) = (((a χ : ℤ) * σ χ₀ * d χ₀ : ℤ) : ℂ) := by
      push_cast at h ⊢; linear_combination h
    exact_mod_cast hc
  have hpos : ∀ χ : S, 0 < (a χ : ℤ) ∧ 0 < (d χ : ℤ) := fun χ =>
    ⟨by exact_mod_cast ha χ, by exact_mod_cast hd χ⟩
  have hsame : ∀ χ : S, σ χ = σ χ₀ := by
    intro χ
    have hk := key χ
    obtain ⟨ha0, hd0⟩ := hpos χ₀
    obtain ⟨ha', hd'⟩ := hpos χ
    rcases hσ χ with h1 | h1 <;> rcases hσ χ₀ with h2 | h2
    · rw [h1, h2]
    · rw [h1, h2] at hk; exact absurd hk (by nlinarith [mul_pos ha0 hd', mul_pos ha' hd0])
    · rw [h1, h2] at hk; exact absurd hk (by nlinarith [mul_pos ha0 hd', mul_pos ha' hd0])
    · rw [h1, h2]
  have hprod : ∀ χ : S, (a χ₀ : ℤ) * d χ = (a χ : ℤ) * d χ₀ := by
    intro χ
    have hk := key χ
    rw [hsame χ] at hk
    rcases hσ χ₀ with h | h <;> rw [h] at hk <;> linarith
  have hεeq : ∀ χ : S, ε χ = ε χ₀ := fun χ => by rw [← hσc χ, ← hσc χ₀, hsame χ]
  refine ⟨ε χ₀, hε χ₀, (d χ₀ : ℝ) / (a χ₀ : ℝ),
    div_pos (by exact_mod_cast hd χ₀) (by exact_mod_cast ha χ₀), η, ?_, hηIrr,
    fun χ => by rw [hcoh χ, hεeq χ], fun χ => ?_⟩
  · intro χ ψ h
    refine coherentVal_injective hν ?_
    rw [hcoh χ, hcoh ψ, hεeq χ, hεeq ψ, h]
  · rw [hd1 χ, ha1 χ]
    have hc : ((a χ₀ : ℕ) : ℂ) * (d χ : ℂ) = ((a χ : ℕ) : ℂ) * (d χ₀ : ℂ) := by
      exact_mod_cast hprod χ
    have hac : ((a χ₀ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (ha χ₀).ne'
    push_cast
    field_simp
    linear_combination hc

end CFSG.FeitThompson

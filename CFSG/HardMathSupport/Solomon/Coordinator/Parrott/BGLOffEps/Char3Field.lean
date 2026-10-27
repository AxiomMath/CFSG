module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUFieldFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUCoreConj
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUQuad

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Char3

open Module CFSG.ClassicalGroups.Unitary CFSG.HardMathSupport.Solomon.Coordinator.BGL

variable {K : Type} [Field K] [Finite K] {ι ρ : K ≃+* K}

structure FieldHypAny (ι ρ : K ≃+* K) : Prop where
  hι : IsUnitaryInvolution ι
  hρ3 : orderOf (ρ : RingAut K) = 3
  hcomm : ∀ x, ρ (ι x) = ι (ρ x)
  hq8 : Nat.card (Efix ι) ≠ 8

namespace FieldHypAny

variable (FH : FieldHypAny ι ρ)
include FH

theorem counts : Nat.card (Efix ι) = Nat.card (kfix ι ρ) ^ 3 ∧
    Nat.card (Efix ρ) = Nat.card (kfix ι ρ) ^ 2 ∧ Nat.card K = Nat.card (Efix ι) ^ 2 :=
  galois_counts ι ρ FH.hι.invol FH.hι.exists_ne FH.hρ3 FH.hcomm

theorem card_k_ge : 3 ≤ Nat.card (kfix ι ρ) := by
  have h1 : 1 < Nat.card (kfix ι ρ) := Finite.one_lt_card
  have h2 : Nat.card (kfix ι ρ) ≠ 2 := by
    intro h
    apply FH.hq8
    rw [FH.counts.1, h]
    norm_num
  omega

theorem exists_irr : ∃ z : K, ρ z = z ∧ ι z ≠ z := by
  by_contra hcon
  push Not at hcon
  have hle : Efix ρ ≤ kfix ι ρ := by
    intro z hz
    rw [kfix, Subfield.mem_inf]
    exact ⟨mem_Efix.mpr (hcon z (mem_Efix.mp hz)), hz⟩
  have hinj : Function.Injective (Subfield.inclusion hle) := by
    intro x y h
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [FH.counts.2.1] at h1
  have h2 : 1 < Nat.card (kfix ι ρ) := Finite.one_lt_card
  nlinarith

theorem exists_k : ∃ r : K, ρ r = r ∧ ι r = r ∧ r ≠ 0 ∧ r ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have h3 := FH.card_k_ge
  have h01 : ∀ r : kfix ι ρ, (r : K) = 0 ∨ (r : K) = 1 := fun r => by
    by_cases h0 : (r : K) = 0
    · exact Or.inl h0
    · exact Or.inr (hcon r (Subfield.mem_inf.mp r.2).2 (Subfield.mem_inf.mp r.2).1 h0)
  have hinj : Function.Injective (fun r : kfix ι ρ => decide ((r : K) = 1)) := by
    intro x y h
    simp only [decide_eq_decide] at h
    apply Subtype.ext
    rcases h01 x with hx | hx <;> rcases h01 y with hy | hy <;> simp_all
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

omit [Finite K] in
theorem exists_c₀ : ∃ c : K, c ≠ 0 ∧ ρ c = c ∧ ι c = -c := by
  obtain ⟨τ, hτ0, hτ⟩ := FH.hι.exists_traceZero
  have hστ : ι τ = -τ := by linear_combination hτ
  have hρ3 := rho3_apply ρ FH.hρ3
  have hρ3' : ∀ x, ρ (ρ (ρ x)) = x := hρ3
  refine ⟨τ * ρ τ * ρ (ρ τ), ?_, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero hτ0 ((map_ne_zero ρ).mpr hτ0))
      ((map_ne_zero ρ).mpr ((map_ne_zero ρ).mpr hτ0))
  · rw [map_mul, map_mul, hρ3' τ]
    ring
  · have e1 : ι (ρ τ) = -ρ τ := by rw [← FH.hcomm, hστ, map_neg]
    have e2 : ι (ρ (ρ τ)) = -ρ (ρ τ) := by rw [← FH.hcomm, e1, map_neg]
    rw [map_mul, map_mul, hστ, e1, e2]
    ring

omit [Finite K] in
theorem exists_u : ∃ u : K, ρ u = u ∧ ι u * u = -1 := by
  obtain ⟨u₀, hu₀⟩ := FH.hι.exists_norm_neg_one
  have hρ3' : ∀ x, ρ (ρ (ρ x)) = x := rho3_apply ρ FH.hρ3
  have hN : ∀ x, ρ (ι x * x) = ι (ρ x) * ρ x := fun x => by rw [map_mul, FH.hcomm]
  have h1 : ι (ρ u₀) * ρ u₀ = -1 := by rw [← hN, hu₀, map_neg, map_one]
  have h2 : ι (ρ (ρ u₀)) * ρ (ρ u₀) = -1 := by rw [← hN, h1, map_neg, map_one]
  refine ⟨u₀ * ρ u₀ * ρ (ρ u₀), ?_, ?_⟩
  · rw [map_mul, map_mul, hρ3' u₀]
    ring
  · have e : ι (u₀ * ρ u₀ * ρ (ρ u₀)) * (u₀ * ρ u₀ * ρ (ρ u₀)) =
        (ι u₀ * u₀) * (ι (ρ u₀) * ρ u₀) * (ι (ρ (ρ u₀)) * ρ (ρ u₀)) := by
      rw [map_mul, map_mul]; ring
    rw [e, hu₀, h1, h2]
    norm_num

theorem uctx : UCtx ι ρ where
  ιinv := FH.hι.invol
  ρ3 := rho3_apply ρ FH.hρ3
  comm := FH.hcomm
  c₀ := FH.exists_c₀
  r₂ := by
    obtain ⟨r, h1, h2, h3, h4⟩ := FH.exists_k
    exact ⟨r, h3, h4, h1, h2⟩

theorem exists_ω : ∃ ω : K, ρ ω = ω ∧ ι ω * ω = 1 ∧ ω ≠ 1 := by
  obtain ⟨z, hρz, hz⟩ := FH.exists_irr
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hz (map_zero ι)
  have hιz0 : ι z ≠ 0 := by
    intro h
    apply hz0
    rw [← FH.hι.invol z, h, map_zero]
  refine ⟨ι z / z, ?_, ?_, ?_⟩
  · rw [map_div₀, FH.hcomm, hρz]
  · rw [map_div₀, FH.hι.invol]
    field_simp
  · intro h
    apply hz
    rw [div_eq_one_iff_eq hz0] at h
    exact h

theorem hcard : Nat.card (Efix ι) = Nat.card (FieldHyp.kE ι ρ) ^ 3 := by
  rw [FieldHyp.card_kE]; exact FH.counts.1

theorem hk2 : Nat.card (FieldHyp.kE ι ρ) ≠ 2 := by
  have h := FH.card_k_ge
  rw [FieldHyp.card_kE]
  omega

theorem span : ∀ z : K, z ∈ AddSubgroup.closure
    {z | ∃ t : K, ι t = t ∧ t ≠ 0 ∧ ∃ μ : K, ρ μ = μ ∧ z = t * μ} := by
  obtain ⟨z₀, hρz, hz₀⟩ := FH.exists_irr
  have hrank : finrank (Efix ι) K = 2 := by
    rw [finrank_efix, orderOf_of_involution ι FH.hι.invol FH.hι.exists_ne]
  have hli : LinearIndependent (Efix ι) ![(1 : K), z₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Subfield.smul_def, smul_eq_mul, mul_one] at hst
    have ht : t = 0 := by
      by_contra ht0
      have ht0' : (t : K) ≠ 0 := fun h => ht0 (Subtype.ext h)
      apply hz₀
      have : z₀ = -(s : K) / t := by field_simp; linear_combination hst
      rw [this, map_div₀, map_neg, (mem_Efix.mp s.2), (mem_Efix.mp t.2)]
    subst ht
    refine ⟨?_, rfl⟩
    simpa using hst
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hrank])
  intro z
  have hz : z ∈ Submodule.span (Efix ι) (Set.range ![(1 : K), z₀]) := by
    rw [hspan]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hz
  obtain ⟨c, hc⟩ := hz
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Subfield.smul_def,
    smul_eq_mul, mul_one] at hc
  rw [← hc]
  have hmem : ∀ (e : Efix ι) (μ : K), ρ μ = μ →
      ((e : K) * μ) ∈ AddSubgroup.closure
        {z | ∃ t : K, ι t = t ∧ t ≠ 0 ∧ ∃ μ : K, ρ μ = μ ∧ z = t * μ} := by
    intro e μ hμ
    by_cases he : (e : K) = 0
    · rw [he, zero_mul]; exact zero_mem _
    · exact AddSubgroup.subset_closure ⟨e, mem_Efix.mp e.2, he, μ, hμ, rfl⟩
  have h1 := hmem (c 0) 1 (map_one ρ)
  have h2 := hmem (c 1) z₀ hρz
  rw [mul_one] at h1
  exact add_mem h1 h2

end FieldHypAny

omit [Finite K] in
theorem exists_rational_trace_any (C : UCtx ι ρ) (hι : IsUnitaryInvolution ι) {d : K}
    (hd : ρ d = d) (hdι : ι d = d) : ∃ c : K, ρ c = c ∧ c + ι c = d := by
  by_cases h2 : (2 : K) = 0
  · have three : (3 : K) ≠ 0 := by
      intro h3
      exact one_ne_zero (by linear_combination h3 - h2 : (1 : K) = 0)
    exact exists_rational_trace C hι three hd hdι
  · refine ⟨d / 2, ?_, ?_⟩
    · rw [map_div₀, hd, map_ofNat]
    · rw [map_div₀, hdι, map_ofNat]
      field_simp
      ring

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Char3

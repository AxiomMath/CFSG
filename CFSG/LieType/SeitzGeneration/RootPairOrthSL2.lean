module

public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
public import CFSG.LieType.SeitzGeneration.RootPairSL2

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP

namespace RootPairOrth

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_line_of_irrational [Finite K] {k : Subfield K}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p)
    (hk3 : 3 ≤ Nat.card k) {H : Subgroup (V ≃ₗ[K] V)} {x y c₁ c₂ : V} (hx : Q x = 0)
    (hy : Q y = 0) (hxy : polar Q x y = 0) (hc₁ : Q c₁ = 0) (hc₂ : Q c₂ = 0)
    (hc₁₂ : polar Q c₁ c₂ = 0) {μ : K}
    (hHx : ∀ t ∈ k, eichler Q x (t • y) ∈ H)
    (hHc : ∀ t ∈ k, eichler Q c₁ ((μ⁻¹ * t) • c₂) ∈ H)
    (hirr : μ⁻¹ * (polar Q x c₁ * polar Q y c₂ - polar Q x c₂ * polar Q y c₁) ∉ k) (t : K) :
    eichler Q x (t • y) ∈ H := by
  set a := polar Q x c₁ with ha
  set b := polar Q x c₂ with hb
  set c := polar Q y c₁ with hc
  set d := polar Q y c₂ with hd
  set Δ := a * d - b * c with hΔ
  have hΔ0 : Δ ≠ 0 := fun h => hirr (by rw [h, mul_zero]; exact k.zero_mem)
  set f : V := (d / Δ) • c₁ + (-c / Δ) • c₂ with hf
  set f' : V := (-b / Δ) • c₁ + (a / Δ) • c₂ with hf'
  have hfQ : Q f = 0 := Q_plane hc₁ hc₂ hc₁₂ _ _
  have hf'Q : Q f' = 0 := Q_plane hc₁ hc₂ hc₁₂ _ _
  have hxf : polar Q x f = 1 := by
    rw [hf, polar_add_right, polar_smul_right_eq, polar_smul_right_eq]
    field_simp
    rw [hΔ]
    ring
  have hyf : polar Q y f = 0 := by
    rw [hf, polar_add_right, polar_smul_right_eq, polar_smul_right_eq]
    field_simp
    ring
  have hxf' : polar Q x f' = 0 := by
    rw [hf', polar_add_right, polar_smul_right_eq, polar_smul_right_eq]
    field_simp
    ring
  have hyf' : polar Q y f' = 1 := by
    rw [hf', polar_add_right, polar_smul_right_eq, polar_smul_right_eq]
    field_simp
    rw [hΔ]
    ring
  have hff' : polar Q f f' = 0 := polar_plane hc₁ hc₂ hc₁₂ _ _ _ _
  let P : HypPair Q := ⟨x, f, hx, hfQ, hxf⟩
  let P' : HypPair Q := ⟨y, f', hy, hf'Q, hyf'⟩
  have hPP : P.Orth P' :=
    ⟨hxy, hxf', by rw [polar_comm]; exact hyf, hff'⟩
  set M : Subgroup (SpecialLinearGroup (Fin 2) K) := H.comap (quadHom hPP) with hM
  have hu : ∀ s ∈ k, u2 (s * (-1)) ∈ M := by
    intro s hs
    change quadHom hPP (u2 (s * (-1))) ∈ H
    rw [quadHom_u2]
    have h1 : -(s * (-1)) = s := by ring
    rw [h1]
    exact hHx s hs
  have hl : ∀ s ∈ k, l2 (s * (μ⁻¹ * Δ)) ∈ M := by
    intro s hs
    change quadHom hPP (l2 (s * (μ⁻¹ * Δ))) ∈ H
    rw [quadHom_l2]
    change eichler Q f ((s * (μ⁻¹ * Δ)) • f') ∈ H
    rw [hf, hf', eichler_plane_change hc₁ hc₂ hc₁₂]
    have h2 : (s * (μ⁻¹ * Δ)) * ((d / Δ) * (a / Δ) - (-c / Δ) * (-b / Δ)) = μ⁻¹ * s := by
      field_simp
      rw [hΔ]
      ring
    rw [h2]
    exact hHc s hs
  have hαβ : (-1 : K) * (μ⁻¹ * Δ) ∉ k := by
    intro h
    apply hirr
    have := k.neg_mem h
    simpa using this
  have hM1 : M = ⊤ := sl2_eq_top_of_root_pair hp hp2 hK hk3 hαβ hu hl
  have h3 : u2 (-t) ∈ M := by rw [hM1]; trivial
  change quadHom hPP (u2 (-t)) ∈ H at h3
  rw [quadHom_u2, neg_neg] at h3
  exact h3

end RootPairOrth

end CFSG.LieType.SeitzGeneration

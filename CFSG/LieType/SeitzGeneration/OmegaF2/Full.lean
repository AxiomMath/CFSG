module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Line
public import CFSG.LieType.SeitzGeneration.OmegaF2.BridgeGen

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.RootPairOrth Matrix

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem polar_right_comb (u : V) (l₁ l₂ : K) (c₁ c₂ : V) :
    polar Q u (l₁ • c₁ + l₂ • c₂) = l₁ * polar Q u c₁ + l₂ * polar Q u c₂ := by
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq]

private theorem eichler_dual_plane {c₁ c₂ : V} (hc₁ : Q c₁ = 0) (hc₂ : Q c₂ = 0)
    (hc₁₂ : polar Q c₁ c₂ = 0) {s l₁ l₂ m₁ m₂ : K} (h : s * (l₁ * m₂ - l₂ * m₁) = 1) :
    eichler Q (l₁ • c₁ + l₂ • c₂) (s • (m₁ • c₁ + m₂ • c₂)) = eichler Q c₁ c₂ := by
  rw [eichler_plane_change hc₁ hc₂ hc₁₂, h, one_smul]

theorem exists_hypPairs {x y c₁ c₂ : V} (hx : Q x = 0) (hy : Q y = 0) (hxy : polar Q x y = 0)
    (hc₁ : Q c₁ = 0) (hc₂ : Q c₂ = 0) (hc₁₂ : polar Q c₁ c₂ = 0)
    (hΔ : pairDet Q c₁ c₂ x y ≠ 0) :
    ∃ (P P' : HypPair Q), P.Orth P' ∧ P.e = x ∧ P'.e = y ∧
      (∃ a b a' b' : K, P.f = a • c₁ + b • c₂ ∧ P'.f = a' • c₁ + b' • c₂) ∧
      eichler Q P.f (pairDet Q c₁ c₂ x y • P'.f) = eichler Q c₁ c₂ := by
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : K, pairDet Q c₁ c₂ x y = Δ := ⟨_, rfl⟩
  have hΔ0 : Δ ≠ 0 := by rw [← hΔdef]; exact hΔ
  have hΔexp : Δ = polar Q x c₁ * polar Q y c₂ - polar Q x c₂ * polar Q y c₁ := hΔdef.symm
  have hΔi : Δ * Δ⁻¹ = 1 := mul_inv_cancel₀ hΔ0
  rw [hΔdef]
  obtain ⟨f, hf⟩ : ∃ f : V, f = (polar Q y c₂ / Δ) • c₁ + (-polar Q y c₁ / Δ) • c₂ :=
    ⟨_, rfl⟩
  obtain ⟨f', hf'⟩ : ∃ f' : V, f' = (-polar Q x c₂ / Δ) • c₁ + (polar Q x c₁ / Δ) • c₂ :=
    ⟨_, rfl⟩
  have hfQ : Q f = 0 := by rw [hf]; exact Q_plane hc₁ hc₂ hc₁₂ _ _
  have hf'Q : Q f' = 0 := by rw [hf']; exact Q_plane hc₁ hc₂ hc₁₂ _ _
  have hxf : polar Q x f = 1 := by
    rw [hf, polar_right_comb]
    linear_combination (-Δ⁻¹) * hΔexp + hΔi
  have hyf' : polar Q y f' = 1 := by
    rw [hf', polar_right_comb]
    linear_combination (-Δ⁻¹) * hΔexp + hΔi
  have hxf' : polar Q x f' = 0 := by
    rw [hf', polar_right_comb]
    ring
  have hyf : polar Q y f = 0 := by
    rw [hf, polar_right_comb]
    ring
  have hff' : polar Q f f' = 0 := by
    rw [hf, hf']
    exact polar_plane hc₁ hc₂ hc₁₂ _ _ _ _
  refine ⟨⟨x, f, hx, hfQ, hxf⟩, ⟨y, f', hy, hf'Q, hyf'⟩, ⟨hxy, hxf', ?_, hff'⟩, rfl, rfl,
    ⟨polar Q y c₂ / Δ, -polar Q y c₁ / Δ, -polar Q x c₂ / Δ, polar Q x c₁ / Δ, hf, hf'⟩, ?_⟩
  · rw [polar_comm]
    exact hyf
  · show eichler Q f (Δ • f') = eichler Q c₁ c₂
    rw [hf, hf']
    exact eichler_dual_plane hc₁ hc₂ hc₁₂
      (by linear_combination (Δ * Δ⁻¹ + 1) * hΔi - (Δ⁻¹ ^ 2 * Δ) * hΔexp)

theorem radical_vector_perp {x y z : V} (hx : Q x = 0) (hy : Q y = 0) (hz : Q z = 0)
    (hxy : polar Q x y = 0) (hxz : polar Q x z = 0) (hyz : polar Q y z = 0) (α β : K) :
    Q (z + α • x + β • y) = 0 ∧ polar Q (z + α • x + β • y) x = 0 ∧
      polar Q (z + α • x + β • y) y = 0 := by
  have hzx : polar Q z x = 0 := by rw [polar_comm]; exact hxz
  have hzy : polar Q z y = 0 := by rw [polar_comm]; exact hyz
  have hyx : polar Q y x = 0 := by rw [polar_comm]; exact hxy
  have hxx : polar Q x x = 0 := polar_self_eq_zero hx
  have hyy : polar Q y y = 0 := polar_self_eq_zero hy
  refine ⟨?_, ?_, ?_⟩
  · simp only [QuadraticMap.map_add, map_smul_eq_sq, polar_add_left, polar_add_right,
      polar_smul_left_eq, polar_smul_right_eq, hx, hy, hz, hxy, hzx, hzy, hxx, hyy, hyx,
      mul_zero, zero_add, add_zero]
  · simp only [polar_add_left, polar_smul_left_eq, hzx, hxx, hyx, mul_zero, add_zero]
  · simp only [polar_add_left, polar_smul_left_eq, hzy, hxy, hyy, mul_zero, add_zero]

theorem exists_full_line [Finite K] [CharP K 2] {k : Subfield K}
    (hk : Nat.card k = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = Nat.card k ^ p) {H : Subgroup (V ≃ₗ[K] V)} {x y z c₁ c₂ : V}
    (hx : Q x = 0) (hy : Q y = 0) (hz : Q z = 0) (hxy : polar Q x y = 0) (hxz : polar Q x z = 0)
    (hyz : polar Q y z = 0) (hc₁ : Q c₁ = 0) (hc₂ : Q c₂ = 0) (hc₁₂ : polar Q c₁ c₂ = 0)
    (hΔ : pairDet Q c₁ c₂ x y ≠ 0)
    (hαβ : ¬ (pairDet Q c₁ c₂ y z / pairDet Q c₁ c₂ x y ∈ k ∧
      pairDet Q c₁ c₂ z x / pairDet Q c₁ c₂ x y ∈ k))
    (hHxy : eichler Q x y ∈ H) (hHxz : eichler Q x z ∈ H) (hHyz : eichler Q y z ∈ H)
    (hHc : eichler Q c₁ c₂ ∈ H) :
    ∃ a₁ a₂ : K, (a₁ ≠ 0 ∨ a₂ ≠ 0) ∧ ∀ t : K,
      eichler Q (z + (pairDet Q c₁ c₂ y z / pairDet Q c₁ c₂ x y) • x +
        (pairDet Q c₁ c₂ z x / pairDet Q c₁ c₂ x y) • y) (t • (a₁ • x + a₂ • y)) ∈ H := by
  set α₀ : K := pairDet Q c₁ c₂ y z / pairDet Q c₁ c₂ x y
  set β₀ : K := pairDet Q c₁ c₂ z x / pairDet Q c₁ c₂ x y
  set r₀ : V := z + α₀ • x + β₀ • y with hr₀
  obtain ⟨P, P', horth, hPe, hP'e, ⟨_, _, _, _, hPf, hP'f⟩, hfe⟩ :=
    exists_hypPairs hx hy hxy hc₁ hc₂ hc₁₂ hΔ
  have hQr : Q r₀ = 0 := (radical_vector_perp hx hy hz hxy hxz hyz α₀ β₀).1
  have hrx : polar Q r₀ x = 0 := (radical_vector_perp hx hy hz hxy hxz hyz α₀ β₀).2.1
  have hry : polar Q r₀ y = 0 := (radical_vector_perp hx hy hz hxy hxz hyz α₀ β₀).2.2
  have hc1r : polar Q r₀ c₁ = 0 := (polar_radical_vector (z := z) hΔ).1
  have hc2r : polar Q r₀ c₂ = 0 := (polar_radical_vector (z := z) hΔ).2
  have hr : PerpData P P' r₀ :=
    { Q_r := hQr
      e := by rw [hPe]; exact hrx
      f := by rw [hPf, polar_right_comb, hc1r, hc2r, mul_zero, mul_zero, add_zero]
      e' := by rw [hP'e]; exact hry
      f' := by rw [hP'f, polar_right_comb, hc1r, hc2r, mul_zero, mul_zero, add_zero] }
  have hid : r₀ + α₀ • x + β₀ • y = z := by
    have h2a : α₀ + α₀ = 0 := CharTwo.add_self_eq_zero α₀
    have h2b : β₀ + β₀ = 0 := CharTwo.add_self_eq_zero β₀
    rw [hr₀]
    calc z + α₀ • x + β₀ • y + α₀ • x + β₀ • y
        = z + (α₀ + α₀) • x + (β₀ + β₀) • y := by module
      _ = z := by rw [h2a, h2b, zero_smul, zero_smul, add_zero, add_zero]
  have hTC := twistSet_closed horth hr H
  have h1 : ((0 : Matrix (Fin 2) (Fin 2) K), u2 (1 : K)) ∈ twistSet horth r₀ H := by
    show eichler Q r₀ (quadEmb P P' 0) * quadHom horth (u2 1) ∈ H
    rw [theta_zero_u2, one_smul, hPe, hP'e]
    exact hHxy
  have hx' : ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K), u2 β₀) ∈ twistSet horth r₀ H := by
    show eichler Q r₀ (quadEmb P P' !![1, 0; 0, 0]) * quadHom horth (u2 β₀) ∈ H
    rw [← eichler_e_eq_theta horth hr α₀ β₀, hPe, hP'e, hid]
    exact hHxz
  have hy' : ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K), u2 α₀) ∈ twistSet horth r₀ H := by
    show eichler Q r₀ (quadEmb P P' !![0, 1; 0, 0]) * quadHom horth (u2 α₀) ∈ H
    rw [← eichler_e'_eq_theta horth hr α₀ β₀, hPe, hP'e, hid]
    exact hHyz
  have hl' : ((0 : Matrix (Fin 2) (Fin 2) K), l2 (pairDet Q c₁ c₂ x y)) ∈
      twistSet horth r₀ H := by
    show eichler Q r₀ (quadEmb P P' 0) * quadHom horth (l2 (pairDet Q c₁ c₂ x y)) ∈ H
    rw [theta_zero_l2, hfe]
    exact hHc
  obtain ⟨a₁, a₂, ha, hall⟩ :=
    exists_root_line hk hp hp2 hK (not_and_or.mp hαβ) hΔ hTC h1 hx' hy' hl'
  refine ⟨a₁, a₂, ha, fun t => ?_⟩
  have ht : eichler Q r₀ (quadEmb P P' !![t * a₁, t * a₂; 0, 0]) * quadHom horth 1 ∈ H :=
    hall t
  rw [_root_.map_one, _root_.mul_one, quadEmb_t_row, hPe, hP'e] at ht
  exact ht

end CFSG.LieType.SeitzGeneration.OmegaF2

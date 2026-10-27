module

public import CFSG.CGT.Stroth77.Extension25Common

public section

namespace CFSG.CGT.Stroth77

theorem rho_apply_gens_t230 (s : ℕ) (hs : 1 ≤ s) (i j l : ℤ) :
    (StrothTypeIndex.t230 s hs).action.φρ
        (i • gen (StrothTypeIndex.t230 s hs).k 0 + j • gen (StrothTypeIndex.t230 s hs).k 1 +
          l • gen (StrothTypeIndex.t230 s hs).k 2) =
      (i - l) • gen (StrothTypeIndex.t230 s hs).k 0 +
        (-l) • gen (StrothTypeIndex.t230 s hs).k 1 +
          (j - l) • gen (StrothTypeIndex.t230 s hs).k 2 := by
  rw [matAct_zsmul_gens]
  simp [StrothTypeIndex.action, Type230.actionPaper, Type230.action, SigmaFourAction.ofMatEq,
    Type230.ρM, ofCols_apply, sub_eq_add_neg]

theorem u_apply_gens_t230 (s : ℕ) (hs : 1 ≤ s) (i j l : ℤ) :
    (StrothTypeIndex.t230 s hs).action.φu
        (i • gen (StrothTypeIndex.t230 s hs).k 0 + j • gen (StrothTypeIndex.t230 s hs).k 1 +
          l • gen (StrothTypeIndex.t230 s hs).k 2) =
      ((-1 + 2 * 2 ^ s) * i + (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * j +
          (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * (1 - 2 * 2 ^ s) * l) •
          gen (StrothTypeIndex.t230 s hs).k 0 +
        l • gen (StrothTypeIndex.t230 s hs).k 1 + j • gen (StrothTypeIndex.t230 s hs).k 2 := by
  rw [matAct_zsmul_gens]
  simp only [StrothTypeIndex.action, Type230.actionPaper, Type230.action,
    SigmaFourAction.ofMatEq, Type230.uM, uMat, ofCols_apply]
  congr 2
  · congr 1
    simp
    ring
  · congr 1
    simp
  · congr 1
    simp

theorem rho_fixed_mod_two_t230 (s : ℕ) (hs : 1 ≤ s) {x z : Torus (StrothTypeIndex.t230 s hs).k}
    (h : (StrothTypeIndex.t230 s hs).action.φρ x - x = 2 • z) :
    ∃ (p : ℤ) (w : Torus (StrothTypeIndex.t230 s hs).k),
      x = p • gen (StrothTypeIndex.t230 s hs).k 0 + 2 • w := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ x
  obtain ⟨z0, z1, z2, rfl⟩ := torus_eq_zsmul_gens _ z
  rw [rho_apply_gens_t230, nsmul_zsmul_gens] at h
  have e : (i - l) • gen (StrothTypeIndex.t230 s hs).k 0 +
        (-l) • gen (StrothTypeIndex.t230 s hs).k 1 +
        (j - l) • gen (StrothTypeIndex.t230 s hs).k 2 -
      (i • gen (StrothTypeIndex.t230 s hs).k 0 + j • gen (StrothTypeIndex.t230 s hs).k 1 +
        l • gen (StrothTypeIndex.t230 s hs).k 2) =
      (-l) • gen (StrothTypeIndex.t230 s hs).k 0 +
        (-l - j) • gen (StrothTypeIndex.t230 s hs).k 1 +
        (j - 2 * l) • gen (StrothTypeIndex.t230 s hs).k 2 := by
    module
  rw [e] at h
  obtain ⟨h0, h1, -⟩ := zsmul_gens_dvd_of_eq h
  have hk0 : (2 : ℤ) ∣ 2 ^ (StrothTypeIndex.t230 s hs).k 0 :=
    dvd_pow_self 2 (show s + 2 ≠ 0 by omega)
  have hk1 : (2 : ℤ) ∣ 2 ^ (StrothTypeIndex.t230 s hs).k 1 :=
    dvd_pow_self 2 (show s + 4 ≠ 0 by omega)
  have hl : (2 : ℤ) ∣ l := by
    have := dvd_trans hk0 h0
    omega
  have hj : (2 : ℤ) ∣ j := by
    have := dvd_trans hk1 h1
    omega
  obtain ⟨l', rfl⟩ := hl
  obtain ⟨j', rfl⟩ := hj
  exact ⟨i, j' • gen (StrothTypeIndex.t230 s hs).k 1 + l' • gen (StrothTypeIndex.t230 s hs).k 2,
    by module⟩

theorem false_of_int_u_cocycle_t230 {s : ℕ} (hs : 1 ≤ s) {F p w0 w1 w2 y0 y1 y2 : ℤ}
    (hp : Odd p)
    (c1 : (2 : ℤ) ^ (s + 2) ∣ 2 * y0 - ((-1 + 2 * 2 ^ s) * (p + 2 * w0) +
      (-2 * F + 2 * 2 ^ s) * (2 * w1) + (-2 * F + 2 * 2 ^ s) * (1 - 2 * 2 ^ s) * (2 * w2) -
      (p + 2 * w0)))
    (u1 : (2 : ℤ) ^ (s + 2) ∣ -y0 - ((-1 + 2 * 2 ^ s) * y0 + (-2 * F + 2 * 2 ^ s) * y1 +
      (-2 * F + 2 * 2 ^ s) * (1 - 2 * 2 ^ s) * y2))
    (u2 : (2 : ℤ) ^ (s + 4) ∣ -y1 - y2) : False := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨t, ht⟩ := u2
  obtain ⟨q, hq⟩ := u1
  obtain ⟨r, hr⟩ := c1
  have hPne : (2 : ℤ) * 2 ^ (s' + 1) ≠ 0 := by positivity
  have hy0 : -y0 - (-2 * F + 2 * 2 ^ (s' + 1)) * y1 +
      8 * t * ((-2 * F + 2 * 2 ^ (s' + 1)) * (1 - 2 * 2 ^ (s' + 1))) - 2 * q = 0 := by
    have h : (2 : ℤ) * 2 ^ (s' + 1) * (-y0 - (-2 * F + 2 * 2 ^ (s' + 1)) * y1 +
        8 * t * ((-2 * F + 2 * 2 ^ (s' + 1)) * (1 - 2 * 2 ^ (s' + 1))) - 2 * q) = 0 := by
      linear_combination hq - (-2 * F + 2 * 2 ^ (s' + 1)) * (1 - 2 * 2 ^ (s' + 1)) * ht
    exact (mul_eq_zero.mp h).resolve_left hPne
  have h2p : ∃ X : ℤ, 2 * p = 4 * X := by
    refine ⟨2 ^ (s' + 1) * r + (2 ^ (s' + 1) - F) * y1 -
      8 * t * (2 ^ (s' + 1) - F) * (1 - 2 * 2 ^ (s' + 1)) + q - w0 + 2 ^ s' * p +
      2 ^ (s' + 1) * w0 + (2 ^ (s' + 1) - F) * w1 +
      (2 ^ (s' + 1) - F) * (1 - 2 * 2 ^ (s' + 1)) * w2, ?_⟩
    linear_combination hr + 2 * hy0
  obtain ⟨X, hX⟩ := h2p
  obtain ⟨r', hr'⟩ := hp
  omega

theorem false_of_u_cocycle_t230 (s : ℕ) (hs : 1 ≤ s) {p : ℤ} (hp : Odd p)
    {w y : Torus (StrothTypeIndex.t230 s hs).k}
    (h1 : (StrothTypeIndex.t230 s hs).action.φu (p • gen (StrothTypeIndex.t230 s hs).k 0 + 2 • w) -
      (p • gen (StrothTypeIndex.t230 s hs).k 0 + 2 • w) = 2 • y)
    (h2 : (StrothTypeIndex.t230 s hs).action.φu y = -y) : False := by
  obtain ⟨w0, w1, w2, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨y0, y1, y2, rfl⟩ := torus_eq_zsmul_gens _ y
  have ex : p • gen (StrothTypeIndex.t230 s hs).k 0 +
      2 • (w0 • gen (StrothTypeIndex.t230 s hs).k 0 + w1 • gen (StrothTypeIndex.t230 s hs).k 1 +
        w2 • gen (StrothTypeIndex.t230 s hs).k 2) =
      (p + 2 * w0) • gen (StrothTypeIndex.t230 s hs).k 0 +
        (2 * w1) • gen (StrothTypeIndex.t230 s hs).k 1 +
        (2 * w2) • gen (StrothTypeIndex.t230 s hs).k 2 := by
    module
  rw [ex, u_apply_gens_t230, nsmul_zsmul_gens] at h1
  have e1 : ((-1 + 2 * 2 ^ s) * (p + 2 * w0) + (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * (2 * w1) +
          (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * (1 - 2 * 2 ^ s) * (2 * w2)) •
          gen (StrothTypeIndex.t230 s hs).k 0 +
        (2 * w2) • gen (StrothTypeIndex.t230 s hs).k 1 +
        (2 * w1) • gen (StrothTypeIndex.t230 s hs).k 2 -
      ((p + 2 * w0) • gen (StrothTypeIndex.t230 s hs).k 0 +
        (2 * w1) • gen (StrothTypeIndex.t230 s hs).k 1 +
        (2 * w2) • gen (StrothTypeIndex.t230 s hs).k 2) =
      ((-1 + 2 * 2 ^ s) * (p + 2 * w0) + (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * (2 * w1) +
          (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * (1 - 2 * 2 ^ s) * (2 * w2) - (p + 2 * w0)) •
          gen (StrothTypeIndex.t230 s hs).k 0 +
        (2 * w2 - 2 * w1) • gen (StrothTypeIndex.t230 s hs).k 1 +
        (2 * w1 - 2 * w2) • gen (StrothTypeIndex.t230 s hs).k 2 := by
    module
  rw [e1] at h1
  obtain ⟨c1, -, -⟩ := zsmul_gens_dvd_of_eq h1
  rw [u_apply_gens_t230] at h2
  have e2 : -(y0 • gen (StrothTypeIndex.t230 s hs).k 0 + y1 • gen (StrothTypeIndex.t230 s hs).k 1 +
        y2 • gen (StrothTypeIndex.t230 s hs).k 2) =
      (-y0) • gen (StrothTypeIndex.t230 s hs).k 0 + (-y1) • gen (StrothTypeIndex.t230 s hs).k 1 +
        (-y2) • gen (StrothTypeIndex.t230 s hs).k 2 := by
    module
  rw [e2] at h2
  obtain ⟨u1, u2, -⟩ := zsmul_gens_dvd_of_eq h2
  exact false_of_int_u_cocycle_t230 hs hp c1 u1 u2


theorem rho_apply_gens_t231 (s : ℕ) (hs : 1 ≤ s) (i j l : ℤ) :
    (StrothTypeIndex.t231 s hs).action.φρ
        (i • gen (StrothTypeIndex.t231 s hs).k 0 + j • gen (StrothTypeIndex.t231 s hs).k 1 +
          l • gen (StrothTypeIndex.t231 s hs).k 2) =
      (i - l) • gen (StrothTypeIndex.t231 s hs).k 0 +
        (-l) • gen (StrothTypeIndex.t231 s hs).k 1 +
          (j - l) • gen (StrothTypeIndex.t231 s hs).k 2 := by
  rw [matAct_zsmul_gens]
  simp [StrothTypeIndex.action, Type231.actionPaper, Type231.action, SigmaFourAction.ofMatEq,
    Type231.ρM, ofCols_apply, sub_eq_add_neg]

theorem u_apply_gens_t231 (s : ℕ) (hs : 1 ≤ s) (i j l : ℤ) :
    (StrothTypeIndex.t231 s hs).action.φu
        (i • gen (StrothTypeIndex.t231 s hs).k 0 + j • gen (StrothTypeIndex.t231 s hs).k 1 +
          l • gen (StrothTypeIndex.t231 s hs).k 2) =
      ((-1 + 2 * 2 ^ s) * i + (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * j +
          (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * (1 - 2 * 2 ^ s) * l) •
          gen (StrothTypeIndex.t231 s hs).k 0 +
        l • gen (StrothTypeIndex.t231 s hs).k 1 + j • gen (StrothTypeIndex.t231 s hs).k 2 := by
  rw [matAct_zsmul_gens]
  simp only [StrothTypeIndex.action, Type231.actionPaper, Type231.action,
    SigmaFourAction.ofMatEq, Type231.uM, uMat, ofCols_apply]
  congr 2
  · congr 1
    simp
    ring
  · congr 1
    simp
  · congr 1
    simp

theorem rho_fixed_mod_two_t231 (s : ℕ) (hs : 1 ≤ s) {x z : Torus (StrothTypeIndex.t231 s hs).k}
    (h : (StrothTypeIndex.t231 s hs).action.φρ x - x = 2 • z) :
    ∃ (p : ℤ) (w : Torus (StrothTypeIndex.t231 s hs).k),
      x = p • gen (StrothTypeIndex.t231 s hs).k 0 + 2 • w := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ x
  obtain ⟨z0, z1, z2, rfl⟩ := torus_eq_zsmul_gens _ z
  rw [rho_apply_gens_t231, nsmul_zsmul_gens] at h
  have e : (i - l) • gen (StrothTypeIndex.t231 s hs).k 0 +
        (-l) • gen (StrothTypeIndex.t231 s hs).k 1 +
        (j - l) • gen (StrothTypeIndex.t231 s hs).k 2 -
      (i • gen (StrothTypeIndex.t231 s hs).k 0 + j • gen (StrothTypeIndex.t231 s hs).k 1 +
        l • gen (StrothTypeIndex.t231 s hs).k 2) =
      (-l) • gen (StrothTypeIndex.t231 s hs).k 0 +
        (-l - j) • gen (StrothTypeIndex.t231 s hs).k 1 +
        (j - 2 * l) • gen (StrothTypeIndex.t231 s hs).k 2 := by
    module
  rw [e] at h
  obtain ⟨h0, h1, -⟩ := zsmul_gens_dvd_of_eq h
  have hk0 : (2 : ℤ) ∣ 2 ^ (StrothTypeIndex.t231 s hs).k 0 :=
    dvd_pow_self 2 (show s + 2 ≠ 0 by omega)
  have hk1 : (2 : ℤ) ∣ 2 ^ (StrothTypeIndex.t231 s hs).k 1 :=
    dvd_pow_self 2 (show s + 4 ≠ 0 by omega)
  have hl : (2 : ℤ) ∣ l := by
    have := dvd_trans hk0 h0
    omega
  have hj : (2 : ℤ) ∣ j := by
    have := dvd_trans hk1 h1
    omega
  obtain ⟨l', rfl⟩ := hl
  obtain ⟨j', rfl⟩ := hj
  exact ⟨i, j' • gen (StrothTypeIndex.t231 s hs).k 1 + l' • gen (StrothTypeIndex.t231 s hs).k 2,
    by module⟩

theorem false_of_u_cocycle_t231 (s : ℕ) (hs : 1 ≤ s) {p : ℤ} (hp : Odd p)
    {w y : Torus (StrothTypeIndex.t231 s hs).k}
    (h1 : (StrothTypeIndex.t231 s hs).action.φu (p • gen (StrothTypeIndex.t231 s hs).k 0 + 2 • w) -
      (p • gen (StrothTypeIndex.t231 s hs).k 0 + 2 • w) = 2 • y)
    (h2 : (StrothTypeIndex.t231 s hs).action.φu y = -y) : False := by
  obtain ⟨w0, w1, w2, rfl⟩ := torus_eq_zsmul_gens _ w
  obtain ⟨y0, y1, y2, rfl⟩ := torus_eq_zsmul_gens _ y
  have ex : p • gen (StrothTypeIndex.t231 s hs).k 0 +
      2 • (w0 • gen (StrothTypeIndex.t231 s hs).k 0 + w1 • gen (StrothTypeIndex.t231 s hs).k 1 +
        w2 • gen (StrothTypeIndex.t231 s hs).k 2) =
      (p + 2 * w0) • gen (StrothTypeIndex.t231 s hs).k 0 +
        (2 * w1) • gen (StrothTypeIndex.t231 s hs).k 1 +
        (2 * w2) • gen (StrothTypeIndex.t231 s hs).k 2 := by
    module
  rw [ex, u_apply_gens_t231, nsmul_zsmul_gens] at h1
  have e1 : ((-1 + 2 * 2 ^ s) * (p + 2 * w0) + (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * (2 * w1) +
          (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * (1 - 2 * 2 ^ s) * (2 * w2)) •
          gen (StrothTypeIndex.t231 s hs).k 0 +
        (2 * w2) • gen (StrothTypeIndex.t231 s hs).k 1 +
        (2 * w1) • gen (StrothTypeIndex.t231 s hs).k 2 -
      ((p + 2 * w0) • gen (StrothTypeIndex.t231 s hs).k 0 +
        (2 * w1) • gen (StrothTypeIndex.t231 s hs).k 1 +
        (2 * w2) • gen (StrothTypeIndex.t231 s hs).k 2) =
      ((-1 + 2 * 2 ^ s) * (p + 2 * w0) + (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * (2 * w1) +
          (-2 * Type120.FV (s + 4) + 2 * 2 ^ s) * (1 - 2 * 2 ^ s) * (2 * w2) - (p + 2 * w0)) •
          gen (StrothTypeIndex.t231 s hs).k 0 +
        (2 * w2 - 2 * w1) • gen (StrothTypeIndex.t231 s hs).k 1 +
        (2 * w1 - 2 * w2) • gen (StrothTypeIndex.t231 s hs).k 2 := by
    module
  rw [e1] at h1
  obtain ⟨c1, -, -⟩ := zsmul_gens_dvd_of_eq h1
  rw [u_apply_gens_t231] at h2
  have e2 : -(y0 • gen (StrothTypeIndex.t231 s hs).k 0 + y1 • gen (StrothTypeIndex.t231 s hs).k 1 +
        y2 • gen (StrothTypeIndex.t231 s hs).k 2) =
      (-y0) • gen (StrothTypeIndex.t231 s hs).k 0 + (-y1) • gen (StrothTypeIndex.t231 s hs).k 1 +
        (-y2) • gen (StrothTypeIndex.t231 s hs).k 2 := by
    module
  rw [e2] at h2
  obtain ⟨u1, u2, -⟩ := zsmul_gens_dvd_of_eq h2
  exact false_of_int_u_cocycle_t230 hs hp c1 u1 u2

section IndexTwo

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem false_of_index_two_of_rho_u_t230 {τ : StrothTypeIndex} (D : StrothTypeData B τ)
    (hρfix : ∀ x z : Torus τ.k, τ.action.φρ x - x = 2 • z →
      ∃ (p : ℤ) (w : Torus τ.k), x = p • gen τ.k 0 + 2 • w)
    (hu : ∀ (p : ℤ) (w y : Torus τ.k), Odd p →
      τ.action.φu (p • gen τ.k 0 + 2 • w) - (p • gen τ.k 0 + 2 • w) = 2 • y →
        τ.action.φu y = -y → False)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  classical
  obtain ⟨d, hdC, hdB⟩ : ∃ d, d ∈ C ∧ d ∉ B := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (fun x hx => hcon x hx : C ≤ B)
    have hpos : 0 < Nat.card B := Nat.card_pos
    omega
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  have hdH : (⟨d, hdC⟩ : C) ∉ B.subgroupOf C := fun h => hdB (Subgroup.mem_subgroupOf.mp h)
  have hd2H : (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ ∈ B.subgroupOf C :=
    (Subgroup.mul_mem_iff_of_index_two hindex).mpr (by simp [hdH])
  have hd2B : d * d ∈ B := by
    simpa using Subgroup.mem_subgroupOf.mp hd2H
  let sB : B := ⟨d * d, hd2B⟩
  have hcommB : ∀ β : B, (β : S) * d = d * (β : S) := fun β =>
    Subgroup.mem_centralizer_iff.mp (hC hdC) (β : S) β.2
  have hconj : ∀ {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B),
      ∃ β : B, g⁻¹ * d * g = d * (β : S) ∧ conjBy hgB sB = sB * (β * β) := by
    intro g hgC hgB
    obtain ⟨β, hβ⟩ := exists_conj_eq hBC hrel hdC hdB g hgC hgB
    have hβS : g⁻¹ * d * g = d * (β : S) := by
      simpa [conjBy_val] using congrArg Subtype.val hβ
    refine ⟨β, hβS, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, conjBy_val]
    change g⁻¹ * (d * d) * g = d * d * ((β : S) * β)
    have h1 : g⁻¹ * (d * d) * g = (g⁻¹ * d * g) * (g⁻¹ * d * g) := by group
    rw [h1, hβS]
    calc d * (β : S) * (d * (β : S)) = d * ((β : S) * d) * β := by group
      _ = d * (d * (β : S)) * β := by rw [hcommB β]
      _ = d * d * ((β : S) * β) := by group
  obtain ⟨βρ, -, hρ⟩ := hconj (hL D.ρ_mem_L) D.ρ_mem
  have hρ' : τ.action.φρ (D.ec sB) - D.ec sB = 2 • D.ec βρ := by
    have h := D.ρ_conj sB
    change D.ec (conjBy D.ρ_mem sB) = τ.action.φρ (D.ec sB) at h
    rw [← h, hρ, D.ec_mul, D.ec_mul, two_nsmul]
    abel
  obtain ⟨p, w, hpw⟩ := hρfix _ _ hρ'
  rcases Int.even_or_odd p with ⟨q, hq⟩ | hp
  ·
    let σ : B := Additive.toMul (D.e.symm (q • gen τ.k 0 + w))
    have hσz : D.ec σ = q • gen τ.k 0 + w := D.e.apply_symm_apply _
    have hσ : σ * σ = sB := by
      apply D.ec_injective
      rw [D.ec_mul, hσz, hpw, hq]
      module
    have hσS : (σ : S) * σ = d * d := by
      simpa [sB] using congrArg Subtype.val hσ
    have hσC : (σ : S) ∈ C := hBC σ.2
    let z : S := d * (σ : S)⁻¹
    have hzC : z ∈ C := C.mul_mem hdC (C.inv_mem hσC)
    have hzz : z * z = 1 := by
      have hcσ : (σ : S)⁻¹ * d = d * (σ : S)⁻¹ := by
        have h := hcommB σ⁻¹
        simpa using h
      calc z * z = d * ((σ : S)⁻¹ * d) * (σ : S)⁻¹ := by simp only [z]; group
        _ = d * (d * (σ : S)⁻¹) * (σ : S)⁻¹ := by rw [hcσ]
        _ = (d * d) * ((σ : S) * σ)⁻¹ := by group
        _ = 1 := by rw [hσS, mul_inv_cancel]
    have hzB : z ∈ B := hH z (hcS hzC) hzz (hC hzC)
    apply hdB
    have hd : d = z * (σ : S) := by simp only [z]; group
    rw [hd]
    exact B.mul_mem hzB σ.2
  ·
    obtain ⟨βu, hβuS, hu1⟩ := hconj (hL D.u_mem_L) D.u_mem
    have hu1' : τ.action.φu (D.ec sB) - D.ec sB = 2 • D.ec βu := by
      have h := D.u_conj sB
      change D.ec (conjBy D.u_mem sB) = τ.action.φu (D.ec sB) at h
      rw [← h, hu1, D.ec_mul, D.ec_mul, two_nsmul]
      abel
    have hβu : βu * conjBy D.u_mem βu = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, conjBy_val, Subgroup.coe_one]
      have huu : D.u * D.u = 1 := D.u_sq
      have huinv : D.u⁻¹ = D.u := inv_eq_of_mul_eq_one_right huu
      have h2 : D.u⁻¹ * (D.u⁻¹ * d * D.u) * D.u = d := by
        rw [huinv]
        calc D.u * (D.u * d * D.u) * D.u = (D.u * D.u) * d * (D.u * D.u) := by group
          _ = d := by rw [huu]; group
      rw [hβuS] at h2
      have h3 : D.u⁻¹ * (d * (βu : S)) * D.u = (D.u⁻¹ * d * D.u) * (D.u⁻¹ * βu * D.u) := by
        group
      rw [h3, hβuS] at h2
      have h4 : d * ((βu : S) * (D.u⁻¹ * βu * D.u)) = d * 1 := by
        rw [mul_one]
        calc d * ((βu : S) * (D.u⁻¹ * βu * D.u)) = d * βu * (D.u⁻¹ * βu * D.u) := by group
          _ = d := h2
      exact mul_left_cancel h4
    have hu2 : τ.action.φu (D.ec βu) = -D.ec βu := by
      have h := D.u_conj βu
      change D.ec (conjBy D.u_mem βu) = τ.action.φu (D.ec βu) at h
      have h' := congrArg D.ec hβu
      rw [D.ec_mul, D.ec_one, h] at h'
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h'
    rw [hpw] at hu1'
    exact hu p w (D.ec βu) hp hu1' hu2

end IndexTwo

theorem false_of_index_two_t230_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {s : ℕ} {hs : 1 ≤ s} (D : StrothTypeData B (StrothTypeIndex.t230 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_two_of_rho_u_t230 D (fun _ _ h => rho_fixed_mod_two_t230 s hs h)
    (fun _ _ _ hp h1 h2 => false_of_u_cocycle_t230 s hs hp h1 h2) hBC hC hrel hL hH hcS

theorem false_of_index_two_t230 {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {s : ℕ} {hs : 1 ≤ s} (hB : HasStrothType B (StrothTypeIndex.t230 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_two_t230_of_data hB.data hBC hC hrel hL hH hcS

theorem false_of_index_two_t231_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {s : ℕ} {hs : 1 ≤ s} (D : StrothTypeData B (StrothTypeIndex.t231 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_two_of_rho_u_t230 D (fun _ _ h => rho_fixed_mod_two_t231 s hs h)
    (fun _ _ _ hp h1 h2 => false_of_u_cocycle_t231 s hs hp h1 h2) hBC hC hrel hL hH hcS

theorem false_of_index_two_t231 {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {s : ℕ} {hs : 1 ≤ s} (hB : HasStrothType B (StrothTypeIndex.t231 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_two_t231_of_data hB.data hBC hC hrel hL hH hcS

theorem t_apply_gens_t230 (s : ℕ) (hs : 1 ≤ s) (i j l : ℤ) :
    (StrothTypeIndex.t230 s hs).action.φt
        (i • gen (StrothTypeIndex.t230 s hs).k 0 + j • gen (StrothTypeIndex.t230 s hs).k 1 +
          l • gen (StrothTypeIndex.t230 s hs).k 2) =
      ((4 - Type120.iV (s + 4)) * i +
          (2 * 2 ^ s + 2 * Type120.GV (s + 4) * Type120.iV (s + 4)) * j +
          (6 * 2 ^ s + Type120.FV (s + 4) * Type120.iV (s + 4) - 2 * Type120.iV (s + 4)) * l) •
          gen (StrothTypeIndex.t230 s hs).k 0 +
        (4 * i + (-7 * Type120.iV (s + 4) - 4 * 2 ^ s) * j +
          (-2 * Type120.iV (s + 4) + 4 * 2 ^ s) * l) • gen (StrothTypeIndex.t230 s hs).k 1 +
        ((8 + 8 * 2 ^ s) * i + (-8 * Type120.iV (s + 4) + 8 * 2 ^ s) * j +
          (-7 * Type120.iV (s + 4) + 12 * 2 ^ s) * l) • gen (StrothTypeIndex.t230 s hs).k 2 := by
  rw [matAct_zsmul_gens]
  simp only [StrothTypeIndex.action, Type230.actionPaper, Type230.action,
    SigmaFourAction.ofMatEq, Type230.tM, Type230.uvA, Type230.ρM, ofCols_apply]
  congr 2
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff]
    ring
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff]
    ring
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff]
    ring

theorem odd_iV_FV_GV_t230 (s : ℕ) :
    Odd (Type120.iV (s + 4)) ∧ Odd (Type120.FV (s + 4)) ∧ Odd (Type120.GV (s + 4)) := by
  obtain ⟨hi, hF, hG, -⟩ := Type230.data s
  generalize ((2 : ℤ) ^ s) ^ 2 = X at hG
  refine ⟨Int.odd_iff.mpr ?_, Int.odd_iff.mpr ?_, Int.odd_iff.mpr ?_⟩ <;> omega

theorem t230_k_pos (s : ℕ) (hs : 1 ≤ s) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t230 s hs).k i := by
  fin_cases i <;> simp [StrothTypeIndex.k, Type230.k]

@[expose] def rhoBar230 (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 := ![v 0 + v 2, v 2, v 1 + v 2]

@[expose] def tBar230 (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 := ![v 0 + v 2, v 1, v 2]

theorem parityTorus_rho_t230 (s : ℕ) (hs : 1 ≤ s) (y : Torus (StrothTypeIndex.t230 s hs).k) :
    parityTorus _ (t230_k_pos s hs) ((StrothTypeIndex.t230 s hs).action.φρ y) =
      rhoBar230 (parityTorus _ (t230_k_pos s hs) y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [rho_apply_gens_t230, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  funext r
  fin_cases r
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_t_t230 (s : ℕ) (hs : 1 ≤ s) (y : Torus (StrothTypeIndex.t230 s hs).k) :
    parityTorus _ (t230_k_pos s hs) ((StrothTypeIndex.t230 s hs).action.φt y) =
      tBar230 (parityTorus _ (t230_k_pos s hs) y) := by
  obtain ⟨hI, hF, hG⟩ := odd_iV_FV_GV_t230 s
  have hI2 : ((Type120.iV (s + 4) : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hI
  have hF2 : ((Type120.FV (s + 4) : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hF
  have hG2 : ((Type120.GV (s + 4) : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hG
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [t_apply_gens_t230, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h6 : (6 : ZMod 2) = 0 := by decide
  have h7 : (7 : ZMod 2) = 1 := by decide
  have h8 : (8 : ZMod 2) = 0 := by decide
  have h12 : (12 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r
  · simp [tBar230, hI2, hF2, hG2, h2, h4, h6, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, hI2, h2, h4, h7, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, hI2, h4, h7, h8, h12, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem plane_check_t230 : ∀ v w : Fin 3 → ZMod 2, (v ≠ 0 ∧ w ≠ 0 ∧ v ≠ w ∧
    (rhoBar230 v = v ∨ rhoBar230 v = w ∨ rhoBar230 v = v + w) ∧
    (rhoBar230 w = v ∨ rhoBar230 w = w ∨ rhoBar230 w = v + w) ∧
    (tBar230 v = v ∨ tBar230 v = w ∨ tBar230 v = v + w) ∧
    (tBar230 w = v ∨ tBar230 w = w ∨ tBar230 w = v + w)) → False := by
  unfold rhoBar230 tBar230
  decide

theorem fixed_rho_t_t230 {S : Type*} [Group S] [Finite S] {B : Subgroup S} {s : ℕ} {hs : 1 ≤ s}
    (D : StrothTypeData B (StrothTypeIndex.t230 s hs)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t230 s hs).action.φρ (D.ec y) = D.ec y := by
    have h := D.ρ_conj y
    change D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t230 s hs).action.φρ (D.ec y) at h
    rw [← h, hρ]
  have ht' : (StrothTypeIndex.t230 s hs).action.φt (D.ec y) = D.ec y := by
    have h := D.t_conj y
    change D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t230 s hs).action.φt (D.ec y) at h
    rw [← h, ht]
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens _ (D.ec y)
  rw [hy, rho_apply_gens_t230] at hρ'
  rw [hy, t_apply_gens_t230] at ht'
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hρ'
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq ht'
  change (2 : ℤ) ^ (s + 4) ∣ _ at hρ1 hρ2 ht1
  have h3 : IsCoprime ((2 : ℤ) ^ (s + 4)) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  have hl : (2 : ℤ) ^ (s + 4) ∣ l := by
    refine h3.dvd_of_dvd_mul_left ?_
    have := dvd_add hρ1 hρ2
    convert this using 1
    ring
  have hj : (2 : ℤ) ^ (s + 4) ∣ j := by
    have := dvd_sub hρ1 hl
    convert this using 1
    ring
  have h4i : (2 : ℤ) ^ (s + 4) ∣ 4 * i := by
    have := dvd_sub (dvd_sub (dvd_mul_of_dvd_right hj (1 - (-7 * Type120.iV (s + 4) - 4 * 2 ^ s)))
      (dvd_mul_of_dvd_right hl (-2 * Type120.iV (s + 4) + 4 * 2 ^ s))) ht1
    convert this using 1
    ring
  have hi : (2 : ℤ) ^ (s + 2) ∣ i := by
    have h16 : (2 : ℤ) ^ (s + 4) = 4 * 2 ^ (s + 2) := by ring
    rw [h16] at h4i
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4i
  apply D.ec_eq_zero_iff.mp
  rw [hy]
  have h0 := zsmul_gens_eq_of_dvd (k := (StrothTypeIndex.t230 s hs).k) (p := i) (q := j) (r := l)
    (p' := 0) (q' := 0) (r' := 0)
    (by change (2 : ℤ) ^ (s + 2) ∣ 0 - i; rw [zero_sub, dvd_neg]; exact hi)
    (by change (2 : ℤ) ^ (s + 4) ∣ 0 - j; rw [zero_sub, dvd_neg]; exact hj)
    (by change (2 : ℤ) ^ (s + 4) ∣ 0 - l; rw [zero_sub, dvd_neg]; exact hl)
  rw [h0]
  simp

theorem t_apply_gens_t231 (s : ℕ) (hs : 1 ≤ s) (i j l : ℤ) :
    (StrothTypeIndex.t231 s hs).action.φt
        (i • gen (StrothTypeIndex.t231 s hs).k 0 + j • gen (StrothTypeIndex.t231 s hs).k 1 +
          l • gen (StrothTypeIndex.t231 s hs).k 2) =
      ((4 - Type120.iV (s + 4)) * i +
          (2 * 2 ^ s + 2 * Type120.GV (s + 4) * Type120.iV (s + 4)) * j +
          (Type120.FV (s + 4) * Type120.iV (s + 4) - 2 * Type120.iV (s + 4) - 2 * 2 ^ s) * l) •
          gen (StrothTypeIndex.t231 s hs).k 0 +
        (4 * i + (-7 * Type120.iV (s + 4) + 4 * 2 ^ s) * j +
          (-2 * Type120.iV (s + 4) - 4 * 2 ^ s) * l) • gen (StrothTypeIndex.t231 s hs).k 1 +
        ((8 + 8 * 2 ^ s) * i + (-8 * Type120.iV (s + 4) + 8 * 2 ^ s) * j +
          (-7 * Type120.iV (s + 4) + 4 * 2 ^ s) * l) • gen (StrothTypeIndex.t231 s hs).k 2 := by
  rw [matAct_zsmul_gens]
  simp only [StrothTypeIndex.action, Type231.actionPaper, Type231.action,
    SigmaFourAction.ofMatEq, Type231.tM, Type231.uvA, Type231.ρM, ofCols_apply]
  congr 2
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff]
    ring
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff]
    ring
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff]
    ring

theorem t231_k_pos (s : ℕ) (hs : 1 ≤ s) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t231 s hs).k i := by
  fin_cases i <;> simp [StrothTypeIndex.k, Type231.k]

theorem parityTorus_rho_t231 (s : ℕ) (hs : 1 ≤ s) (y : Torus (StrothTypeIndex.t231 s hs).k) :
    parityTorus _ (t231_k_pos s hs) ((StrothTypeIndex.t231 s hs).action.φρ y) =
      rhoBar230 (parityTorus _ (t231_k_pos s hs) y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [rho_apply_gens_t231, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  funext r
  fin_cases r
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar230, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_t_t231 (s : ℕ) (hs : 1 ≤ s) (y : Torus (StrothTypeIndex.t231 s hs).k) :
    parityTorus _ (t231_k_pos s hs) ((StrothTypeIndex.t231 s hs).action.φt y) =
      tBar230 (parityTorus _ (t231_k_pos s hs) y) := by
  obtain ⟨hI, hF, hG⟩ := odd_iV_FV_GV_t230 s
  have hI2 : ((Type120.iV (s + 4) : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hI
  have hF2 : ((Type120.FV (s + 4) : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hF
  have hG2 : ((Type120.GV (s + 4) : ℤ) : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hG
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [t_apply_gens_t231, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h6 : (6 : ZMod 2) = 0 := by decide
  have h7 : (7 : ZMod 2) = 1 := by decide
  have h8 : (8 : ZMod 2) = 0 := by decide
  have h12 : (12 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r
  · simp [tBar230, hI2, hF2, hG2, h2, h4, h6, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, hI2, h2, h4, h7, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar230, hI2, h4, h7, h8, h12, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem fixed_rho_t_t231 {S : Type*} [Group S] [Finite S] {B : Subgroup S} {s : ℕ} {hs : 1 ≤ s}
    (D : StrothTypeData B (StrothTypeIndex.t231 s hs)) {y : B}
    (hρ : conjBy D.ρ_mem y = y) (ht : conjBy D.t_mem y = y) : y = 1 := by
  have hρ' : (StrothTypeIndex.t231 s hs).action.φρ (D.ec y) = D.ec y := by
    have h := D.ρ_conj y
    change D.ec (conjBy D.ρ_mem y) = (StrothTypeIndex.t231 s hs).action.φρ (D.ec y) at h
    rw [← h, hρ]
  have ht' : (StrothTypeIndex.t231 s hs).action.φt (D.ec y) = D.ec y := by
    have h := D.t_conj y
    change D.ec (conjBy D.t_mem y) = (StrothTypeIndex.t231 s hs).action.φt (D.ec y) at h
    rw [← h, ht]
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens _ (D.ec y)
  rw [hy, rho_apply_gens_t231] at hρ'
  rw [hy, t_apply_gens_t231] at ht'
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hρ'
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq ht'
  change (2 : ℤ) ^ (s + 4) ∣ _ at hρ1 hρ2 ht1
  have h3 : IsCoprime ((2 : ℤ) ^ (s + 4)) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  have hl : (2 : ℤ) ^ (s + 4) ∣ l := by
    refine h3.dvd_of_dvd_mul_left ?_
    have := dvd_add hρ1 hρ2
    convert this using 1
    ring
  have hj : (2 : ℤ) ^ (s + 4) ∣ j := by
    have := dvd_sub hρ1 hl
    convert this using 1
    ring
  have h4i : (2 : ℤ) ^ (s + 4) ∣ 4 * i := by
    have := dvd_sub (dvd_sub (dvd_mul_of_dvd_right hj (1 - (-7 * Type120.iV (s + 4) + 4 * 2 ^ s)))
      (dvd_mul_of_dvd_right hl (-2 * Type120.iV (s + 4) - 4 * 2 ^ s))) ht1
    convert this using 1
    ring
  have hi : (2 : ℤ) ^ (s + 2) ∣ i := by
    have h16 : (2 : ℤ) ^ (s + 4) = 4 * 2 ^ (s + 2) := by ring
    rw [h16] at h4i
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4i
  apply D.ec_eq_zero_iff.mp
  rw [hy]
  have h0 := zsmul_gens_eq_of_dvd (k := (StrothTypeIndex.t231 s hs).k) (p := i) (q := j) (r := l)
    (p' := 0) (q' := 0) (r' := 0)
    (by change (2 : ℤ) ^ (s + 2) ∣ 0 - i; rw [zero_sub, dvd_neg]; exact hi)
    (by change (2 : ℤ) ^ (s + 4) ∣ 0 - j; rw [zero_sub, dvd_neg]; exact hj)
    (by change (2 : ℤ) ^ (s + 4) ∣ 0 - l; rw [zero_sub, dvd_neg]; exact hl)
  rw [h0]
  simp

section IndexFour

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem false_of_index_four_of_planes_t230 {τ : StrothTypeIndex} (D : StrothTypeData B τ)
    (hk : ∀ i, 1 ≤ τ.k i)
    (hρpar : ∀ y, parityTorus τ.k hk (τ.action.φρ y) = rhoBar230 (parityTorus τ.k hk y))
    (htpar : ∀ y, parityTorus τ.k hk (τ.action.φt y) = tBar230 (parityTorus τ.k hk y))
    (hfix : ∀ y : B, conjBy D.ρ_mem y = y → conjBy D.t_mem y = y → y = 1)
    [hN : (B.subgroupOf C).Normal]
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hcyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) : False := by
  classical
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_Idx4 D hBC hC hrel hL hcyc hfix
  have hcomm : ∀ x y : C, x * y = y * x := fun x y => hcommC.is_comm.comm x y
  have hsq : ∀ x : C, (x : S) * x ∈ B := fun x =>
    sq_mem_of_not_cyclic_quotient_four hBC hC hrel hcyc x
  have hcard : Nat.card (C ⧸ B.subgroupOf C) = 4 := card_quotient_four hBC hC hrel
  have hexp : ∀ q : C ⧸ B.subgroupOf C, q * q = 1 := by
    rcases cyclic_or_sq_eq_one hcard with h | h
    · exact absurd h hcyc
    · exact h
  obtain ⟨x₁, x₂, h1, h2, h12⟩ := exists_gens_Idx4 hcard hcyc
  let π : C → Fin 3 → ZMod 2 := sqParityIdx4 D hk hsq
  have hπmul : ∀ x y : C, π (x * y) = π x + π y := sqParityIdx4_mul hcomm
  have hπB : ∀ x : C, x ∈ B.subgroupOf C → π x = 0 := fun x hx =>
    sqParityIdx4_of_mem x (Subgroup.mem_subgroupOf.mp hx)
  have hπ0 : ∀ x : C, π x = 0 → x ∈ B.subgroupOf C := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (mem_of_sqParityIdx4_eq_zero hcomm hC hH hcS hBC x hx)
  have hπcoset : ∀ y z : C, y * z⁻¹ ∈ B.subgroupOf C → π y = π z := by
    intro y z h
    have hy : y = (y * z⁻¹) * z := by group
    rw [hy, hπmul, hπB _ h, zero_add]
  have hv : π x₁ ≠ 0 := fun h => h1 (hπ0 _ h)
  have hw : π x₂ ≠ 0 := fun h => h2 (hπ0 _ h)
  have hvw : π x₁ ≠ π x₂ := by
    intro h
    apply h12
    apply hπ0
    have h3 : π x₁ = π (x₁ * x₂⁻¹) + π x₂ := by rw [← hπmul, inv_mul_cancel_right]
    rw [h] at h3
    have h4 := congrArg (· - π x₂) h3
    simpa using h4.symm
  have himage : ∀ {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
      (x : C), x ∉ B.subgroupOf C →
      π (conjBy hgC x) = π x₁ ∨ π (conjBy hgC x) = π x₂ ∨
        π (conjBy hgC x) = π x₁ + π x₂ := by
    intro g hgC hgB x hx
    rcases mem_cosets_Idx4 hcard hexp h1 h2 h12 (conjBy hgC x) with h | h | h | h
    · exfalso
      apply hx
      rw [Subgroup.mem_subgroupOf] at h ⊢
      exact (Subgroup.mem_normalizer_iff''.mp hgB (x : S)).mpr h
    · exact Or.inl (hπcoset _ _ h)
    · exact Or.inr (Or.inl (hπcoset _ _ h))
    · exact Or.inr (Or.inr (by rw [hπcoset _ _ h, hπmul]))
  have hρx : ∀ x : C, π (conjBy (hL D.ρ_mem_L) x) = rhoBar230 (π x) := fun x =>
    sqParityIdx4_conj (hL D.ρ_mem_L) D.ρ_mem (fun y => D.ρ_conj y) hρpar x
  have htx : ∀ x : C, π (conjBy (hL D.t_mem_L) x) = tBar230 (π x) := fun x =>
    sqParityIdx4_conj (hL D.t_mem_L) D.t_mem (fun y => D.t_conj y) htpar x
  refine plane_check_t230 (π x₁) (π x₂) ⟨hv, hw, hvw, ?_, ?_, ?_, ?_⟩
  · rw [← hρx]; exact himage _ D.ρ_mem x₁ h1
  · rw [← hρx]; exact himage _ D.ρ_mem x₂ h2
  · rw [← htx]; exact himage _ D.t_mem x₁ h1
  · rw [← htx]; exact himage _ D.t_mem x₂ h2

end IndexFour

theorem false_of_index_four_t230_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {s : ℕ} {hs : 1 ≤ s} (D : StrothTypeData B (StrothTypeIndex.t230 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  by_cases hcyc : IsCyclic (C ⧸ B.subgroupOf C)
  · obtain ⟨C₂, hBC₂, hC₂C, hrel₂, hL₂⟩ :=
      exists_index_two_of_isCyclic_Idx4 D hBC hC hrel hL hcyc
    exact false_of_index_two_t230_of_data D hBC₂ (hC₂C.trans hC) hrel₂ hL₂ hH (hC₂C.trans hcS)
  · exact false_of_index_four_of_planes_t230 D (t230_k_pos s hs) (parityTorus_rho_t230 s hs)
      (parityTorus_t_t230 s hs) (fun _ hρ ht => fixed_rho_t_t230 D hρ ht) hBC hC hrel hL
      hH hcS hcyc

theorem false_of_index_four_t230 {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {s : ℕ} {hs : 1 ≤ s} (hB : HasStrothType B (StrothTypeIndex.t230 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_four_t230_of_data hB.data hBC hC hrel hL hH hcS

theorem false_of_index_four_t231_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {s : ℕ} {hs : 1 ≤ s} (D : StrothTypeData B (StrothTypeIndex.t231 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  by_cases hcyc : IsCyclic (C ⧸ B.subgroupOf C)
  · obtain ⟨C₂, hBC₂, hC₂C, hrel₂, hL₂⟩ :=
      exists_index_two_of_isCyclic_Idx4 D hBC hC hrel hL hcyc
    exact false_of_index_two_t231_of_data D hBC₂ (hC₂C.trans hC) hrel₂ hL₂ hH (hC₂C.trans hcS)
  · exact false_of_index_four_of_planes_t230 D (t231_k_pos s hs) (parityTorus_rho_t231 s hs)
      (parityTorus_t_t231 s hs) (fun _ hρ ht => fixed_rho_t_t231 D hρ ht) hBC hC hrel hL
      hH hcS hcyc

theorem false_of_index_four_t231 {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}
    {s : ℕ} {hs : 1 ≤ s} (hB : HasStrothType B (StrothTypeIndex.t231 s hs))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_four_t231_of_data hB.data hBC hC hrel hL hH hcS

end CFSG.CGT.Stroth77

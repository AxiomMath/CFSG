module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesWeir

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {P : Submodule (ZMod 3) V}

theorem om6par_aniso (hnd : (Q.restrict P).Nondegenerate)
    (hdim : Module.finrank (ZMod 3) P = 2) (hs : quadSign (Q.restrict P) = -1)
    {p : V} (hp : p ∈ P) (hp0 : p ≠ 0) : Q p ≠ 0 := by
  intro hQp
  have hp0' : (⟨p, hp⟩ : P) ≠ 0 := fun h => hp0 (congrArg Subtype.val h)
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict P) := by
    refine ⟨Submodule.span (ZMod 3) {(⟨p, hp⟩ : P)}, ?_, ?_⟩
    · rw [finrank_span_singleton hp0', hdim]
    · intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [QuadraticMap.map_smul]
      have h0 : (Q.restrict P) ⟨p, hp⟩ = 0 := hQp
      rw [h0, smul_zero]
  have h1 := (isPlusType_iff_quadSign_eq_one hnd (d := 1) (by rw [hdim])).mp hplus
  rw [hs] at h1
  exact absurd h1 (by decide)

private theorem om6par_plane_key : ∀ a c d f μ : ZMod 3, μ ≠ 0 →
    (∀ x y : ZMod 3, (x * a + y * d) * (x * a + y * d) + (x * c + y * f) * (x * c + y * f) =
      μ * (x * x + y * y)) →
    (((∀ x y : ZMod 3, x * a + y * d = x * a + (-y) * d ∧
        -(x * c + y * f) = x * c + (-y) * f) ∨
      (∀ x y : ZMod 3, x * a + y * d = -(x * a + (-y) * d) ∧
        -(x * c + y * f) = -(x * c + (-y) * f))) ↔ μ = 1) := by
  decide +kernel

theorem om6par_plane (hnd : (Q.restrict P).Nondegenerate) (hdim : Module.finrank (ZMod 3) P = 2)
    (hs : quadSign (Q.restrict P) = -1) {b τ : V ≃ₗ[ZMod 3] V} {μ : ZMod 3} (hμ : μ ≠ 0)
    (hbP : ∀ p ∈ P, b p ∈ P) (hτP : ∀ p ∈ P, τ p ∈ P) (hbb : ∀ p ∈ P, b (b p) = p)
    (hbQ : ∀ p ∈ P, Q (b p) = Q p) (hτQ : ∀ p ∈ P, Q (τ p) = μ * Q p)
    (hb1 : ∃ p ∈ P, b p ≠ p) (hb2 : ∃ p ∈ P, b p ≠ -p) :
    ((∀ p ∈ P, b (τ p) = τ (b p)) ∨ (∀ p ∈ P, b (τ p) = -τ (b p))) ↔ μ = 1 := by
  have haniso : ∀ {p : V}, p ∈ P → p ≠ 0 → Q p ≠ 0 := fun hp hp0 =>
    om6par_aniso hnd hdim hs hp hp0
  have h2ne : (2 : ZMod 3) ≠ 0 := by decide
  obtain ⟨p₁, hp₁, hbp₁⟩ := hb1
  obtain ⟨p₂, hp₂, hbp₂⟩ := hb2
  have hv : p₂ + b p₂ ∈ P := P.add_mem hp₂ (hbP _ hp₂)
  have hw : p₁ - b p₁ ∈ P := P.sub_mem hp₁ (hbP _ hp₁)
  generalize hvdef : p₂ + b p₂ = v at hv
  generalize hwdef : p₁ - b p₁ = w at hw
  have hbv : b v = v := by rw [← hvdef, map_add, hbb _ hp₂, add_comm]
  have hbw : b w = -w := by rw [← hwdef, map_sub, hbb _ hp₁, neg_sub]
  have hv0 : v ≠ 0 := by
    intro h
    rw [← hvdef] at h
    exact hbp₂ (eq_neg_of_add_eq_zero_right h)
  have hw0 : w ≠ 0 := by
    intro h
    rw [← hwdef] at h
    exact hbp₁ (sub_eq_zero.mp h).symm
  have hbpolar : ∀ x ∈ P, ∀ y ∈ P, polar Q (b x) (b y) = polar Q x y := by
    intro x hx y hy
    have h := hbQ _ (P.add_mem hx hy)
    simp only [polar]
    rw [← map_add b x y, h, hbQ _ hx, hbQ _ hy]
  have hpol : polar Q v w = 0 := by
    have h := hbpolar v hv w hw
    rw [hbv, hbw, polar_neg_right] at h
    have h' : (2 : ZMod 3) * polar Q v w = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left h2ne
  have hvw : v + w ≠ 0 := by
    intro h
    have hwv : w = -v := eq_neg_of_add_eq_zero_right h
    have h1 : b w = -v := by rw [hwv, map_neg, hbv]
    rw [hbw, hwv, neg_neg] at h1
    have h2 : (2 : ZMod 3) • v = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr h1
    exact hv0 ((smul_eq_zero.mp h2).resolve_left h2ne)
  have hQv := haniso hv hv0
  have hQw := haniso hw hw0
  have hQvw : Q v = Q w := by
    by_contra hne
    have hsum : Q v + Q w = 0 := by
      revert hQv hQw hne
      generalize Q v = s
      generalize Q w = t
      revert s t
      decide
    refine haniso (P.add_mem hv hw) hvw ?_
    rw [QuadraticMap.map_add Q, hpol, hsum, add_zero]
  have hind : ∀ s t : ZMod 3, s • v + t • w = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have h1 : s • v - t • w = 0 := by
      have h' := congrArg b h
      rwa [map_add, map_smul, map_smul, map_zero, hbv, hbw, smul_neg, ← sub_eq_add_neg] at h'
    have h3 : (2 * s) • v = 0 := by
      calc (2 * s) • v = (s • v + t • w) + (s • v - t • w) := by rw [mul_smul, two_smul]; abel
        _ = 0 := by rw [h, h1, add_zero]
    have hs0 : s = 0 :=
      (mul_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv0)).resolve_left h2ne
    rw [hs0, zero_smul, zero_add] at h
    exact ⟨hs0, (smul_eq_zero.mp h).resolve_right hw0⟩
  have hcomb : ∀ s t s' t' : ZMod 3, s • v + t • w = s' • v + t' • w ↔ s = s' ∧ t = t' := by
    intro s t s' t'
    refine ⟨fun h => ?_, fun h => by rw [h.1, h.2]⟩
    have h' : (s - s') • v + (t - t') • w = 0 := by
      calc (s - s') • v + (t - t') • w = (s • v + t • w) - (s' • v + t' • w) := by module
        _ = 0 := by rw [h, sub_self]
    exact ⟨sub_eq_zero.mp (hind _ _ h').1, sub_eq_zero.mp (hind _ _ h').2⟩
  have hli : LinearIndependent (ZMod 3) ![v, w] := LinearIndependent.pair_iff.mpr hind
  have hspan : Submodule.span (ZMod 3) (Set.range ![v, w]) = P := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hv
      · exact hw
    · rw [finrank_span_eq_card hli, hdim]
      simp
  have hcoord : ∀ p ∈ P, ∃ x y : ZMod 3, p = x • v + y • w := by
    intro p hp
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hp
    obtain ⟨c, hc⟩ := hp
    exact ⟨c 0, c 1, by rw [← hc, Fin.sum_univ_two]; simp⟩
  obtain ⟨a, c, hτv⟩ := hcoord (τ v) (hτP v hv)
  obtain ⟨d, f, hτw⟩ := hcoord (τ w) (hτP w hw)
  have hτ : ∀ x y : ZMod 3, τ (x • v + y • w) =
      (x * a + y * d) • v + (x * c + y * f) • w := by
    intro x y
    rw [map_add, map_smul, map_smul, hτv, hτw]
    module
  have hb' : ∀ x y : ZMod 3, b (x • v + y • w) = x • v + (-y) • w := by
    intro x y
    rw [map_add, map_smul, map_smul, hbv, hbw]
    module
  have hneg : ∀ s t : ZMod 3, -(s • v + t • w) = (-s) • v + (-t) • w := by
    intro s t
    module
  have hQ' : ∀ x y : ZMod 3, Q (x • v + y • w) = Q v * (x * x + y * y) := by
    intro x y
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
      polar_smul_right, hpol, ← hQvw]
    simp only [smul_eq_mul, mul_zero]
    ring
  have hsim : ∀ x y : ZMod 3, (x * a + y * d) * (x * a + y * d) +
      (x * c + y * f) * (x * c + y * f) = μ * (x * x + y * y) := by
    intro x y
    have h := hτQ (x • v + y • w) (P.add_mem (P.smul_mem _ hv) (P.smul_mem _ hw))
    rw [hτ, hQ', hQ'] at h
    refine mul_left_cancel₀ hQv ?_
    rw [h]
    ring
  have hmem : ∀ x y : ZMod 3, x • v + y • w ∈ P := fun x y =>
    P.add_mem (P.smul_mem _ hv) (P.smul_mem _ hw)
  have hP1 : (∀ p ∈ P, b (τ p) = τ (b p)) ↔ ∀ x y : ZMod 3,
      x * a + y * d = x * a + (-y) * d ∧ -(x * c + y * f) = x * c + (-y) * f := by
    constructor
    · intro H x y
      have h := H (x • v + y • w) (hmem x y)
      simpa only [hτ, hb', hcomb] using h
    · intro H p hp
      obtain ⟨x, y, rfl⟩ := hcoord p hp
      simpa only [hτ, hb', hcomb] using H x y
  have hP2 : (∀ p ∈ P, b (τ p) = -τ (b p)) ↔ ∀ x y : ZMod 3,
      x * a + y * d = -(x * a + (-y) * d) ∧ -(x * c + y * f) = -(x * c + (-y) * f) := by
    constructor
    · intro H x y
      have h := H (x • v + y • w) (hmem x y)
      simpa only [hτ, hb', hneg, hcomb] using h
    · intro H p hp
      obtain ⟨x, y, rfl⟩ := hcoord p hp
      simpa only [hτ, hb', hneg, hcomb] using H x y
  rw [hP1, hP2]
  exact om6par_plane_key a c d f μ hμ hsim

end CFSG.OddStandard.SmallF3.Omega

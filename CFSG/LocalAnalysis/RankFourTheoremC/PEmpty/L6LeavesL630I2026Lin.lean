module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure QDRel (a b c d ζ : Module.End K V) : Prop where
  aa : a * a = ζ
  bb : b * b = ζ
  cc : c * c = ζ
  dd : d * d = 1
  zz : ζ * ζ = 1
  ba : b * a = ζ * (a * b)
  dc : d * c = ζ * (c * d)
  ac : a * c = c * a
  ad : a * d = d * a
  bc : b * c = c * b
  bd : b * d = d * b
  z_ne : ζ ≠ 1

theorem indep_pair_aux {p q : V} (hp0 : p ≠ 0) (hq : ∀ ν : K, q ≠ ν • p) (x y : K)
    (hxy : x • p + y • q = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    rw [zero_smul, add_zero] at hxy
    exact ⟨(smul_eq_zero.mp hxy).resolve_right hp0, rfl⟩
  · exfalso
    apply hq (-(y⁻¹ * x))
    have h1 : y • q = -(x • p) := eq_neg_of_add_eq_zero_right hxy
    calc q = y⁻¹ • (y • q) := by rw [smul_smul, inv_mul_cancel₀ hy, one_smul]
      _ = (-(y⁻¹ * x)) • p := by rw [h1, smul_neg, smul_smul, neg_smul]

namespace QDRel

variable {a b c d ζ : Module.End K V} (h : QDRel a b c d ζ)

include h

theorem aa' (v : V) : a (a v) = ζ v := by
  rw [← Module.End.mul_apply, h.aa]

theorem bb' (v : V) : b (b v) = ζ v := by
  rw [← Module.End.mul_apply, h.bb]

theorem cc' (v : V) : c (c v) = ζ v := by
  rw [← Module.End.mul_apply, h.cc]

theorem dd' (v : V) : d (d v) = v := by
  rw [← Module.End.mul_apply, h.dd, Module.End.one_apply]

theorem zz' (v : V) : ζ (ζ v) = v := by
  rw [← Module.End.mul_apply, h.zz, Module.End.one_apply]

theorem ba' (v : V) : b (a v) = ζ (a (b v)) := by
  rw [← Module.End.mul_apply, h.ba, Module.End.mul_apply, Module.End.mul_apply]

theorem ab' (v : V) : a (b v) = ζ (b (a v)) := by
  rw [h.ba', h.zz']

theorem dc' (v : V) : d (c v) = ζ (c (d v)) := by
  rw [← Module.End.mul_apply, h.dc, Module.End.mul_apply, Module.End.mul_apply]

theorem ac' (v : V) : a (c v) = c (a v) := by
  rw [← Module.End.mul_apply, h.ac, Module.End.mul_apply]

theorem ad' (v : V) : a (d v) = d (a v) := by
  rw [← Module.End.mul_apply, h.ad, Module.End.mul_apply]

theorem bd' (v : V) : b (d v) = d (b v) := by
  rw [← Module.End.mul_apply, h.bd, Module.End.mul_apply]

theorem za (v : V) : ζ (a v) = a (ζ v) := by
  rw [← h.aa' (a v), h.aa' v]

theorem zb (v : V) : ζ (b v) = b (ζ v) := by
  rw [← h.bb' (b v), h.bb' v]

theorem zc (v : V) : ζ (c v) = c (ζ v) := by
  rw [← h.cc' (c v), h.cc' v]

theorem zd (v : V) : ζ (d v) = d (ζ v) := by
  rw [← h.aa' (d v), h.ad', h.ad', h.aa' v]

theorem a_inj {v : V} (hv : a v = 0) : v = 0 := by
  have h1 : ζ v = 0 := by rw [← h.aa' v, hv, map_zero]
  rw [← h.zz' v, h1, map_zero]

theorem b_inj {v : V} (hv : b v = 0) : v = 0 := by
  have h1 : ζ v = 0 := by rw [← h.bb' v, hv, map_zero]
  rw [← h.zz' v, h1, map_zero]

theorem c_inj {v : V} (hv : c v = 0) : v = 0 := by
  have h1 : ζ v = 0 := by rw [← h.cc' v, hv, map_zero]
  rw [← h.zz' v, h1, map_zero]

theorem exists_u0 : ∃ u : V, u ≠ 0 ∧ ζ u = -u ∧ d u = u := by
  obtain ⟨w, hw⟩ : ∃ w : V, ζ w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact h.z_ne (LinearMap.ext fun w => by simpa using hcon w)
  have hw₁ne : w - ζ w ≠ 0 := sub_ne_zero.mpr (fun h' => hw h'.symm)
  have hζw₁ : ζ (w - ζ w) = -(w - ζ w) := by
    rw [map_sub, h.zz', neg_sub]
  by_cases hd : (w - ζ w) + d (w - ζ w) = 0
  · have hdw : d (w - ζ w) = -(w - ζ w) := eq_neg_of_add_eq_zero_right hd
    refine ⟨c (w - ζ w), fun h0 => hw₁ne (h.c_inj h0), ?_, ?_⟩
    · rw [h.zc, hζw₁, map_neg]
    · rw [h.dc', hdw, map_neg, map_neg, h.zc, hζw₁, map_neg, neg_neg]
  · refine ⟨(w - ζ w) + d (w - ζ w), hd, ?_, ?_⟩
    · rw [map_add, h.zd, hζw₁, map_neg, neg_add]
    · rw [map_add, h.dd']
      exact add_comm _ _

theorem exists_u (h2 : (2 : K) ≠ 0) :
    ∃ u : V, ζ u = -u ∧ d u = u ∧ ∀ x y : K, x • u + y • a u = 0 → x = 0 ∧ y = 0 := by
  obtain ⟨p, hp0, hpζ, hpd⟩ := h.exists_u0
  by_cases hpa : ∃ l : K, a p = l • p
  · obtain ⟨l, hl⟩ := hpa
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hp0 (h.a_inj (by rw [hl, zero_smul]))
    obtain ⟨q, hq⟩ : ∃ q : V, q = b p := ⟨_, rfl⟩
    have hqζ : ζ q = -q := by rw [hq, h.zb, hpζ, map_neg]
    have hqd : d q = q := by rw [hq, ← h.bd', hpd]
    have haq : a q = (-l) • q := by
      rw [hq, h.ab', hl, map_smul, map_smul, ← hq, hqζ, smul_neg, neg_smul]
    have hind : ∀ ν : K, q ≠ ν • p := by
      intro ν hν
      have h1 : a q = (ν * l) • p := by rw [hν, map_smul, hl, smul_smul]
      have h2' : a q = (-l * ν) • p := by rw [haq, hν, smul_smul]
      have h3 : (2 * (ν * l)) • p = 0 := by
        have : ((ν * l) - (-l * ν)) • p = 0 := by rw [sub_smul, ← h1, ← h2', sub_self]
        rw [← this]
        congr 1
        ring
      have h4 : 2 * (ν * l) = 0 := (smul_eq_zero.mp h3).resolve_right hp0
      have h5 : ν = 0 := by
        rcases mul_eq_zero.mp h4 with h6 | h6
        · exact absurd h6 h2
        · exact (mul_eq_zero.mp h6).resolve_right hl0
      apply hp0
      apply h.b_inj
      rw [← hq, hν, h5, zero_smul]
    refine ⟨p + q, ?_, ?_, ?_⟩
    · rw [map_add, hpζ, hqζ, neg_add]
    · rw [map_add, hpd, hqd]
    · intro x y hxy
      have hap : a (p + q) = l • p + (-l) • q := by rw [map_add, hl, haq]
      have key : (x + y * l) • p + (x - y * l) • q = 0 := by
        rw [hap] at hxy
        rw [← hxy]
        module
      obtain ⟨hx1, hx2⟩ := indep_pair_aux hp0 hind _ _ key
      have hy : y = 0 := by
        have h3 : 2 * (y * l) = 0 := by linear_combination hx1 - hx2
        rcases mul_eq_zero.mp h3 with h6 | h6
        · exact absurd h6 h2
        · exact (mul_eq_zero.mp h6).resolve_right hl0
      subst hy
      exact ⟨by simpa using hx1, rfl⟩
  · refine ⟨p, hpζ, hpd, ?_⟩
    push Not at hpa
    intro x y hxy
    by_cases hy : y = 0
    · subst hy
      rw [zero_smul, add_zero] at hxy
      exact ⟨(smul_eq_zero.mp hxy).resolve_right hp0, rfl⟩
    · exfalso
      apply hpa (-(y⁻¹ * x))
      have h1 : y • a p = -(x • p) := eq_neg_of_add_eq_zero_right hxy
      calc a p = y⁻¹ • (y • a p) := by rw [smul_smul, inv_mul_cancel₀ hy, one_smul]
        _ = (-(y⁻¹ * x)) • p := by rw [h1, smul_neg, smul_smul, neg_smul]

theorem four_indep (h2 : (2 : K) ≠ 0) {u : V} (hζ : ζ u = -u) (hd : d u = u)
    (hin : ∀ x y : K, x • u + y • a u = 0 → x = 0 ∧ y = 0) :
    LinearIndependent K ![u, a u, c u, a (c u)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • u + g 1 • a u + g 2 • c u + g 3 • a (c u) = 0 := by
    simpa [Fin.sum_univ_four] using hg
  have hdau : d (a u) = a u := by rw [← h.ad', hd]
  have hdcu : d (c u) = -c u := by rw [h.dc', hd, h.zc, hζ, map_neg]
  have hdacu : d (a (c u)) = -a (c u) := by rw [← h.ad', hdcu, map_neg]
  have hE2 : g 0 • u + g 1 • a u - g 2 • c u - g 3 • a (c u) = 0 := by
    have := congrArg d hg'
    simp only [map_add, map_smul, map_zero, hd, hdau, hdcu, hdacu, smul_neg] at this
    linear_combination (norm := module) this
  have hA : (2 : K) • (g 0 • u + g 1 • a u) = 0 := by
    linear_combination (norm := module) hg' + hE2
  have hB : (2 : K) • (g 2 • c u + g 3 • a (c u)) = 0 := by
    linear_combination (norm := module) hg' - hE2
  have hA' : g 0 • u + g 1 • a u = 0 := (smul_eq_zero.mp hA).resolve_left h2
  have hB' : g 2 • c u + g 3 • a (c u) = 0 := (smul_eq_zero.mp hB).resolve_left h2
  have hB'' : c (g 2 • u + g 3 • a u) = 0 := by
    rw [map_add, map_smul, map_smul, ← h.ac' u]
    exact hB'
  have hC : g 2 • u + g 3 • a u = 0 := h.c_inj hB''
  obtain ⟨h0, h1⟩ := hin _ _ hA'
  obtain ⟨h2', h3⟩ := hin _ _ hC
  intro i
  fin_cases i <;> simp [h0, h1, h2', h3]

theorem fixed_decomp (h2 : (2 : K) ≠ 0) {u : V} (hζ : ζ u = -u) (hd : d u = u)
    (hin : ∀ x y : K, x • u + y • a u = 0 → x = 0 ∧ y = 0)
    (hspan : Submodule.span K (Set.range ![u, a u, c u, a (c u)]) = ⊤) {w : V} (hw : d w = w) :
    ∃ x y : K, w = x • u + y • a u := by
  have hwm : w ∈ Submodule.span K (Set.range ![u, a u, c u, a (c u)]) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hwm
  have hg' : g 0 • u + g 1 • a u + g 2 • c u + g 3 • a (c u) = w := by
    simpa [Fin.sum_univ_four] using hg
  have hdau : d (a u) = a u := by rw [← h.ad', hd]
  have hdcu : d (c u) = -c u := by rw [h.dc', hd, h.zc, hζ, map_neg]
  have hdacu : d (a (c u)) = -a (c u) := by rw [← h.ad', hdcu, map_neg]
  have hE2 : g 0 • u + g 1 • a u - g 2 • c u - g 3 • a (c u) = w := by
    have := congrArg d hg'
    simp only [map_add, map_smul, hw, hd, hdau, hdcu, hdacu, smul_neg] at this
    linear_combination (norm := module) this
  have hB : (2 : K) • (g 2 • c u + g 3 • a (c u)) = 0 := by
    linear_combination (norm := module) hg' - hE2
  have hB' : g 2 • c u + g 3 • a (c u) = 0 := (smul_eq_zero.mp hB).resolve_left h2
  have hB'' : c (g 2 • u + g 3 • a u) = 0 := by
    rw [map_add, map_smul, map_smul, ← h.ac' u]
    exact hB'
  have hC : g 2 • u + g 3 • a u = 0 := h.c_inj hB''
  obtain ⟨h2', h3⟩ := hin _ _ hC
  refine ⟨g 0, g 1, ?_⟩
  rw [← hg', h2', h3]
  simp

theorem commutant_scalar (h2 : (2 : K) ≠ 0) (hV : finrank K V = 4) (G : Module.End K V)
    (hGa : G * a = a * G) (hGb : G * b = b * G) (hGc : G * c = c * G) (hGd : G * d = d * G) :
    ζ = -1 ∧ ∃ k : K, G = k • (1 : Module.End K V) := by
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨u, hζ, hd, hin⟩ := h.exists_u h2
  have hu0 : u ≠ 0 := by
    intro h0
    have := (hin 1 0 (by simp [h0])).1
    exact one_ne_zero this
  have hli := h.four_indep h2 hζ hd hin
  have hspan : Submodule.span K (Set.range ![u, a u, c u, a (c u)]) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank' hli (by simp [hV])
  have hGa' : ∀ v, G (a v) = a (G v) := fun v => by
    rw [← Module.End.mul_apply, hGa, Module.End.mul_apply]
  have hGb' : ∀ v, G (b v) = b (G v) := fun v => by
    rw [← Module.End.mul_apply, hGb, Module.End.mul_apply]
  have hGc' : ∀ v, G (c v) = c (G v) := fun v => by
    rw [← Module.End.mul_apply, hGc, Module.End.mul_apply]
  have hGd' : ∀ v, d (G v) = G (d v) := fun v => by
    rw [← Module.End.mul_apply, ← hGd, Module.End.mul_apply]
  have hζall : ∀ v, ζ v = -v := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range ![u, a u, c u, a (c u)]) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
    have hg' : g 0 • u + g 1 • a u + g 2 • c u + g 3 • a (c u) = v := by
      simpa [Fin.sum_univ_four] using hg
    have e1 : ζ (a u) = -a u := by rw [h.za, hζ, map_neg]
    have e2 : ζ (c u) = -c u := by rw [h.zc, hζ, map_neg]
    have e3 : ζ (a (c u)) = -a (c u) := by rw [h.za, e2, map_neg]
    rw [← hg']
    simp only [map_add, map_smul, hζ, e1, e2, e3, smul_neg, neg_add]
  refine ⟨LinearMap.ext fun v => by simpa using hζall v, ?_⟩
  obtain ⟨x₁, x₂, hGu⟩ := h.fixed_decomp h2 hζ hd hin hspan (w := G u) (by rw [hGd', hd])
  obtain ⟨y₁, y₂, hbu⟩ := h.fixed_decomp h2 hζ hd hin hspan (w := b u)
    (by rw [← h.bd' u, hd])
  have haau : a (a u) = -u := by rw [h.aa', hζall]
  have hbau : b (a u) = -a (b u) := by rw [h.ba', hζall]
  have habu : a (b u) = y₁ • a u - y₂ • u := by
    rw [hbu, map_add, map_smul, map_smul, haau]
    module
  have hL : G (b u) = (y₁ * x₁ - y₂ * x₂) • u + (y₁ * x₂ + y₂ * x₁) • a u := by
    rw [hbu, map_add, map_smul, map_smul, hGa', hGu, map_add, map_smul, map_smul, haau]
    module
  have hR : b (G u) = (x₁ * y₁ + x₂ * y₂) • u + (x₁ * y₂ - x₂ * y₁) • a u := by
    rw [hGu, map_add, map_smul, map_smul, hbau, smul_neg, habu, hbu]
    module
  have hkey : (-(2 * (x₂ * y₂))) • u + (2 * (x₂ * y₁)) • a u = 0 := by
    have e1 : G (b u) = b (G u) := hGb' u
    rw [hL, hR] at e1
    linear_combination (norm := module) e1
  obtain ⟨hk1, hk2⟩ := hin _ _ hkey
  have hx₂ : x₂ = 0 := by
    by_contra hne
    have hy₂ : y₂ = 0 := by
      have : 2 * (x₂ * y₂) = 0 := by linear_combination -hk1
      rcases mul_eq_zero.mp this with h6 | h6
      · exact absurd h6 h2
      · exact (mul_eq_zero.mp h6).resolve_left hne
    have hy₁ : y₁ = 0 := by
      rcases mul_eq_zero.mp hk2 with h6 | h6
      · exact absurd h6 h2
      · exact (mul_eq_zero.mp h6).resolve_left hne
    apply hu0
    apply h.b_inj
    rw [hbu, hy₁, hy₂]
    simp
  rw [hx₂, zero_smul, add_zero] at hGu
  refine ⟨x₁, LinearMap.ext_on hspan ?_⟩
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · simpa using hGu
  · simp [hGa', hGu]
  · simp [hGc', hGu]
  · simp [hGa', hGc', hGu]

end QDRel

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026

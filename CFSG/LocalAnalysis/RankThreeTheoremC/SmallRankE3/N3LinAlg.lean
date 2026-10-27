module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

structure Q8D8Op (I J R T Z : Module.End F V) : Prop where
  zz : Z * Z = 1
  ii : I * I = Z
  jj : J * J = Z
  rr : R * R = Z
  tt : T * T = 1
  ij : I * J = Z * (J * I)
  tr : T * R = Z * (R * T)
  ir : I * R = R * I
  it : I * T = T * I
  jr : J * R = R * J
  jt : J * T = T * J
  zi : Z * I = I * Z
  zj : Z * J = J * Z
  zr : Z * R = R * Z
  zt : Z * T = T * Z

theorem dep_pair {x y : V} (hx : x ≠ 0) (hdep : ¬ LinearIndependent F ![x, y]) :
    ∃ c : F, y = c • x := by
  by_contra hno
  apply hdep
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra ht
    apply hno
    refine ⟨-(t⁻¹ * s), ?_⟩
    have h1 : t • y = -(s • x) := eq_neg_of_add_eq_zero_right hst
    calc y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = t⁻¹ • (-(s • x)) := by rw [h1]
      _ = (-(t⁻¹ * s)) • x := by rw [smul_neg, smul_smul, neg_smul]
  have hs : s • x = 0 := by
    rw [ht, zero_smul, add_zero] at hst
    exact hst
  rcases smul_eq_zero.mp hs with hs0 | hs0
  · exact ⟨hs0, ht⟩
  · exact absurd hs0 hx

namespace Q8D8Op

variable {I J R T Z : Module.End F V} (h : Q8D8Op I J R T Z)
include h

theorem Z_Z_apply (v : V) : Z (Z v) = v := LinearMap.congr_fun h.zz v

theorem T_T_apply (v : V) : T (T v) = v := LinearMap.congr_fun h.tt v

theorem I_eq_zero {v : V} (hv : I v = 0) : v = 0 := by
  have e : I (I v) = Z v := LinearMap.congr_fun h.ii v
  have hZv : Z v = 0 := by
    rw [← e, hv, map_zero]
  calc v = Z (Z v) := (h.Z_Z_apply v).symm
    _ = 0 := by rw [hZv, map_zero]

theorem J_eq_zero {v : V} (hv : J v = 0) : v = 0 := by
  have e : J (J v) = Z v := LinearMap.congr_fun h.jj v
  have hZv : Z v = 0 := by
    rw [← e, hv, map_zero]
  calc v = Z (Z v) := (h.Z_Z_apply v).symm
    _ = 0 := by rw [hZv, map_zero]

theorem R_eq_zero {v : V} (hv : R v = 0) : v = 0 := by
  have e : R (R v) = Z v := LinearMap.congr_fun h.rr v
  have hZv : Z v = 0 := by
    rw [← e, hv, map_zero]
  calc v = Z (Z v) := (h.Z_Z_apply v).symm
    _ = 0 := by rw [hZv, map_zero]

theorem neg_stable {v : V} (hv : Z v = -v) :
    Z (I v) = -(I v) ∧ Z (J v) = -(J v) ∧ Z (R v) = -(R v) ∧ Z (T v) = -(T v) := by
  have eI : Z (I v) = I (Z v) := LinearMap.congr_fun h.zi v
  have eJ : Z (J v) = J (Z v) := LinearMap.congr_fun h.zj v
  have eR : Z (R v) = R (Z v) := LinearMap.congr_fun h.zr v
  have eT : Z (T v) = T (Z v) := LinearMap.congr_fun h.zt v
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eI, hv, map_neg]
  · rw [eJ, hv, map_neg]
  · rw [eR, hv, map_neg]
  · rw [eT, hv, map_neg]

theorem anti_IJ {v : V} (hv : Z v = -v) : I (J v) = -(J (I v)) := by
  have hIv : Z (I v) = -(I v) := (h.neg_stable hv).1
  have hJIv : Z (J (I v)) = -(J (I v)) := (h.neg_stable hIv).2.1
  have e : I (J v) = Z (J (I v)) := LinearMap.congr_fun h.ij v
  rw [e, hJIv]

theorem anti_TR {v : V} (hv : Z v = -v) : T (R v) = -(R (T v)) := by
  have hTv : Z (T v) = -(T v) := (h.neg_stable hv).2.2.2
  have hRTv : Z (R (T v)) = -(R (T v)) := (h.neg_stable hTv).2.2.1
  have e : T (R v) = Z (R (T v)) := LinearMap.congr_fun h.tr v
  rw [e, hRTv]

theorem indep_I_or_J (h2 : (2 : F) ≠ 0) {v : V} (hv : Z v = -v) (hv0 : v ≠ 0) :
    LinearIndependent F ![v, I v] ∨ LinearIndependent F ![v, J v] := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hI, hJ⟩ := hcon
  obtain ⟨c, hc⟩ := dep_pair hv0 hI
  obtain ⟨d, hd⟩ := dep_pair hv0 hJ
  have hIJ : I (J v) = (d * c) • v := by
    rw [hd, map_smul, hc, smul_smul]
  have hJI : J (I v) = (c * d) • v := by
    rw [hc, map_smul, hd, smul_smul]
  have hanti : (d * c) • v = -((c * d) • v) := by
    rw [← hIJ, ← hJI]
    exact h.anti_IJ hv
  have key : (2 * (c * d)) • v = 0 := by
    have h3 : (d * c + c * d) • v = 0 := by
      rw [add_smul]
      exact eq_neg_iff_add_eq_zero.mp hanti
    have h4 : d * c + c * d = 2 * (c * d) := by ring
    rw [← h4]
    exact h3
  rcases smul_eq_zero.mp key with h5 | h5
  · rcases mul_eq_zero.mp h5 with h6 | h6
    · exact h2 h6
    · rcases mul_eq_zero.mp h6 with h7 | h7
      · apply hv0
        apply h.I_eq_zero
        rw [hc, h7, zero_smul]
      · apply hv0
        apply h.J_eq_zero
        rw [hd, h7, zero_smul]
  · exact hv0 h5

theorem indep_four (h2 : (2 : F) ≠ 0) {u : V} (hu : Z u = -u) (hTu : T u = u) {A : Module.End F V}
    (hAT : A * T = T * A) (hAR : A * R = R * A) (hAZ : Z * A = A * Z)
    (hA : LinearIndependent F ![u, A u]) :
    LinearIndependent F ![u, A u, R u, R (A u)] := by
  have hAu : Z (A u) = -(A u) := by
    have e : Z (A u) = A (Z u) := LinearMap.congr_fun hAZ u
    rw [e, hu, map_neg]
  have hTAu : T (A u) = A u := by
    have e : A (T u) = T (A u) := LinearMap.congr_fun hAT u
    rw [← e, hTu]
  have hT1 : T (R u) = -(R u) := by
    have e := h.anti_TR hu
    rwa [hTu] at e
  have hT2 : T (R (A u)) = -(R (A u)) := by
    have e := h.anti_TR hAu
    rwa [hTAu] at e
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • u + g 1 • A u + g 2 • R u + g 3 • R (A u) = 0 := by
    simpa [Fin.sum_univ_four] using hg
  have eT : T (g 0 • u + g 1 • A u + g 2 • R u + g 3 • R (A u)) = 0 := by
    rw [hg', map_zero]
  simp only [map_add, map_smul, hTu, hTAu, hT1, hT2, smul_neg] at eT
  have hP : g 0 • u + g 1 • A u = 0 := by
    have h3 : (2 : F) • (g 0 • u + g 1 • A u) = 0 := by
      linear_combination (norm := module) hg' + eT
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 h2
    · exact h4
  have hQ : g 2 • R u + g 3 • R (A u) = 0 := by
    have h3 : (2 : F) • (g 2 • R u + g 3 • R (A u)) = 0 := by
      linear_combination (norm := module) hg' - eT
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 h2
    · exact h4
  have hRQ : R (g 2 • u + g 3 • A u) = 0 := by
    rw [map_add, map_smul, map_smul]
    exact hQ
  have hQ' : g 2 • u + g 3 • A u = 0 := h.R_eq_zero hRQ
  have hc01 := LinearIndependent.pair_iff.mp hA (g 0) (g 1) hP
  have hc23 := LinearIndependent.pair_iff.mp hA (g 2) (g 3) hQ'
  intro i
  fin_cases i
  · exact hc01.1
  · exact hc01.2
  · exact hc23.1
  · exact hc23.2

theorem Z_eq_neg_one [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (hdim : Module.finrank F V = 4)
    (hZ1 : Z ≠ 1) : Z = -1 := by
  obtain ⟨w, hw0, hwZ⟩ : ∃ w : V, w ≠ 0 ∧ Z w = -w := by
    have hex : ∃ v : V, Z v ≠ v := by
      by_contra hcon
      apply hZ1
      apply LinearMap.ext
      intro v
      by_contra hv
      rw [Module.End.one_apply] at hv
      exact hcon ⟨v, hv⟩
    obtain ⟨v, hv⟩ := hex
    refine ⟨v - Z v, ?_, ?_⟩
    · intro h0
      exact hv (sub_eq_zero.mp h0).symm
    · rw [map_sub, h.Z_Z_apply, neg_sub]
  obtain ⟨u, hu0, hZu, hTu⟩ : ∃ u : V, u ≠ 0 ∧ Z u = -u ∧ T u = u := by
    have hTw : T (T w) = w := h.T_T_apply w
    have hZTw : Z (T w) = -(T w) := (h.neg_stable hwZ).2.2.2
    by_cases hu1 : w + T w = 0
    · have hu2 : w - T w ≠ 0 := by
        intro hu2
        apply hw0
        have h2w : (2 : F) • w = 0 := by
          rw [two_smul]
          calc w + w = (w + T w) + (w - T w) := by abel
            _ = 0 := by rw [hu1, hu2, add_zero]
        rcases smul_eq_zero.mp h2w with h4 | h4
        · exact absurd h4 h2
        · exact h4
      have hZu2 : Z (w - T w) = -(w - T w) := by
        rw [map_sub, hwZ, hZTw]
        abel
      have hTu2 : T (w - T w) = -(w - T w) := by
        rw [map_sub, hTw, neg_sub]
      refine ⟨R (w - T w), ?_, ?_, ?_⟩
      · intro hR
        exact hu2 (h.R_eq_zero hR)
      · exact (h.neg_stable hZu2).2.2.1
      · rw [h.anti_TR hZu2, hTu2, map_neg, neg_neg]
    · refine ⟨w + T w, hu1, ?_, ?_⟩
      · rw [map_add, hwZ, hZTw]
        abel
      · rw [map_add, hTw, add_comm]
  obtain ⟨A, hAT, hAR, hAZ, hA⟩ : ∃ A : Module.End F V, A * T = T * A ∧ A * R = R * A ∧
      Z * A = A * Z ∧ LinearIndependent F ![u, A u] := by
    rcases h.indep_I_or_J h2 hZu hu0 with hA | hA
    · exact ⟨I, h.it, h.ir, h.zi, hA⟩
    · exact ⟨J, h.jt, h.jr, h.zj, hA⟩
  have hind := h.indep_four h2 hZu hTu hAT hAR hAZ hA
  have hAZu : Z (A u) = -(A u) := by
    have e : Z (A u) = A (Z u) := LinearMap.congr_fun hAZ u
    rw [e, hZu, map_neg]
  have hRZu : Z (R u) = -(R u) := (h.neg_stable hZu).2.2.1
  have hRAZu : Z (R (A u)) = -(R (A u)) := (h.neg_stable hAZu).2.2.1
  have hmem : ∀ x : V, Z x = -x → x ∈ LinearMap.ker (Z + 1) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, hx, neg_add_cancel]
  have hsub : Submodule.span F (Set.range ![u, A u, R u, R (A u)]) ≤ LinearMap.ker (Z + 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hmem u hZu
    · exact hmem (A u) hAZu
    · exact hmem (R u) hRZu
    · exact hmem (R (A u)) hRAZu
  have hcard := finrank_span_eq_card hind
  rw [Fintype.card_fin] at hcard
  have hle1 := Submodule.finrank_mono hsub
  have hle2 := Submodule.finrank_le (LinearMap.ker (Z + 1))
  have hW : LinearMap.ker (Z + 1) = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  have hall : ∀ x : V, Z x = -x := by
    intro x
    have hx : x ∈ LinearMap.ker (Z + 1) := by
      rw [hW]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hx
    exact eq_neg_of_add_eq_zero_left hx
  apply LinearMap.ext
  intro x
  rw [hall x, LinearMap.neg_apply, Module.End.one_apply]

end Q8D8Op

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

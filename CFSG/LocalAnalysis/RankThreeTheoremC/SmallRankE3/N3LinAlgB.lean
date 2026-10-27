module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3LinAlg
public import Mathlib.LinearAlgebra.Center

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem n3_comm_apply {X Y : Module.End F V} (hXY : X * Y = Y * X) (v : V) :
    X (Y v) = Y (X v) := by
  simpa only [Module.End.mul_apply] using LinearMap.congr_fun hXY v

theorem n3_exists_smul_of_not_li {x y : V} (hx : x ≠ 0) (hxy : ¬LinearIndependent F ![x, y]) :
    ∃ c : F, y = c • x := by
  have key : ∃ s t : F, s • x + t • y = 0 ∧ ¬(s = 0 ∧ t = 0) := by
    by_contra hcon
    apply hxy
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_contra hne
    exact hcon ⟨s, t, hst, hne⟩
  obtain ⟨s, t, hst, hne⟩ := key
  have ht : t ≠ 0 := by
    intro ht0
    subst ht0
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    rcases hst with hs | hs
    · exact hne ⟨hs, rfl⟩
    · exact hx hs
  have h1 : t • y = -(s • x) := eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hst)
  refine ⟨-(s / t), ?_⟩
  calc y = t⁻¹ • (t • y) := (inv_smul_smul₀ ht y).symm
    _ = t⁻¹ • (-(s • x)) := by rw [h1]
    _ = -(s / t) • x := by rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem n3_not_li_of_smul {x y : V} {c : F} (hc : y = c • x) :
    ¬LinearIndependent F ![x, y] := by
  intro hli
  have h1 := LinearIndependent.pair_iff.mp hli c (-1) (by rw [hc]; simp)
  exact one_ne_zero (neg_eq_zero.mp h1.2)

namespace Q8D8Op

variable {I J R T Z : Module.End F V} (h : Q8D8Op I J R T Z)
include h

theorem form_of_fixed {g : Module.End F V} {u : V} (h2 : (2 : F) ≠ 0) (hTu : T u = u)
    (hTgu : T (g u) = g u) (hTRu : T (R u) = -(R u)) (hTRgu : T (R (g u)) = -(R (g u)))
    (hli : LinearIndependent F ![u, g u, R u, R (g u)])
    (hspan : ∀ w : V, ∃ c : Fin 4 → F, c 0 • u + c 1 • g u + c 2 • R u + c 3 • R (g u) = w)
    (X : Module.End F V) (hTX : T (X u) = X u) :
    ∃ a b : F, X u = a • u + b • g u := by
  obtain ⟨c, hc⟩ := hspan (X u)
  have hTc : T (c 0 • u + c 1 • g u + c 2 • R u + c 3 • R (g u)) =
      c 0 • u + c 1 • g u + -(c 2 • R u) + -(c 3 • R (g u)) := by
    simp only [map_add, map_smul, hTu, hTgu, hTRu, hTRgu, smul_neg]
  have hrel : c 0 • u + c 1 • g u + -(c 2 • R u) + -(c 3 • R (g u)) =
      c 0 • u + c 1 • g u + c 2 • R u + c 3 • R (g u) := by
    rw [← hTc, hc, hTX]
  have hB : (2 * c 2) • R u + (2 * c 3) • R (g u) = 0 := by
    linear_combination (norm := module) (-1 : F) • hrel
  have hfun := Fintype.linearIndependent_iff.mp hli ![0, 0, 2 * c 2, 2 * c 3]
    (by simpa [Fin.sum_univ_four] using hB)
  have h2c2 : 2 * c 2 = 0 := hfun 2
  have h2c3 : 2 * c 3 = 0 := hfun 3
  have hc2 : c 2 = 0 := (mul_eq_zero.mp h2c2).resolve_left h2
  have hc3 : c 3 = 0 := (mul_eq_zero.mp h2c3).resolve_left h2
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc]
  simp [hc2, hc3]

theorem false_of_li_fixed [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hdim : Module.finrank F V = 4) (hZ : Z = -1) {g : Module.End F V}
    (hI : g * I = I * g) (hJ : g * J = J * g) (hR : g * R = R * g) (hT : g * T = T * g)
    {u : V} (hu0 : u ≠ 0) (hTu : T u = u) (hli : LinearIndependent F ![u, g u]) : False := by
  have hZv : ∀ v : V, Z v = -v := fun v => by simp [hZ]
  have hZg : Z * g = g * Z := by simp [hZ]
  have hTgu : T (g u) = g u := by rw [← n3_comm_apply hT u, hTu]
  have hTRu : T (R u) = -(R u) := by rw [h.anti_TR (hZv u), hTu]
  have hTRgu : T (R (g u)) = -(R (g u)) := by rw [h.anti_TR (hZv (g u)), hTgu]
  have hli4 : LinearIndependent F ![u, g u, R u, R (g u)] :=
    h.indep_four h2 (hZv u) hTu hT hR hZg hli
  have hspan : ∀ w : V, ∃ c : Fin 4 → F,
      c 0 • u + c 1 • g u + c 2 • R u + c 3 • R (g u) = w := by
    intro w
    have hcard : Fintype.card (Fin 4) = Module.finrank F V := by
      rw [Fintype.card_fin, hdim]
    have htop := hli4.span_eq_top_of_card_eq_finrank hcard
    have hw : w ∈ Submodule.span F (Set.range ![u, g u, R u, R (g u)]) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hw
    exact ⟨c, by rw [← hc]; simp [Fin.sum_univ_four]⟩
  have hTI : T (I u) = I u := by rw [← n3_comm_apply h.it u, hTu]
  have hTJ : T (J u) = J u := by rw [← n3_comm_apply h.jt u, hTu]
  obtain ⟨a1, a2, hIu⟩ := h.form_of_fixed h2 hTu hTgu hTRu hTRgu hli4 hspan I hTI
  obtain ⟨b1, b2, hJu⟩ := h.form_of_fixed h2 hTu hTgu hTRu hTRgu hli4 hspan J hTJ
  have e1 : I (J u) = b1 • I u + b2 • I (g u) := by
    rw [hJu, map_add, map_smul, map_smul]
  have e2 : J (I u) = a1 • J u + a2 • J (g u) := by
    rw [hIu, map_add, map_smul, map_smul]
  have e3 : I (g u) = a1 • g u + a2 • g (g u) := by
    rw [← n3_comm_apply hI u, hIu, map_add, map_smul, map_smul]
  have e4 : J (g u) = b1 • g u + b2 • g (g u) := by
    rw [← n3_comm_apply hJ u, hJu, map_add, map_smul, map_smul]
  have hIJ : I (J u) = J (I u) := by
    rw [e1, e2, e3, e4, hIu, hJu]
    module
  have hx : J (I u) = -(J (I u)) := by
    have := h.anti_IJ (hZv u)
    rwa [hIJ] at this
  have hx2 : (2 : F) • J (I u) = 0 := by
    linear_combination (norm := module) hx
  have hy : J (I u) = 0 := (smul_eq_zero.mp hx2).resolve_left h2
  have hIJ0 : I (J u) = 0 := by rw [hIJ, hy]
  exact hu0 (h.J_eq_zero (h.I_eq_zero hIJ0))

theorem eig_fixed [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hdim : Module.finrank F V = 4) (hZ : Z = -1) {g : Module.End F V}
    (hI : g * I = I * g) (hJ : g * J = J * g) (hR : g * R = R * g) (hT : g * T = T * g)
    {u : V} (hu0 : u ≠ 0) (hTu : T u = u) : ∃ c : F, g u = c • u := by
  by_cases hli : LinearIndependent F ![u, g u]
  · exact (h.false_of_li_fixed h2 hdim hZ hI hJ hR hT hu0 hTu hli).elim
  · exact n3_exists_smul_of_not_li hu0 hli

theorem eig_eq_of_fixed [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hdim : Module.finrank F V = 4) (hZ : Z = -1) {g : Module.End F V}
    (hI : g * I = I * g) (hJ : g * J = J * g) (hR : g * R = R * g) (hT : g * T = T * g)
    {p q : V} (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hTp : T p = p) (hTq : T q = q)
    {a b : F} (hgp : g p = a • p) (hgq : g q = b • q) : a = b := by
  by_cases hli : LinearIndependent F ![p, q]
  · have hTs : T (p + q) = p + q := by rw [map_add, hTp, hTq]
    have hs0 : p + q ≠ 0 := by
      intro hs
      have h1 := LinearIndependent.pair_iff.mp hli 1 1 (by rw [one_smul, one_smul]; exact hs)
      exact one_ne_zero h1.1
    obtain ⟨c, hc⟩ := h.eig_fixed h2 hdim hZ hI hJ hR hT hs0 hTs
    have hgs : g (p + q) = a • p + b • q := by rw [map_add, hgp, hgq]
    have hac : a • p + b • q = c • (p + q) := by
      rw [← hgs]
      exact hc
    have hlin : (a - c) • p + (b - c) • q = 0 := by
      linear_combination (norm := module) hac
    have h1 := LinearIndependent.pair_iff.mp hli (a - c) (b - c) hlin
    exact (sub_eq_zero.mp h1.1).trans (sub_eq_zero.mp h1.2).symm
  · obtain ⟨d, hd⟩ := n3_exists_smul_of_not_li hp0 hli
    have hga' : g q = a • q := by
      rw [hd, map_smul, hgp]
      module
    have hab : (a - b) • q = 0 := by
      rw [sub_smul, ← hga', hgq, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hab).resolve_right hq0)

theorem scalar_of_commute [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hdim : Module.finrank F V = 4) (hZ : Z = -1) {g : Module.End F V}
    (hI : g * I = I * g) (hJ : g * J = J * g) (hR : g * R = R * g) (hT : g * T = T * g) :
    ∃ a : F, g = a • (1 : Module.End F V) := by
  have hZv : ∀ v : V, Z v = -v := fun v => by simp [hZ]
  have hEig : ∀ x : V, T x = x → ∃ c : F, g x = c • x := by
    intro x hx
    by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    · exact h.eig_fixed h2 hdim hZ hI hJ hR hT hx0 hx
  have hall : ∀ v : V, ∃ c : F, g v = c • v := by
    intro v
    have hTp : T (v + T v) = v + T v := by rw [map_add, h.T_T_apply, add_comm]
    have hTm : T (v - T v) = -(v - T v) := by rw [map_sub, h.T_T_apply, neg_sub]
    have hTq : T (R (v - T v)) = R (v - T v) := by
      rw [h.anti_TR (hZv (v - T v)), hTm, map_neg, neg_neg]
    obtain ⟨a, hga⟩ := hEig _ hTp
    obtain ⟨b, hgb⟩ := hEig _ hTq
    have hgm : g (v - T v) = b • (v - T v) := by
      have hRm : R (g (v - T v)) = R (b • (v - T v)) := by
        rw [← n3_comm_apply hR (v - T v), hgb, map_smul]
      have h0 : R (g (v - T v) - b • (v - T v)) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact hRm
      exact sub_eq_zero.mp (h.R_eq_zero h0)
    have hc : ∃ c : F, g (v + T v) = c • (v + T v) ∧ g (v - T v) = c • (v - T v) := by
      by_cases hp : v + T v = 0
      · exact ⟨b, by rw [hp, map_zero, smul_zero], hgm⟩
      · by_cases hm : v - T v = 0
        · exact ⟨a, hga, by rw [hm, map_zero, smul_zero]⟩
        · have hRm0 : R (v - T v) ≠ 0 := fun h0 => hm (h.R_eq_zero h0)
          have hab : a = b :=
            h.eig_eq_of_fixed h2 hdim hZ hI hJ hR hT hp hRm0 hTp hTq hga hgb
          exact ⟨a, hga, by rw [hab]; exact hgm⟩
    obtain ⟨c, hgp, hgm'⟩ := hc
    have hpm : (2 : F) • v = (v + T v) + (v - T v) := by
      rw [two_smul]
      abel
    have hg2 : (2 : F) • g v = g (v + T v) + g (v - T v) := by
      rw [← map_add g, ← hpm, map_smul]
    have hfin : (2 : F) • g v = (2 : F) • (c • v) := by
      rw [hg2, hgp, hgm']
      module
    rw [← sub_eq_zero, ← smul_sub] at hfin
    exact ⟨c, sub_eq_zero.mp ((smul_eq_zero.mp hfin).resolve_left h2)⟩
  have hnli : ∀ v : V, ¬LinearIndependent F ![v, g v] := by
    intro v
    obtain ⟨c, hc⟩ := hall v
    exact n3_not_li_of_smul hc
  exact LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hnli

end Q8D8Op

theorem la_scalar [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (hdim : Module.finrank F V = 4)
    {I J R T Z : Module.End F V} (h : Q8D8Op I J R T Z) (hZ1 : Z ≠ 1) :
    Z = -1 ∧ ∀ g : Module.End F V, g * I = I * g → g * J = J * g → g * R = R * g →
      g * T = T * g → ∃ a : F, g = a • (1 : Module.End F V) := by
  have hZ := h.Z_eq_neg_one h2 hdim hZ1
  exact ⟨hZ, fun g hI hJ hR hT => h.scalar_of_commute h2 hdim hZ hI hJ hR hT⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

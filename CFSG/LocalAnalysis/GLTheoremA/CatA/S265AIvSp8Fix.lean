module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

omit [Module.Finite (ZMod 2) V] in
private theorem two_add_self (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem fixed_of_isotropic_pair {B : LinearMap.BilinForm (ZMod 2) V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {D : V ≃ₗ[ZMod 2] V} (hD : ∀ u v, B (D u) (D v) = B u v)
    (hD3 : D ^ 3 = 1)
    (hdim : Nat.card ↥(LinearMap.ker ((D : V →ₗ[ZMod 2] V) - 1)) * 4 = Nat.card V)
    {y : V} (hy : B y (D y) = 0) : D y = y := by
  classical
  set N : V →ₗ[ZMod 2] V := (D : V →ₗ[ZMod 2] V) - 1 with hNdef
  have hN : ∀ x, N x = D x - x := fun x => by simp [hNdef]
  have hD3' : ∀ x, D (D (D x)) = x := fun x => by
    have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e x) hD3
    simpa [pow_three] using h
  have hneg : ∀ a : ZMod 2, -a = a := by decide
  have hsym : ∀ x z, B x z = B z x := fun x z => (hneg (B x z)).symm.trans (hB.neg_eq x z)
  set K := LinearMap.ker N with hK
  set P := LinearMap.range N with hP
  have hdimf : Module.finrank (ZMod 2) K + 2 = Module.finrank (ZMod 2) V := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod] at h1 h2
    refine Nat.pow_right_injective (le_refl 2) ?_
    show 2 ^ (Module.finrank (ZMod 2) K + 2) = 2 ^ Module.finrank (ZMod 2) V
    rw [pow_add, ← h1, ← h2]
    exact hdim
  have hPdim : Module.finrank (ZMod 2) P = 2 := by
    have h := N.finrank_range_add_finrank_ker
    rw [← hK, ← hP] at h
    omega
  have hKfix : ∀ c ∈ K, D c = c := fun c hc =>
    sub_eq_zero.mp ((hN c).symm.trans (LinearMap.mem_ker.mp hc))
  have hPD : ∀ p ∈ P, D p ∈ P := by
    rintro _ ⟨t, rfl⟩
    exact ⟨D t, by rw [hN, hN, map_sub]⟩
  have hKP : ∀ c ∈ K, ∀ p ∈ P, B c p = 0 := by
    rintro c hc _ ⟨x, rfl⟩
    have h1 := hD c x
    rw [hKfix c hc] at h1
    rw [hN, map_sub, h1, sub_self]
  have hKP0 : ∀ p ∈ K, p ∈ P → p = 0 := by
    rintro _ hpK ⟨t, rfl⟩
    have h1 : D (N t) = N t := hKfix _ hpK
    rw [hN, map_sub] at h1
    have e : D (D t) - t = (D (D t) - D t) + (D t - t) := by abel
    rw [h1, two_add_self, sub_eq_zero] at e
    have h3 : D t = t := by
      have := hD3' t
      rwa [e] at this
    rw [hN]
    exact sub_eq_zero.mpr h3
  obtain ⟨w, hw⟩ : ∃ w, w = y + D y + D (D y) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = y - w := ⟨_, rfl⟩
  have hwK : w ∈ K := by
    rw [hK, LinearMap.mem_ker, hN, hw]
    simp only [map_add]
    rw [hD3']
    abel
  have huP : u ∈ P := by
    refine ⟨D y, ?_⟩
    rw [hN, hu, hw]
    have e : D (D y) - D y - (y - (y + D y + D (D y))) = D (D y) + D (D y) := by abel
    rw [two_add_self] at e
    exact sub_eq_zero.mp e
  have hDu : D u ∈ P := hPD u huP
  have hBu : B u (D u) = 0 := by
    have hyw : y = w + u := by rw [hu]; abel
    have hDw : D w = w := hKfix w hwK
    rw [hyw] at hy
    simp only [map_add, LinearMap.add_apply, hDw] at hy
    have h1 : B w (D u) = 0 := hKP w hwK _ hDu
    have h2 : B u w = 0 := by rw [hsym]; exact hKP w hwK u huP
    simpa [hB.self_eq_zero, h1, h2] using hy
  have hu0 : u = 0 := by
    by_contra hne
    set S : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {u, D u} with hS
    have hSP : S ≤ P := Submodule.span_le.mpr (by
      rintro z (rfl | rfl)
      · exact huP
      · exact hDu)
    have hlt : Submodule.span (ZMod 2) {u} < S := by
      refine lt_of_le_of_ne (Submodule.span_mono (by simp)) fun heq => ?_
      have hmem : D u ∈ Submodule.span (ZMod 2) {u} :=
        heq ▸ Submodule.subset_span (by simp)
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · rw [zero_smul] at hc
        exact hne (D.injective (by rw [← hc, map_zero]))
      · rw [one_smul] at hc
        exact hne (hKP0 u (LinearMap.mem_ker.mpr
          (by rw [hN]; exact sub_eq_zero.mpr hc.symm)) huP)
    have hS2 : 2 ≤ Module.finrank (ZMod 2) S := by
      have h1 := Submodule.finrank_lt_finrank_of_lt hlt
      have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {u}) = 1 :=
        finrank_span_singleton hne
      omega
    have hSeq : S = P := Submodule.eq_of_le_of_finrank_le hSP (by omega)
    have hBDu : B (D u) u = 0 := by rw [hsym]; exact hBu
    have hPP : ∀ p ∈ P, ∀ q ∈ P, B p q = 0 := by
      intro p hp q hq
      rw [← hSeq] at hp hq
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
      obtain ⟨a', b', rfl⟩ := Submodule.mem_span_pair.mp hq
      simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        hB.self_eq_zero, hBu, hBDu]
    have hKle : K ≤ B.orthogonal P := fun c hc p hp => by
      rw [hsym]
      exact hKP c hc p hp
    have hKeq : K = B.orthogonal P := by
      refine Submodule.eq_of_le_of_finrank_le hKle ?_
      rw [LinearMap.BilinForm.finrank_orthogonal hnd]
      omega
    have hPK : P ≤ K := hKeq ▸ fun p hp n hn => hPP n hn p hp
    exact hne (hKP0 u (hPK huP) huP)
  have hyw : y = w := sub_eq_zero.mp (hu ▸ hu0)
  rw [hyw, hKfix w hwK]

end CFSG.LocalAnalysis.GLTheoremA.S265A

end

module

public import CFSG.RankThree.Classical.OddQuadraticFrame
public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace OmSeven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def GoodPair (Q : QuadraticForm K V) (g : V ≃ₗ[K] V) (x y : V) : Prop :=
  Q x = Q y ∧ polar Q x y = Q y ∧ Q y ≠ 0 ∧
    ((g x = x ∧ g y = y) ∨ (g x = -y ∧ g y = x - y))

theorem apply_apply_apply_of_pow_three {g : V ≃ₗ[K] V} (hg3 : g ^ 3 = 1) (v : V) :
    g (g (g v)) = v := by
  have h := congrArg (fun f : V ≃ₗ[K] V => f v) hg3
  simpa [pow_succ, LinearEquiv.mul_apply] using h

theorem exists_goodPair_of_fixed [Finite K] (hK : Odd (Nat.card K)) (h3 : (3 : K) ≠ 0)
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 3 ≤ Module.finrank K V) {g : V ≃ₗ[K] V} (hg : ∀ v, g v = v) :
    ∃ x y, GoodPair Q g x y := by
  have := Fintype.ofFinite K
  have hK' : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_odd hK'
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank K V = d := ⟨_, rfl⟩
  rw [hd] at hdim
  obtain ⟨v, hv, hva, hvd⟩ := exists_orthogonal_basis_quad_eq hK hd (by omega) Q hQ
    (one_ne_zero (α := K))
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  let i2 : Fin d := ⟨2, by omega⟩
  have e0 : Q (v i0) = 1 := hva i0 (by show 0 + 1 < d; omega)
  have e1 : Q (v i1) = 1 := hva i1 (by show 1 + 1 < d; omega)
  have e2 : Q (v i2) ≠ 0 := by
    by_cases h : 2 + 1 < d
    · rw [hva i2 (by show 2 + 1 < d; exact h)]
      exact one_ne_zero
    · have : i2 = ⟨d - 1, by omega⟩ := Fin.ext (by show 2 = d - 1; omega)
      rw [this]
      exact hvd
  have o01 : polar Q (v i0) (v i1) = 0 := hv _ _ (by simp [i0, i1, Fin.ext_iff])
  have o02 : polar Q (v i0) (v i2) = 0 := hv _ _ (by simp [i0, i2, Fin.ext_iff])
  have o12 : polar Q (v i1) (v i2) = 0 := hv _ _ (by simp [i1, i2, Fin.ext_iff])
  obtain ⟨s, t, -, -, hQb, -, -⟩ := exists_plane_step hK' Q o12
    (by rw [e1]; exact one_ne_zero) e2 h3
  set a := v i0 with ha
  set b := s • v i1 + t • v i2 with hb
  have hab : polar Q a b = 0 := polar_smul_add_smul_right_eq_zero Q o01 o02 s t
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hQy : Q (a + b) = 4 := by
    rw [QuadraticMap.map_add Q, hab, hQb, e0]
    norm_num
  refine ⟨(2 : K) • a, a + b, ?_, ?_, ?_, Or.inl ⟨hg _, hg _⟩⟩
  · rw [map_smul_eq_sq, hQy, e0]
    norm_num
  · rw [polar_smul_left_eq, polar_add_right, polar_self_eq_two_mul, hab, e0, hQy]
    norm_num
  · rw [hQy]
    exact h4

theorem exists_nonsingular_of_moved (h3 : (3 : K) ≠ 0) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : g ^ 3 = 1) {w : V} (hw : g w ≠ w) :
    ∃ u, u + g u + g (g u) = 0 ∧ Q u ≠ 0 := by
  have hg3' := apply_apply_apply_of_pow_three hg3
  by_contra! hno
  have hfix : ∀ v : V, g (v + g v + g (g v)) = v + g v + g (g v) := fun v => by
    rw [map_add, map_add, hg3' v]
    abel
  have hWadd : ∀ a b : V, a + g a + g (g a) = 0 → b + g b + g (g b) = 0 →
      (a + b) + g (a + b) + g (g (a + b)) = 0 := fun a b ha hb => by
    have : (a + b) + g (a + b) + g (g (a + b)) = (a + g a + g (g a)) + (b + g b + g (g b)) := by
      simp only [map_add]
      abel
    rw [this, ha, hb, add_zero]
  set s := w + g w + g (g w) with hs
  set u₀ : V := (3 : K) • w - s with hu₀
  have hu₀W : u₀ + g u₀ + g (g u₀) = 0 := by
    have h1 : u₀ + g u₀ + g (g u₀) = (3 : K) • s - ((3 : K) • s) := by
      rw [hu₀]
      simp only [map_sub, map_smul, hfix w, ← hs]
      simp only [hs, map_add]
      rw [hg3' w]
      module
    rw [h1, sub_self]
  have hu₀ne : u₀ ≠ 0 := by
    intro h
    apply hw
    have h1 : (3 : K) • w = s := sub_eq_zero.mp h
    have h2 : (3 : K) • g w = s := by
      rw [← map_smul, h1]
      exact hfix w
    exact (smul_right_injective V h3 (h2.trans h1.symm))
  apply hu₀ne
  apply eq_zero_of_polar_eq_zero hQ
  intro v
  set sv := v + g v + g (g v) with hsv
  set v₁ : V := (3 : K)⁻¹ • sv with hv₁
  set v₂ : V := v - v₁ with hv₂
  have hgv₁ : g v₁ = v₁ := by rw [hv₁, map_smul, hfix v]
  have hv₂W : v₂ + g v₂ + g (g v₂) = 0 := by
    have h3v : (3 : K) • v₁ = sv := by rw [hv₁, smul_smul, mul_inv_cancel₀ h3, one_smul]
    have h1 : v₂ + g v₂ + g (g v₂) = sv - (v₁ + g v₁ + g (g v₁)) := by
      rw [hv₂, hsv]
      simp only [map_sub]
      abel
    rw [h1, hgv₁, hgv₁, ← h3v]
    module
  have hp₂ : polar Q u₀ v₂ = 0 := by
    have h1 := QuadraticMap.map_add Q u₀ v₂
    rw [hno u₀ hu₀W, hno v₂ hv₂W, hno _ (hWadd _ _ hu₀W hv₂W)] at h1
    linear_combination -h1
  have hp₁ : polar Q u₀ v₁ = 0 := by
    have e1 : polar Q (g u₀) v₁ = polar Q u₀ v₁ := by
      conv_lhs => rw [← hgv₁]
      exact polar_map_of_mem hg u₀ v₁
    have e2 : polar Q (g (g u₀)) v₁ = polar Q u₀ v₁ := by
      conv_lhs => rw [← hgv₁, ← hgv₁]
      rw [polar_map_of_mem hg (g u₀) (g v₁)]
      rw [hgv₁]
      exact e1
    have h1 : polar Q (u₀ + g u₀ + g (g u₀)) v₁ = 3 * polar Q u₀ v₁ := by
      rw [polar_add_left, polar_add_left, e1, e2]
      ring
    rw [hu₀W, polar_zero_left] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left h3
  have hvsplit : v = v₁ + v₂ := by rw [hv₂]; abel
  rw [hvsplit, polar_add_right, hp₁, hp₂, add_zero]

theorem two_ne_zero_of_odd_card [Finite K] (hK : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  have := Fintype.ofFinite K
  refine two_ne_zero_of_card_odd ?_
  rw [← Nat.card_eq_fintype_card]
  exact Nat.odd_iff.mp hK

theorem goodPair_of_torsion (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : g ^ 3 = 1) {u : V}
    (hu : u + g u + g (g u) = 0) (hQu : Q u ≠ 0) : GoodPair Q g (u + g u) u := by
  have hg3' := apply_apply_apply_of_pow_three hg3
  have hgg : g (g u) = -(u + g u) := eq_neg_of_add_eq_zero_right hu
  have hd : polar Q u (g u) = -Q u := by
    have h1 : polar Q (g u) u = polar Q u (g (g u)) := by
      have := polar_map_of_mem hg u (g (g u))
      rwa [hg3' u] at this
    rw [polar_comm Q (g u) u, hgg, polar_neg_right, polar_add_right, polar_self_eq_two_mul] at h1
    apply mul_left_cancel₀ h2
    linear_combination h1
  have hQg : Q (g u) = Q u := map_of_mem hg u
  refine ⟨?_, ?_, hQu, Or.inr ⟨?_, ?_⟩⟩
  · rw [QuadraticMap.map_add Q, hQg, hd]
    ring
  · rw [polar_add_left, polar_comm Q (g u) u, hd, polar_self_eq_two_mul]
    ring
  · rw [map_add, hgg]
    abel
  · abel

theorem exists_goodPair [Finite K] (hK : Odd (Nat.card K)) (h3 : (3 : K) ≠ 0)
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 3 ≤ Module.finrank K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : g ^ 3 = 1) :
    ∃ x y, GoodPair Q g x y := by
  by_cases h1 : ∀ v, g v = v
  · exact exists_goodPair_of_fixed hK h3 hQ hdim h1
  · push Not at h1
    obtain ⟨w, hw⟩ := h1
    obtain ⟨u, hu, hQu⟩ := exists_nonsingular_of_moved h3 hQ hg hg3 hw
    exact ⟨_, _, goodPair_of_torsion (two_ne_zero_of_odd_card hK) hg hg3 hu hQu⟩

end OmSeven

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

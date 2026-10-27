module

public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap Module

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

omit [FiniteDimensional F V] in
theorem eichler_eq_eichler_iff_sub_mem (hQ : (polarBilin Q).Nondegenerate) {z b b' : V}
    (hz0 : z ≠ 0) (hz : Q z = 0) (hb : polar Q z b = 0) (hb' : polar Q z b' = 0) :
    eichler Q z b = eichler Q z b' ↔ b - b' ∈ F ∙ z := by
  constructor
  · intro he
    obtain ⟨v0, hv0⟩ := exists_polar_ne_zero hQ hz0
    have hv0' : polar Q v0 z ≠ 0 := by rwa [polar_comm]
    have hv : polar Q ((polar Q v0 z)⁻¹ • v0) z = 1 := by
      rw [polar_smul_left_eq, inv_mul_cancel₀ hv0']
    have hEq := LinearEquiv.congr_fun he ((polar Q v0 z)⁻¹ • v0)
    rw [eichler_apply hz hb, eichler_apply hz hb', hv] at hEq
    simp only [one_smul, mul_one] at hEq
    have hsub : b - b' =
        (polar Q ((polar Q v0 z)⁻¹ • v0) b + Q b) • z -
          (polar Q ((polar Q v0 z)⁻¹ • v0) b' + Q b') • z := by
      linear_combination (norm := module) hEq
    rw [← sub_smul] at hsub
    exact Submodule.mem_span_singleton.mpr ⟨_, hsub.symm⟩
  · rintro hc
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
    have hb_eq : b = b' + c • z := by
      linear_combination (norm := module) hc.symm
    rw [hb_eq, eichler_add_smul_self hz]

section CharTwo

variable [CharP F 2]

theorem reflect_not_mem_elementaryGroup (hQ : (polarBilin Q).Nondegenerate) {x : V}
    (hx : Q x ≠ 0) : reflect Q x ∉ elementaryGroup Q := by
  intro hE
  have homega := elementaryGroup_le_omegaGroup hQ hE
  rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup] at homega
  have h1 : finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace (reflect Q x)) = 1 := by
    let _ : Invertible (Q x) := invertibleOfNonzero hx
    rw [reflect_eq_reflection]
    exact CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ x
  have h2 := homega.2
  rw [h1] at h2
  exact Nat.not_even_one h2

omit [FiniteDimensional F V] [CharP F 2] in
private theorem Q_smul_pair {z x : V} (hz : Q z = 0) (hx : Q x = 1)
    (hzx : polar Q z x = 0) (a b : F) : Q (a • z + b • x) = b * b := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hz, hx, polar_smul_left_eq,
    polar_smul_right_eq, hzx]
  ring

omit [FiniteDimensional F V] [CharP F 2] in
private theorem Q_add_smul_pair {z x v : V} (hz : Q z = 0) (hx : Q x = 1)
    (hzx : polar Q z x = 0) (hvz : polar Q z v = 0) (a b : F) :
    Q (v + a • z + b • x) = Q v + b * polar Q v x + b * b := by
  have hvz' : polar Q v z = 0 := by rwa [polar_comm] at hvz
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hz, hx]
  simp only [polar_smul_left_eq, polar_smul_right_eq, polar_add_left, hzx, hvz', mul_zero,
    mul_one, add_zero]
  ring

omit [FiniteDimensional F V] [CharP F 2] in
private theorem linearIndependent_pair_singular {z x : V} (hz0 : z ≠ 0) (hz : Q z = 0)
    (hzx : polar Q z x = 0) (hx : Q x = 1) : LinearIndependent F ![z, x] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hQ0 : Q (a • z + b • x) = 0 := by rw [hab, QuadraticMap.map_zero]
  rw [Q_smul_pair (Q := Q) hz hx hzx a b] at hQ0
  have hb : b = 0 := mul_self_eq_zero.mp hQ0
  subst hb
  constructor
  · by_contra ha
    have hz0' : a • z = 0 := by simpa using hab
    rcases smul_eq_zero.mp hz0' with h | h
    · exact ha h
    · exact hz0 h
  · rfl

omit [FiniteDimensional F V] [CharP F 2] in
private theorem eichler_sub_mem_span_pair (u w y : V) :
    eichler Q u w y - y ∈ Submodule.span F {u, w} := by
  obtain ⟨a, b, hy⟩ := eichler_apply_eq_add (Q := Q) u w y
  rw [hy]
  have h : y + a • w + b • u - y = b • u + a • w := by abel
  rw [h]
  exact Submodule.mem_span_pair.mpr ⟨b, a, rfl⟩

theorem mem_rootGroup_or_reflect_mul_mem (hQ : (polarBilin Q).Nondegenerate) {z x : V}
    (hz0 : z ≠ 0) (hz : Q z = 0) (hzx : polar Q z x = 0) (hx : Q x = 1) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgz : g z = z)
    (hspan : ∀ v, polar Q z v = 0 → g v - v ∈ Submodule.span F {z, x}) :
    g ∈ rootGroup Q z ∨ reflect Q x * g ∈ rootGroup Q z := by
  obtain ⟨v, hv⟩ := exists_dual_family hQ (linearIndependent_pair_singular hz0 hz hzx hx)
  let u : V := v 1
  have huz : polar Q u z = 0 := by
    have h := hv 0 1
    rw [polar_comm]
    simpa [u] using h
  have hux : polar Q u x = 1 := by
    rw [polar_comm]
    simpa [u] using hv 1 1
  let beta : V → F := fun v => polar Q u (g v) - polar Q u v
  have hbeta_add : ∀ a b : V, beta (a + b) = beta a + beta b := by
    intro a b
    dsimp only [beta]
    rw [map_add g, polar_add_right, polar_add_right]
    ring
  have hcoord : ∀ (v : V) (hv : polar Q z v = 0) (a b : F),
      g v - v = a • z + b • x → beta v = b := by
    intro v hv a b hdec
    dsimp only [beta]
    rw [← polar_sub_right, hdec, polar_add_right]
    simp only [polar_smul_right_eq, huz, hux, mul_zero, mul_one, zero_add]
  have hquad : ∀ (v : V) (hv : polar Q z v = 0) (a b : F),
      g v - v = a • z + b • x → beta v * (beta v + polar Q v x) = 0 := by
    intro v hv a b hdec
    have hgv : g v = v + a • z + b • x := by
      linear_combination (norm := module) hdec
    have hexp := Q_add_smul_pair hz hx hzx hv a b
    have hQv : Q v = Q v + b * polar Q v x + b * b := by
      calc Q v = Q (g v) := (map_of_mem hg v).symm
        _ = Q (v + a • z + b • x) := by rw [hgv]
        _ = Q v + b * polar Q v x + b * b := hexp
    have hX : b * polar Q v x + b * b = 0 := by
      have h : Q v + (b * polar Q v x + b * b) = Q v + 0 := by
        rw [add_zero]
        calc Q v + (b * polar Q v x + b * b) = Q v + b * polar Q v x + b * b := by
              abel
          _ = Q v := hQv.symm
      exact add_left_cancel h
    have hb : beta v = b := hcoord v hv a b hdec
    rw [hb, mul_add, add_comm]
    exact hX
  by_cases hcase : ∀ v, polar Q z v = 0 → beta v = 0
  · left
    refine (mem_rootGroup_iff hQ hz hz0).mpr ⟨hg, hgz, ?_⟩
    intro v hv
    have hv' : polar Q z v = 0 := by rwa [polar_comm] at hv
    obtain ⟨a, b, hdec⟩ := Submodule.mem_span_pair.mp (hspan v hv')
    have hb : b = 0 := by
      rw [← hcoord v hv' a b hdec.symm]
      exact hcase v hv'
    exact ⟨a, by rw [hdec.symm, hb, zero_smul, add_zero]⟩
  · push Not at hcase
    obtain ⟨v₁, hv₁, hbeta₁⟩ := hcase
    right
    have hcase₂ : ∀ v, polar Q z v = 0 → beta v = polar Q v x := by
      by_contra hcon
      push Not at hcon
      obtain ⟨v₂, hv₂, hbeta₂⟩ := hcon
      obtain ⟨a₁, b₁, hdec₁⟩ := Submodule.mem_span_pair.mp (hspan v₁ hv₁)
      obtain ⟨a₂, b₂, hdec₂⟩ := Submodule.mem_span_pair.mp (hspan v₂ hv₂)
      have hfac₁ := hquad v₁ hv₁ a₁ b₁ hdec₁.symm
      have hfac₂ := hquad v₂ hv₂ a₂ b₂ hdec₂.symm
      have hb₁ : beta v₁ = polar Q v₁ x := by
        rcases mul_eq_zero.mp hfac₁ with h | h
        · exact absurd h hbeta₁
        · have h' : beta v₁ = -polar Q v₁ x := eq_neg_of_add_eq_zero_left h
          rwa [CharTwo.neg_eq] at h'
      have hB₁ : polar Q v₁ x ≠ 0 := by
        intro h0
        exact hbeta₁ (by rw [hb₁, h0])
      have hb₂ : beta v₂ = 0 := by
        rcases mul_eq_zero.mp hfac₂ with h | h
        · exact h
        · exfalso
          apply hbeta₂
          have h' : beta v₂ = -polar Q v₂ x := eq_neg_of_add_eq_zero_left h
          rwa [CharTwo.neg_eq] at h'
      have hB₂ : polar Q v₂ x ≠ 0 := by
        intro h0
        exact hbeta₂ (by rw [hb₂, h0])
      obtain ⟨a₁₂, b₁₂, hdec₁₂⟩ :=
        Submodule.mem_span_pair.mp (hspan (v₁ + v₂) (by rw [polar_add_right, hv₁, hv₂, add_zero]))
      have hb₁₂ : beta (v₁ + v₂) = polar Q v₁ x := by
        rw [hbeta_add, hb₁, hb₂, add_zero]
      have hfac₁₂ := hquad (v₁ + v₂) (by rw [polar_add_right, hv₁, hv₂, add_zero])
        a₁₂ b₁₂ hdec₁₂.symm
      have hb₁₂' : beta (v₁ + v₂) = polar Q (v₁ + v₂) x := by
        rcases mul_eq_zero.mp hfac₁₂ with h | h
        · rw [h] at hb₁₂
          exact absurd hb₁₂.symm hB₁
        · have h' : beta (v₁ + v₂) = -polar Q (v₁ + v₂) x := eq_neg_of_add_eq_zero_left h
          rwa [CharTwo.neg_eq] at h'
      have hzero : polar Q v₂ x = 0 := by
        rw [polar_add_left] at hb₁₂'
        have hEq : polar Q v₁ x + polar Q v₂ x = polar Q v₁ x + 0 := by
          rw [← hb₁₂', hb₁₂]
          simp
        exact add_left_cancel hEq
      exact hB₂ hzero
    have hx0 : Q x ≠ 0 := by rw [hx]; exact one_ne_zero
    have hzx' : polar Q x z = 0 := by rw [polar_comm, hzx]
    have hxx : polar Q x x = 0 := by
      rw [polar_self_eq_two_mul, hx, CharTwo.two_eq_zero, zero_mul]
    have hrO : reflect Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      reflect_mem_orthogonalGroup Q x
    have hrgO : reflect Q x * g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      mul_mem hrO hg
    have hrgz : (reflect Q x * g) z = z := by
      rw [LinearEquiv.mul_apply, hgz, reflect_apply hx0, hzx', zero_div, zero_smul, sub_zero]
    refine (mem_rootGroup_iff hQ hz hz0).mpr ⟨hrgO, hrgz, ?_⟩
    intro v hv
    have hv' : polar Q z v = 0 := by rwa [polar_comm] at hv
    obtain ⟨a, b, hdec⟩ := Submodule.mem_span_pair.mp (hspan v hv')
    have hb : b = polar Q v x := by
      rw [← hcoord v hv' a b hdec.symm]
      exact hcase₂ v hv'
    have hBxg : polar Q x (g v) = polar Q x v := by
      have hgv : g v = v + a • z + b • x := by linear_combination (norm := module) hdec.symm
      rw [hgv]
      simp only [QuadraticMap.polar_add_right, polar_smul_right_eq, hzx', hxx, mul_zero,
        add_zero]
    refine ⟨a, ?_⟩
    have hgv : g v = v + a • z + b • x := by linear_combination (norm := module) hdec.symm
    rw [LinearEquiv.mul_apply, reflect_apply hx0, hx, hBxg, hgv, hb, polar_comm]
    module

theorem mem_rootGroup_of_mem_elementaryGroup (hQ : (polarBilin Q).Nondegenerate) {z x : V}
    (hz0 : z ≠ 0) (hz : Q z = 0) (hzx : polar Q z x = 0) (hx : Q x = 1) {g : V ≃ₗ[F] V}
    (hgE : g ∈ elementaryGroup Q) (hgz : g z = z)
    (hspan : ∀ v, polar Q z v = 0 → g v - v ∈ Submodule.span F {z, x}) :
    g ∈ rootGroup Q z := by
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q hgE
  rcases mem_rootGroup_or_reflect_mul_mem hQ hz0 hz hzx hx hgO hgz hspan with h | h
  · exact h
  · exfalso
    have hrgE : reflect Q x * g ∈ elementaryGroup Q := rootGroup_le_elementaryGroup Q z h
    have hrE : reflect Q x ∈ elementaryGroup Q := by
      have := mul_mem hrgE (inv_mem hgE)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at this
    exact reflect_not_mem_elementaryGroup hQ (by rw [hx]; exact one_ne_zero) hrE

omit [CharP F 2] in
theorem fix_of_commute_eichler (hF : ∀ a : F, a = 0 ∨ a = 1) (hQ : (polarBilin Q).Nondegenerate)
    {z x : V} (hz0 : z ≠ 0) (hz : Q z = 0) (hzx : polar Q z x = 0) (hx : Q x = 1)
    {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : g * eichler Q z x = eichler Q z x * g) : g z = z ∧ g x - x ∈ F ∙ z := by
  obtain ⟨w, hw⟩ := exists_dual_family hQ (linearIndependent_pair_singular hz0 hz hzx hx)
  have hBz1 : polar Q z (w 1) = 0 := by simpa using hw 0 1
  have hBx1 : polar Q x (w 1) = 1 := by simpa using hw 1 1
  have hBz2 : polar Q z (w 0) = 1 := by simpa using hw 0 0
  have hBx2 : polar Q x (w 0) = 0 := by simpa using hw 1 0
  have hEv1 : eichler Q z x (w 1) = w 1 - z := by
    rw [eichler_apply hz hzx, show polar Q (w 1) z = 0 by rw [polar_comm, hBz1],
      show polar Q (w 1) x = 1 by rw [polar_comm, hBx1], hx]
    simp
  have hEv2 : eichler Q z x (w 0) = w 0 + x - z := by
    rw [eichler_apply hz hzx, show polar Q (w 0) z = 1 by rw [polar_comm, hBz2],
      show polar Q (w 0) x = 0 by rw [polar_comm, hBx2], hx]
    simp
  have hzform : z = w 1 - eichler Q z x (w 1) := by rw [hEv1]; abel
  have hxform : x - z = eichler Q z x (w 0) - w 0 := by rw [hEv2]; abel
  have hcomm1 : g (eichler Q z x (w 1)) = eichler Q z x (g (w 1)) := by
    simpa only [LinearEquiv.mul_apply] using LinearEquiv.congr_fun hc (w 1)
  have hcomm2 : g (eichler Q z x (w 0)) = eichler Q z x (g (w 0)) := by
    simpa only [LinearEquiv.mul_apply] using LinearEquiv.congr_fun hc (w 0)
  have hgzeq : g z = g (w 1) - eichler Q z x (g (w 1)) := by
    calc g z = g (w 1 - eichler Q z x (w 1)) := congrArg g hzform
      _ = g (w 1) - g (eichler Q z x (w 1)) := by rw [map_sub]
      _ = g (w 1) - eichler Q z x (g (w 1)) := by rw [hcomm1]
  have hgxzeq : g (x - z) = eichler Q z x (g (w 0)) - g (w 0) := by
    calc g (x - z) = g (eichler Q z x (w 0) - w 0) := congrArg g hxform
      _ = g (eichler Q z x (w 0)) - g (w 0) := by rw [map_sub]
      _ = eichler Q z x (g (w 0)) - g (w 0) := by rw [hcomm2]
  have hgz_mem : g z ∈ Submodule.span F {z, x} := by
    rw [hgzeq]
    have hmem := eichler_sub_mem_span_pair (Q := Q) z x (g (w 1))
    simpa only [neg_sub] using Submodule.neg_mem _ hmem
  have hgxz_mem : g (x - z) ∈ Submodule.span F {z, x} := by
    rw [hgxzeq]
    exact eichler_sub_mem_span_pair (Q := Q) z x (g (w 0))
  have hgx_mem : g x ∈ Submodule.span F {z, x} := by
    have hadd : g (x - z) + g z = g x := by
      rw [← map_add]
      congr 1
      abel
    rw [← hadd]
    exact Submodule.add_mem _ hgxz_mem hgz_mem
  obtain ⟨a, b, hgzab⟩ := Submodule.mem_span_pair.mp hgz_mem
  have hgzQ : Q (g z) = 0 := by rw [map_of_mem hg, hz]
  have hbb : b * b = 0 := by
    have hexp := Q_smul_pair (Q := Q) hz hx hzx a b
    rw [hgzab, hgzQ] at hexp
    exact hexp.symm
  have hb : b = 0 := mul_self_eq_zero.mp hbb
  have hgza : g z = a • z := by rw [← hgzab, hb, zero_smul, add_zero]
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, zero_smul] at hgza
    exact hz0 (g.injective (by rw [hgza, map_zero]))
  have ha1 : a = 1 := by
    rcases hF a with h0 | h1
    · exact absurd h0 ha0
    · exact h1
  have hgz : g z = z := by rw [hgza, ha1, one_smul]
  obtain ⟨a', b', hgxab⟩ := Submodule.mem_span_pair.mp hgx_mem
  have hgxQ : Q (g x) = 1 := by rw [map_of_mem hg, hx]
  have hb'b' : b' * b' = 1 := by
    have hexp := Q_smul_pair (Q := Q) hz hx hzx a' b'
    rw [hgxab, hgxQ] at hexp
    exact hexp.symm
  have hb'0 : b' ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hb'b'
    exact zero_ne_one hb'b'
  have hb'1 : b' = 1 := by
    rcases hF b' with h0 | h1
    · exact absurd h0 hb'0
    · exact h1
  refine ⟨hgz, ?_⟩
  have hdiff : g x - x = a' • z := by
    rw [← hgxab, hb'1, one_smul]
    abel
  exact Submodule.mem_span_singleton.mpr ⟨a', hdiff.symm⟩

end CharTwo

end CFSG.ClassicalGroups.Orthogonal

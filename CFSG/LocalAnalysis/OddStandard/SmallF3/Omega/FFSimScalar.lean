module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ff_zmod3_eq_one_or_two {a : ZMod 3} (ha : a ≠ 0) : a = 1 ∨ a = 2 := by
  fin_cases a
  · exact absurd rfl ha
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem ff_zmod3_two_nonzero (a c e : ZMod 3) (ha : a ≠ 0) (hc : c ≠ 0) (he : e ≠ 0)
    (hac : a ≠ c) : e = a ∨ e = c := by
  rcases ff_zmod3_eq_one_or_two ha with rfl | rfl <;>
    rcases ff_zmod3_eq_one_or_two hc with rfl | rfl <;>
      rcases ff_zmod3_eq_one_or_two he with rfl | rfl <;>
        first
          | exact absurd rfl hac
          | exact Or.inl rfl
          | exact Or.inr rfl

theorem ff_eigen_star {γ : V ≃ₗ[ZMod 3] V}
    (hγ : ∀ u : V, Q u ≠ 0 → ∃ c : ZMod 3, γ u = c • u) {x y : V} (hx : Q x ≠ 0) (hy : Q y ≠ 0)
    {a b : ZMod 3} (hxa : γ x = a • x) (hyb : γ y = b • y) (hab : a ≠ b) :
    polar Q x y = 0 ∧ Q y = - Q x := by
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, QuadraticMap.map_zero])
  have hy0 : y ≠ 0 := fun h => hy (by rw [h, QuadraticMap.map_zero])
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hlin : ∀ s t : ZMod 3, s • x + t • y = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    have h1' : (s * a) • x + (t * b) • y = 0 := by
      have h1 : γ (s • x + t • y) = 0 := by rw [hst, map_zero]
      rw [map_add, map_smul, map_smul, hxa, hyb] at h1
      rw [smul_smul, smul_smul] at h1
      exact h1
    have h2' : (s * a) • x + (t * a) • y = 0 := by
      have h2 : a • (s • x + t • y) = 0 := by rw [hst, smul_zero]
      rw [smul_add, smul_smul, smul_smul] at h2
      rw [mul_comm a s, mul_comm a t] at h2
      exact h2
    have htb : (t * b) • y = (t * a) • y := by
      have e1 : (t * b) • y = -((s * a) • x) := by
        rw [eq_neg_iff_add_eq_zero]
        rwa [add_comm]
      have e2 : (t * a) • y = -((s * a) • x) := by
        rw [eq_neg_iff_add_eq_zero]
        rwa [add_comm]
      rw [e1, e2]
    have hsub : (t * (b - a)) • y = 0 := by
      have hcoeff : t * (b - a) = t * b - t * a := by ring
      rw [hcoeff, sub_smul, htb, sub_self]
    have ht : t = 0 := by
      have hz : t * (b - a) = 0 := (smul_eq_zero.mp hsub).resolve_right hy0
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd h hba
    have hs : s = 0 := by
      have hsz : s • x = 0 := by
        rw [ht, zero_smul, add_zero] at hst
        exact hst
      exact (smul_eq_zero.mp hsz).resolve_right hx0
    exact ⟨hs, ht⟩
  have hQxy : Q (x + y) = 0 := by
    by_contra hne
    obtain ⟨c, hc⟩ := hγ (x + y) hne
    have hsum : a • x + b • y = c • x + c • y := by
      have h : γ (x + y) = a • x + b • y := by rw [map_add, hxa, hyb]
      rw [smul_add] at hc
      exact h.symm.trans hc
    have hzero : (a - c) • x + (b - c) • y = 0 := by
      rw [sub_smul, sub_smul]
      rw [show (a • x - c • x) + (b • y - c • y) = (a • x + b • y) - (c • x + c • y) by
        abel, hsum, sub_self]
    obtain ⟨h1, h2⟩ := hlin (a - c) (b - c) hzero
    exact hab ((sub_eq_zero.mp h1).trans (sub_eq_zero.mp h2).symm)
  have hQxmy : Q (x - y) = 0 := by
    by_contra hne
    obtain ⟨c, hc⟩ := hγ (x - y) hne
    have hsum : a • x - b • y = c • x - c • y := by
      have h : γ (x - y) = a • x - b • y := by rw [map_sub, hxa, hyb]
      rw [smul_sub] at hc
      exact h.symm.trans hc
    have hzero : (a - c) • x + (c - b) • y = 0 := by
      rw [sub_smul, sub_smul]
      rw [show (a • x - c • x) + (c • y - b • y) = (a • x - b • y) - (c • x - c • y) by
        abel, hsum, sub_self]
    obtain ⟨h1, h2⟩ := hlin (a - c) (c - b) hzero
    exact hab ((sub_eq_zero.mp h1).trans (sub_eq_zero.mp h2))
  have hplus : Q x + Q y + polar Q x y = 0 := by
    have h := QuadraticMap.map_add Q x y
    rw [hQxy] at h
    exact h.symm
  have hminus : Q x + Q y - polar Q x y = 0 := by
    have h := QuadraticMap.map_add Q x (-y)
    rw [show x + -y = x - y by abel, hQxmy, QuadraticMap.map_neg, polar_neg_right] at h
    rw [sub_eq_add_neg]
    exact h.symm
  have h2ne : (2 : ZMod 3) ≠ 0 := by decide
  have hpolar : polar Q x y = 0 := by
    have h : (Q x + Q y + polar Q x y) - (Q x + Q y - polar Q x y) = 0 := by
      rw [hplus, hminus, sub_zero]
    have h2p : (2 : ZMod 3) * polar Q x y = 0 := by
      rw [show (Q x + Q y + polar Q x y) - (Q x + Q y - polar Q x y)
          = 2 * polar Q x y by ring] at h
      exact h
    rcases mul_eq_zero.mp h2p with h' | h'
    · exact absurd h' h2ne
    · exact h'
  have hsum : (2 : ZMod 3) * (Q x + Q y) = 0 := by
    have h : (Q x + Q y + polar Q x y) + (Q x + Q y - polar Q x y) = 0 := by
      rw [hplus, hminus, add_zero]
    rw [show (Q x + Q y + polar Q x y) + (Q x + Q y - polar Q x y)
        = 2 * (Q x + Q y) by ring] at h
    exact h
  refine ⟨hpolar, ?_⟩
  rcases mul_eq_zero.mp hsum with h' | h'
  · exact absurd h' h2ne
  · rw [eq_neg_iff_add_eq_zero]
    rwa [add_comm]

theorem ff_eigen_const (hQ : Q.Nondegenerate) (h4 : 4 ≤ Module.finrank (ZMod 3) V)
    (γ : V ≃ₗ[ZMod 3] V) (hγ : ∀ u : V, Q u ≠ 0 → ∃ c : ZMod 3, γ u = c • u) :
    ∃ c : ZMod 3, ∀ u : V, Q u ≠ 0 → γ u = c • u := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 3) (by omega)
  obtain ⟨u0, hu0u⟩ := hQ.exists_isUnit
  have hu0 : Q u0 ≠ 0 := hu0u.ne_zero
  obtain ⟨c, hc⟩ := hγ u0 hu0
  refine ⟨c, fun x hx => ?_⟩
  by_contra hxc
  obtain ⟨a, ha⟩ := hγ x hx
  have hac : a ≠ c := fun h => hxc (by rw [ha, h])
  have ha0 : a ≠ 0 := by
    intro h
    have : γ x = γ 0 := by rw [ha, h, zero_smul, map_zero]
    exact hx (by rw [γ.injective this, QuadraticMap.map_zero])
  have hc0 : c ≠ 0 := by
    intro h
    have : γ u0 = γ 0 := by rw [hc, h, zero_smul, map_zero]
    exact hu0 (by rw [γ.injective this, QuadraticMap.map_zero])
  have hstar := ff_eigen_star hγ hu0 hx hc ha (Ne.symm hac)
  obtain ⟨z, hzu0, hzx, hz⟩ := ff_exists_orth_pair_nonsingular hQ h4 hu0 hx hstar.1
  set w : V := u0 + x + z with hwdef
  have hQu0x : Q (u0 + x) = Q u0 + Q x := by
    rw [QuadraticMap.map_add Q u0 x, hstar.1, add_zero]
  have hp_u0x_z : polar Q (u0 + x) z = 0 := by
    rw [polar_add_left, hzu0, hzx, add_zero]
  have hQw : Q w = Q z := by
    rw [hwdef, QuadraticMap.map_add Q (u0 + x) z, hQu0x, hp_u0x_z, hstar.2, add_neg_cancel]
    simp
  have hw : Q w ≠ 0 := by rw [hQw]; exact hz
  have hp_u0w : polar Q u0 w = 2 • Q u0 := by
    rw [hwdef, polar_add_right, polar_add_right, QuadraticMap.polar_self, hstar.1, hzu0]
    simp
  have hp_xw : polar Q x w = 2 • Q x := by
    rw [hwdef, polar_add_right, polar_add_right, polar_comm Q x u0, hstar.1, hzx]
    simp
  have h2ne : (2 : ZMod 3) ≠ 0 := by decide
  have hpu0w : polar Q u0 w ≠ 0 := by
    rw [hp_u0w, nsmul_eq_mul]
    exact mul_ne_zero h2ne hu0
  have hpxw : polar Q x w ≠ 0 := by
    rw [hp_xw, nsmul_eq_mul]
    exact mul_ne_zero h2ne hx
  obtain ⟨e, he⟩ := hγ w hw
  have he0 : e ≠ 0 := by
    intro h
    have : γ w = γ 0 := by rw [he, h, zero_smul, map_zero]
    exact hw (by rw [γ.injective this, QuadraticMap.map_zero])
  rcases ff_zmod3_two_nonzero a c e ha0 hc0 he0 hac with hea | hec
  · have hne : e ≠ c := by rw [hea]; exact hac
    have hcon := (ff_eigen_star hγ hw hu0 he hc hne).1
    exact hpu0w (by rwa [polar_comm] at hcon)
  · have hne : e ≠ a := by rw [hec]; exact Ne.symm hac
    have hcon := (ff_eigen_star hγ hw hx he ha hne).1
    exact hpxw (by rwa [polar_comm] at hcon)

end CFSG.OddStandard.SmallF3.Omega

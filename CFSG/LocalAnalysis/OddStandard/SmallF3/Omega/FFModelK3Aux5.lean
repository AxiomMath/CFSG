module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_k3_polar_self (x : V) : polar Q x x = 2 * Q x := by
  rw [QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat]

theorem ff_k3_refl_sum_diff {a b : V} (ha : Q a ≠ 0) (hb : Q a = Q b) (hab : polar Q a b = 0) :
    reflTot Q (a + b) * reflTot Q (a - b) = reflTot Q a * reflTot Q b := by
  have hbne : Q b ≠ 0 := hb ▸ ha
  have h2ne : (2 : ZMod 3) * Q a ≠ 0 := mul_ne_zero (by decide) ha
  have hQab : Q (a + b) = 2 * Q a := by
    rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, hab, add_zero, ← hb]; ring
  have h1 : ((reflTot Q a : OGroup Q) : V ≃ₗ[ZMod 3] V) (a + b) = -(a - b) := by
    rw [coe_reflTot_apply, QuadraticMap.polar_add_right, hab, add_zero, ff_k3_polar_self,
      mul_div_cancel_right₀ _ ha]
    module
  have hpol : polar Q (a + b) a = 2 * Q a := by
    rw [QuadraticMap.polar_add_left, ff_k3_polar_self, QuadraticMap.polar_comm Q b a, hab,
      add_zero]
  have h2 : ((reflTot Q (a + b) : OGroup Q) : V ≃ₗ[ZMod 3] V) a = -b := by
    rw [coe_reflTot_apply, hpol, hQab, div_self h2ne, one_smul]
    abel
  have e1 : reflTot Q (a - b) = reflTot Q a * reflTot Q (a + b) * reflTot Q a := by
    have h := reflTot_conj (reflTot Q a) (a + b)
    rw [reflTot_inv, h1, reflTot_neg] at h
    exact h.symm
  have e2 : reflTot Q b = reflTot Q (a + b) * reflTot Q a * reflTot Q (a + b) := by
    have h := reflTot_conj (reflTot Q (a + b)) a
    rw [reflTot_inv, h2, reflTot_neg] at h
    exact h.symm
  calc reflTot Q (a + b) * reflTot Q (a - b)
      = (reflTot Q (a + b) * reflTot Q a * reflTot Q (a + b)) * reflTot Q a := by
        rw [e1]; group
    _ = reflTot Q b * reflTot Q a := by rw [← e2]
    _ = reflTot Q a * reflTot Q b := (reflTot_comm ha hbne hab).symm

theorem ff_k3_refl_diff_sum {a b : V} (ha : Q a ≠ 0) (hb : Q a = Q b) (hab : polar Q a b = 0) :
    reflTot Q (a - b) * reflTot Q (a + b) = reflTot Q a * reflTot Q b := by
  have hbne : Q b ≠ 0 := hb ▸ ha
  have h := congrArg (fun g => g⁻¹) (ff_k3_refl_sum_diff ha hb hab)
  simp only [mul_inv_rev, reflTot_inv] at h
  rw [h]
  exact (reflTot_comm ha hbne hab).symm

theorem ff_k3_comm_aux {G : Type*} [Group G] {A B C D : G} (hCD : Commute C D)
    (hBD : Commute B D) : A * B * (C * D) = A * D * (B * C) := by
  calc A * B * (C * D) = A * (B * (C * D)) := by group
    _ = A * (B * (D * C)) := by rw [hCD.eq]
    _ = A * ((B * D) * C) := by group
    _ = A * ((D * B) * C) := by rw [hBD.eq]
    _ = A * D * (B * C) := by group

theorem ff_k3_commutator {t : OGroup Q} {u v s s' : V} {c : ZMod 3} (hc : c ≠ 0)
    (hu : Q u = c) (hv : Q v = c) (hs : Q s = c) (hs' : Q s' = c)
    (huv : polar Q u v = 0) (hus : polar Q u s = 0) (hus' : polar Q u s' = 0)
    (hvs : polar Q v s = 0) (hvs' : polar Q v s' = 0) (hss' : polar Q s s' = 0)
    (htu : (t : V ≃ₗ[ZMod 3] V) u = u) (htv : (t : V ≃ₗ[ZMod 3] V) v = v)
    (hts : (t : V ≃ₗ[ZMod 3] V) s = -s) (hts' : (t : V ≃ₗ[ZMod 3] V) s' = -s') :
    t * (reflTot Q (u + s) * reflTot Q (v + s')) * t⁻¹ *
        (reflTot Q (u + s) * reflTot Q (v + s'))⁻¹ =
      reflTot Q u * reflTot Q v * (reflTot Q s * reflTot Q s') := by
  have h2c : (2 : ZMod 3) * c ≠ 0 := mul_ne_zero (by decide) hc
  have hune : Q u ≠ 0 := by rw [hu]; exact hc
  have hvne : Q v ≠ 0 := by rw [hv]; exact hc
  have hsne : Q s ≠ 0 := by rw [hs]; exact hc
  have hs'ne : Q s' ≠ 0 := by rw [hs']; exact hc
  have hsu : polar Q s u = 0 := (QuadraticMap.polar_comm Q s u).trans hus
  have hsv : polar Q s v = 0 := (QuadraticMap.polar_comm Q s v).trans hvs
  have hs'u : polar Q s' u = 0 := (QuadraticMap.polar_comm Q s' u).trans hus'
  have hvu : polar Q v u = 0 := (QuadraticMap.polar_comm Q v u).trans huv
  have hs's : polar Q s' s = 0 := (QuadraticMap.polar_comm Q s' s).trans hss'
  have hPne : Q (u + s) ≠ 0 := by
    rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, hu, hs, hus]
    rw [show c + c + 0 = 2 * c by ring]; exact h2c
  have hP'ne : Q (v + s') ≠ 0 := by
    rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, hv, hs', hvs']
    rw [show c + c + 0 = 2 * c by ring]; exact h2c
  have hT'ne : Q (v - s') ≠ 0 := by
    rw [ff_map_sub, hv, hs', hvs']
    rw [show c + c - 0 = 2 * c by ring]; exact h2c
  have hP'P : polar Q (v + s') (u + s) = 0 := by
    rw [ff_polar_add_add, hvu, hvs, hs'u, hs's]; ring
  have hT'P : polar Q (v - s') (u + s) = 0 := by
    rw [ff_polar_sub_add, hvu, hvs, hs'u, hs's]; ring
  have hTP : (t : V ≃ₗ[ZMod 3] V) (u + s) = u - s := by
    rw [map_add, htu, hts, sub_eq_add_neg]
  have hTP' : (t : V ≃ₗ[ZMod 3] V) (v + s') = v - s' := by
    rw [map_add, htv, hts', sub_eq_add_neg]
  have hmul : ∀ A B : OGroup Q, t * (A * B) * t⁻¹ = (t * A * t⁻¹) * (t * B * t⁻¹) := by
    intro A B; group
  rw [hmul, reflTot_conj, reflTot_conj, hTP, hTP', mul_inv_rev, reflTot_inv, reflTot_inv,
    ff_k3_comm_aux (reflTot_comm hP'ne hPne hP'P) (reflTot_comm hT'ne hPne hT'P),
    ff_k3_refl_diff_sum hune (hu.trans hs.symm) hus,
    ff_k3_refl_diff_sum hvne (hv.trans hs'.symm) hvs']
  calc reflTot Q u * reflTot Q s * (reflTot Q v * reflTot Q s')
      = reflTot Q u * (reflTot Q s * reflTot Q v) * reflTot Q s' := by group
    _ = reflTot Q u * (reflTot Q v * reflTot Q s) * reflTot Q s' := by
        rw [reflTot_comm hsne hvne hsv]
    _ = reflTot Q u * reflTot Q v * (reflTot Q s * reflTot Q s') := by group

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalSkewExp

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {g : V ≃ₗ[K] V} {e d : V}

structure HeisData (Q : QuadraticForm K V) (g : V ≃ₗ[K] V) (e d : V) : Prop where
  mem : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  pow_three : g ^ 3 = 1
  sum_e : e + g e + (g ^ 2) e = 0
  orth_ee : ∀ i j : Fin 3, polar Q ((g ^ (i : ℕ)) e) ((g ^ (j : ℕ)) e) = 0
  orth_ed : ∀ i j : Fin 3, polar Q ((g ^ (i : ℕ)) e) ((g ^ (j : ℕ)) d) = 0
  orth_dd : ∀ i j : Fin 3,
    polar Q ((g ^ (i : ℕ)) d) ((g ^ (j : ℕ)) d) = (if i = j then 2 else -1) * Q d
  ne_d : Q d ≠ 0
  indep : ∀ a b : K, a • e + b • g e = 0 → a = 0 ∧ b = 0
  nondeg : (polarBilin Q).Nondegenerate

@[expose] noncomputable def heisPsi (Q : QuadraticForm K V) (g : V ≃ₗ[K] V) (e d : V) :
    V →ₗ[K] V :=
  ∑ j : Fin 3, skewPair Q ((g ^ (j : ℕ)) e) ((g ^ (j : ℕ)) d)

theorem heisPsi_apply (x : V) :
    heisPsi Q g e d x = ∑ j : Fin 3, (polar Q x ((g ^ (j : ℕ)) e) • (g ^ (j : ℕ)) d -
      polar Q x ((g ^ (j : ℕ)) d) • (g ^ (j : ℕ)) e) := by
  simp [heisPsi, skewPair_apply]

theorem polar_heisPsi_left (x y : V) :
    polar Q (heisPsi Q g e d x) y = - polar Q x (heisPsi Q g e d y) := by
  simp only [heisPsi, Fin.sum_univ_three, LinearMap.add_apply, map_add, polar_add_left,
    polar_add_right, polar_skewPair_left, smul_add]
  abel

theorem heisPsi_map_apply (h : HeisData Q g e d) (x : V) :
    heisPsi Q g e d (g x) = g (heisPsi Q g e d x) := by
  have hge : g ((g ^ 2) e) = e := by
    rw [← LinearEquiv.mul_apply, ← pow_succ', h.pow_three]
    rfl
  have hgd : g ((g ^ 2) d) = d := by
    rw [← LinearEquiv.mul_apply, ← pow_succ', h.pow_three]
    rfl
  have h1 : skewPair Q e d (g x) = g (skewPair Q ((g ^ 2) e) ((g ^ 2) d) x) := by
    conv_lhs => rw [← hge, ← hgd]
    rw [skewPair_map_apply h.mem]
  have h2 : skewPair Q (g e) (g d) (g x) = g (skewPair Q e d x) :=
    skewPair_map_apply h.mem e d x
  have h3 : skewPair Q ((g ^ 2) e) ((g ^ 2) d) (g x) =
      g (skewPair Q (g e) (g d) x) := by
    have h2e : (g ^ 2) e = g (g e) := by
      rw [pow_two, LinearEquiv.mul_apply]
    have h2d : (g ^ 2) d = g (g d) := by
      rw [pow_two, LinearEquiv.mul_apply]
    rw [h2e, h2d, skewPair_map_apply h.mem]
  simp only [heisPsi, Fin.sum_univ_three, LinearMap.add_apply, Fin.val_zero, Fin.val_one,
    Fin.val_two, pow_zero, pow_one, LinearEquiv.coe_one, id_eq]
  rw [h1, h2, h3, map_add, map_add]
  abel

theorem heisPsi_orbit_e (h : HeisData Q g e d) (i : Fin 3) :
    heisPsi Q g e d ((g ^ (i : ℕ)) e) = 0 := by
  rw [heisPsi_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [h.orth_ee i j, h.orth_ed i j]
  simp

private theorem heisPsi_orbit_d_zero (h : HeisData Q g e d) :
    heisPsi Q g e d d = (-(3 * Q d)) • e := by
    have hs : (Q d) • (e + g e + (g ^ 2) e) = 0 := by rw [h.sum_e, smul_zero]
    rw [heisPsi_apply]
    simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      LinearEquiv.coe_one, id_eq]
    rw [show polar Q d e = 0 by rw [polar_comm]; exact h.orth_ed 0 0,
      show polar Q d (g e) = 0 by rw [polar_comm]; simpa using h.orth_ed 1 0,
      show polar Q d ((g ^ 2) e) = 0 by rw [polar_comm]; simpa using h.orth_ed 2 0]
    have hdd0 : polar Q d d = (2 : K) * Q d := by simpa using h.orth_dd 0 0
    have hdd1 : polar Q d (g d) = (-1 : K) * Q d := by
      have h' := h.orth_dd 0 1
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, LinearEquiv.coe_one, id_eq] at h'
      rw [if_neg (show (0 : Fin 3) ≠ 1 by decide)] at h'
      simpa using h'
    have hdd2 : polar Q d ((g ^ 2) d) = (-1 : K) * Q d := by
      have h' := h.orth_dd 0 2
      simp only [Fin.val_zero, Fin.val_two, pow_zero, LinearEquiv.coe_one, id_eq] at h'
      rw [if_neg (show (0 : Fin 3) ≠ 2 by decide)] at h'
      simpa using h'
    rw [hdd0, hdd1, hdd2]
    simp only [zero_smul, zero_sub, sub_zero]
    linear_combination (norm := module) hs

private theorem heisPsi_orbit_d_one (h : HeisData Q g e d) :
    heisPsi Q g e d (g d) = (-(3 * Q d)) • g e := by
    have hs : (Q d) • (e + g e + (g ^ 2) e) = 0 := by rw [h.sum_e, smul_zero]
    rw [heisPsi_apply]
    simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      LinearEquiv.coe_one, id_eq]
    rw [show polar Q (g d) e = 0 by rw [polar_comm]; exact h.orth_ed 0 1,
      show polar Q (g d) (g e) = 0 by rw [polar_comm]; simpa using h.orth_ed 1 1,
      show polar Q (g d) ((g ^ 2) e) = 0 by rw [polar_comm]; simpa using h.orth_ed 2 1]
    have hdd0 : polar Q (g d) d = (-1 : K) * Q d := by
      rw [polar_comm]
      have h' := h.orth_dd 0 1
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, LinearEquiv.coe_one, id_eq] at h'
      rw [if_neg (show (0 : Fin 3) ≠ 1 by decide)] at h'
      simpa using h'
    have hdd1 : polar Q (g d) (g d) = (2 : K) * Q d := by
      have h' := h.orth_dd 1 1
      simp only [Fin.val_one, pow_one] at h'
      rw [if_true] at h'
      simpa using h'
    have hdd2 : polar Q (g d) ((g ^ 2) d) = (-1 : K) * Q d := by
      have h' := h.orth_dd 1 2
      simp only [Fin.val_one, Fin.val_two, pow_one] at h'
      rw [if_neg (show (1 : Fin 3) ≠ 2 by decide)] at h'
      simpa using h'
    rw [hdd0, hdd1, hdd2]
    simp only [zero_smul, zero_sub, sub_zero]
    linear_combination (norm := module) hs

private theorem heisPsi_orbit_d_two (h : HeisData Q g e d) :
    heisPsi Q g e d ((g ^ 2) d) = (-(3 * Q d)) • (g ^ 2) e := by
    have hs : (Q d) • (e + g e + (g ^ 2) e) = 0 := by rw [h.sum_e, smul_zero]
    rw [heisPsi_apply]
    simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      LinearEquiv.coe_one, id_eq]
    rw [show polar Q ((g ^ 2) d) e = 0 by rw [polar_comm]; exact h.orth_ed 0 2,
      show polar Q ((g ^ 2) d) (g e) = 0 by rw [polar_comm]; simpa using h.orth_ed 1 2,
      show polar Q ((g ^ 2) d) ((g ^ 2) e) = 0 by rw [polar_comm]; simpa using h.orth_ed 2 2]
    have hdd0 : polar Q ((g ^ 2) d) d = (-1 : K) * Q d := by
      rw [polar_comm]
      have h' := h.orth_dd 0 2
      simp only [Fin.val_zero, Fin.val_two, pow_zero, LinearEquiv.coe_one, id_eq] at h'
      rw [if_neg (show (0 : Fin 3) ≠ 2 by decide)] at h'
      simpa using h'
    have hdd1 : polar Q ((g ^ 2) d) (g d) = (-1 : K) * Q d := by
      rw [polar_comm]
      have h' := h.orth_dd 1 2
      simp only [Fin.val_one, Fin.val_two, pow_one] at h'
      rw [if_neg (show (1 : Fin 3) ≠ 2 by decide)] at h'
      simpa using h'
    have hdd2 : polar Q ((g ^ 2) d) ((g ^ 2) d) = (2 : K) * Q d := by
      have h' := h.orth_dd 2 2
      simp only [Fin.val_two] at h'
      rw [if_true] at h'
      simpa using h'
    rw [hdd0, hdd1, hdd2]
    simp only [zero_smul, zero_sub, sub_zero]
    linear_combination (norm := module) hs

theorem heisPsi_orbit_d (h : HeisData Q g e d) (i : Fin 3) :
    heisPsi Q g e d ((g ^ (i : ℕ)) d) = (-(3 * Q d)) • (g ^ (i : ℕ)) e := by
  fin_cases i
  · simpa only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      LinearEquiv.coe_one, id_eq] using heisPsi_orbit_d_zero h
  · simpa only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      LinearEquiv.coe_one, id_eq] using heisPsi_orbit_d_one h
  · simpa only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      LinearEquiv.coe_one, id_eq] using heisPsi_orbit_d_two h

theorem heisPsi_sq (h : HeisData Q g e d) (x : V) :
    heisPsi Q g e d (heisPsi Q g e d x) =
      (-(3 * Q d)) • ∑ j : Fin 3, polar Q x ((g ^ (j : ℕ)) e) • (g ^ (j : ℕ)) e := by
  rw [heisPsi_apply x, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sub, map_smul, map_smul, heisPsi_orbit_d h j, heisPsi_orbit_e h j]
  simp only [smul_zero, sub_zero]
  exact smul_comm _ _ _

theorem heisPsi_cube (h : HeisData Q g e d) (x : V) :
    heisPsi Q g e d (heisPsi Q g e d (heisPsi Q g e d x)) = 0 := by
  rw [heisPsi_sq h x, map_smul, map_sum]
  have hz : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      heisPsi Q g e d (polar Q x ((g ^ (j : ℕ)) e) • (g ^ (j : ℕ)) e) = 0 := by
    intro j _
    rw [map_smul, heisPsi_orbit_e h j, smul_zero]
  rw [Finset.sum_eq_zero hz, smul_zero]

theorem exists_heisPsi_sq_ne_zero (h : HeisData Q g e d) (h3 : (3 : K) ≠ 0) :
    ∃ x, heisPsi Q g e d (heisPsi Q g e d x) ≠ 0 := by
  have hx : (2 : K) • e + g e ≠ 0 := by
    intro h0
    exact one_ne_zero (h.indep 2 1 (by simpa using h0)).2
  obtain ⟨x, hxβ⟩ := exists_polar_ne_zero h.nondeg hx
  refine ⟨x, fun hzero => ?_⟩
  have hβ : polar Q x ((2 : K) • e + g e) ≠ 0 := by
    rwa [polar_comm]
  have hg2 : (g ^ 2) e = -e - g e := by
    have h' := eq_neg_of_add_eq_zero_right h.sum_e
    simpa [sub_eq_add_neg, add_comm] using h'
  have hc : (-(3 * Q d)) ≠ 0 := by
    rw [neg_ne_zero]
    exact mul_ne_zero h3 h.ne_d
  have hsum0 : ∑ j : Fin 3, polar Q x ((g ^ (j : ℕ)) e) • (g ^ (j : ℕ)) e = 0 := by
    have h' := hzero
    rw [heisPsi_sq h x] at h'
    exact (smul_eq_zero.1 h').resolve_left hc
  rw [Fin.sum_univ_three] at hsum0
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, LinearEquiv.coe_one,
    id_eq] at hsum0
  have hβ2 : polar Q x ((g ^ 2) e) = -polar Q x e - polar Q x (g e) := by
    rw [hg2, polar_sub_right, polar_neg_right]
  have hsum0' : (polar Q x e - polar Q x ((g ^ 2) e)) • e +
      (polar Q x (g e) - polar Q x ((g ^ 2) e)) • g e = 0 := by
    rw [hg2] at hsum0
    rw [polar_sub_right, polar_neg_right] at hsum0
    rw [hg2, polar_sub_right, polar_neg_right]
    linear_combination (norm := module) hsum0
  have hcoef : (polar Q x e - polar Q x ((g ^ 2) e)) = 0 := by
    have hind := h.indep (polar Q x e - polar Q x ((g ^ 2) e))
      (polar Q x (g e) - polar Q x ((g ^ 2) e)) hsum0'
    exact hind.1
  have hβeq : polar Q x ((2 : K) • e + g e) =
      polar Q x e - polar Q x ((g ^ 2) e) := by
    rw [hβ2, polar_add_right, polar_smul_right, smul_eq_mul]
    ring
  exact hβ (by rw [hβeq]; exact hcoef)

theorem skewPair_sq_eq_zero (h : HeisData Q g e d) (x : V) :
    skewPair Q e (g e) (skewPair Q e (g e) x) = 0 := by
  have h00 : polar Q e e = 0 := by simpa using h.orth_ee 0 0
  have h10 : polar Q (g e) e = 0 := by simpa using h.orth_ee 1 0
  have h11 : polar Q (g e) (g e) = 0 := by simpa using h.orth_ee 1 1
  have h01 : polar Q e (g e) = 0 := by simpa using h.orth_ee 0 1
  simp only [skewPair_apply, polar_sub_left, polar_smul_left, h10, h00, h11, h01, smul_zero,
    sub_zero]
  simp

theorem skewPair_map_g (h : HeisData Q g e d) (x : V) :
    skewPair Q e (g e) (g x) = g (skewPair Q e (g e) x) := by
  have hg2 : (g ^ 2) e = -e - g e := by
    have h' := eq_neg_of_add_eq_zero_right h.sum_e
    simpa [sub_eq_add_neg, add_comm] using h'
  have h2e : g (g e) = (g ^ 2) e := by
    rw [pow_two, LinearEquiv.mul_apply]
  have hsk : skewPair Q e (g e) (g x) = skewPair Q (g e) (-e - g e) (g x) := by
    simp only [skewPair_apply, polar_sub_right, polar_neg_right]
    module
  rw [hsk, ← hg2, ← h2e, skewPair_map_apply h.mem]

theorem skewPair_ne_zero (h : HeisData Q g e d) : skewPair Q e (g e) ≠ 0 := by
  have he : e ≠ 0 := by
    intro h0
    exact one_ne_zero (h.indep 1 0 (by simpa using h0)).1
  obtain ⟨x, hx⟩ := exists_polar_ne_zero h.nondeg he
  intro hψ
  have hψx : polar Q x e • g e - polar Q x (g e) • e = 0 := by
    have h' := congrArg (fun f : V →ₗ[K] V => f x) hψ
    simpa [skewPair_apply] using h'
  have hcomb : (-(polar Q x (g e))) • e + (polar Q x e) • g e = 0 := by
    simpa [neg_smul, sub_eq_add_neg, add_comm] using hψx
  have ha : polar Q x e = 0 := (h.indep _ _ hcomb).2
  have hxe : polar Q x e ≠ 0 := by rwa [polar_comm]
  exact hxe ha

theorem heisPsi_skewPair (h : HeisData Q g e d) (x : V) :
    heisPsi Q g e d (skewPair Q e (g e) x) = 0 := by
  have h0 : heisPsi Q g e d e = 0 := by simpa using heisPsi_orbit_e h 0
  have h1 : heisPsi Q g e d (g e) = 0 := by simpa using heisPsi_orbit_e h 1
  simp only [skewPair_apply, map_sub, map_smul, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    LinearEquiv.coe_one, id_eq]
  rw [h0, h1]
  simp

theorem skewPair_heisPsi (h : HeisData Q g e d) (x : V) :
    skewPair Q e (g e) (heisPsi Q g e d x) = 0 := by
  have h0 : heisPsi Q g e d e = 0 := by simpa using heisPsi_orbit_e h 0
  have h1 : heisPsi Q g e d (g e) = 0 := by simpa using heisPsi_orbit_e h 1
  rw [skewPair_apply, polar_heisPsi_left, polar_heisPsi_left, h0, h1]
  simp

theorem exists_heisenberg_pair (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {p : ℕ} (hp : p.Prime)
    [CharP K p] (h : HeisData Q g e d) :
    ∃ S T : V ≃ₗ[K] V, S ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      T ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ orderOf S = p ∧ orderOf T = p ∧
      Commute S T ∧ T ∉ Subgroup.zpowers S ∧ Commute S g ∧ Commute T g ∧
      ∀ k : V ≃ₗ[K] V, k ∈ TauCeti.QuadraticMap.orthogonalGroup Q → k e = e → k (g e) = g e →
        Commute T k := by
  obtain ⟨x₀, hx₀⟩ := exists_heisPsi_sq_ne_zero h h3
  have hψne : heisPsi Q g e d ≠ 0 := by
    intro hzero
    exact hx₀ (by simp [hzero])
  have hψ'2 : ∀ x, skewPair Q e (g e) (skewPair Q e (g e) x) = 0 := skewPair_sq_eq_zero h
  have hψ' : ∀ x, skewPair Q e (g e) (skewPair Q e (g e) (skewPair Q e (g e) x)) = 0 :=
    fun x => by rw [hψ'2 x, map_zero]
  refine ⟨expSkew (heisPsi Q g e d) h2 (heisPsi_cube h),
    expSkew (skewPair Q e (g e)) h2 hψ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact expSkew_mem_orthogonalGroup h2 (heisPsi_cube h) polar_heisPsi_left
  · exact expSkew_mem_orthogonalGroup h2 hψ' (polar_skewPair_left e (g e))
  · exact orderOf_expSkew_of_charP h2 (heisPsi_cube h) hp hψne
  · exact orderOf_expSkew_of_charP h2 hψ' hp (skewPair_ne_zero h)
  · exact commute_expSkew_expSkew h2 (heisPsi_cube h) hψ' (fun x => by
      rw [heisPsi_skewPair h x, skewPair_heisPsi h x])
  · exact expSkew_not_mem_zpowers h2 (heisPsi_cube h) hψ' hψ'2 (skewPair_ne_zero h)
      ⟨x₀, hx₀⟩
  · exact commute_expSkew_of_commute h2 (heisPsi_cube h) (heisPsi_map_apply h)
  · exact commute_expSkew_of_commute h2 hψ' (skewPair_map_g h)
  · intro k hk hke hkge
    exact commute_expSkew_of_commute h2 hψ' (fun x => by
      have h' := skewPair_map_apply hk e (g e) x
      rwa [hke, hkge] at h')

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

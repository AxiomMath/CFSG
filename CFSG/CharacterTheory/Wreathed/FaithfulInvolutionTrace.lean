module

public import CFSG.CharacterTheory.Semidihedral.Principal.CosetConstantHalfDegree

public section

open scoped BigOperators

namespace CFSG.Wreathed

open CFSG.Semidihedral.Principal.EigenCalculus

section Scalar

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem complex_eq_one_of_norm_eq_one_of_re_eq_one {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re = 1) :
    z = 1 := by
  have hsq : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hz] at h
    norm_num at h
    exact h
  have him : z.im = 0 := by
    rw [hre] at hsq
    have h : z.im * z.im = 0 := by linarith
    exact mul_self_eq_zero.mp h
  exact Complex.ext (by simp [hre]) (by simp [him])

omit [FiniteDimensional ℂ W] in
theorem apply_eq_of_isInternal {ι : Type*} [DecidableEq ι] {E : ι → Submodule ℂ W}
    (hE : DirectSum.IsInternal E) (f : Module.End ℂ W) (c : ℂ) (hf : ∀ j, ∀ v ∈ E j, f v = c • v)
    (v : W) : f v = c • v := by
  have hv : v ∈ ⨆ j, E j := by
    rw [hE.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction E (motive := fun v => f v = c • v) hv hf (by simp) ?_
  intro x y hx hy
  rw [map_add, hx, hy, smul_add]

omit [FiniteDimensional ℂ W] in
theorem restrict_pow_eq_one (f : Module.End ℂ W) {p : Submodule ℂ W} (h : ∀ x ∈ p, f x ∈ p)
    {n : ℕ} (hf : f ^ n = 1) : (f.restrict h) ^ n = 1 := by
  have key : ∀ m : ℕ, ∀ v : p, (((f.restrict h) ^ m) v : W) = (f ^ m) v := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih v]
      rfl
  ext v
  rw [key, hf]
  rfl

theorem exists_smul_of_norm_trace_eq_finrank (s : Module.End ℂ W) {n : ℕ} (hn : n ≠ 0)
    (hs : s ^ n = 1) (htr : ‖LinearMap.trace ℂ W s‖ = Module.finrank ℂ W) :
    ∃ c : ℂ, ∀ v, s v = c • v := by
  classical
  by_cases hk : Module.finrank ℂ W = 0
  · refine ⟨0, fun v => ?_⟩
    have : Subsingleton W := Module.finrank_zero_iff.mp hk
    exact Subsingleton.elim _ _
  have hζ := Complex.isPrimitiveRoot_exp n hn
  have hint := isInternal_eigenspaces hn hs hζ
  have htrace : LinearMap.trace ℂ W s = ∑ j : Fin n,
      Complex.exp (2 * Real.pi * Complex.I / n) ^ (j : ℕ) *
        (Module.finrank ℂ (s.eigenspace (Complex.exp (2 * Real.pi * Complex.I / n) ^ (j : ℕ))) :
          ℂ) := by
    have h := trace_mul_pow_eq_sum (Commute.one_right s) hn hs hζ 1
    simp only [pow_one, one_mul] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [show (1 : Module.End ℂ W).restrict (mapsTo_eigenspace (Commute.one_right s) _) = 1
      from by ext; rfl, LinearMap.trace_one]
  have hsum : ∑ j : Fin n, (Module.finrank ℂ
      (s.eigenspace (Complex.exp (2 * Real.pi * Complex.I / n) ^ (j : ℕ))) : ℝ) =
        Module.finrank ℂ W := by
    rw [finrank_eq_sum hn hs hζ, Nat.cast_sum]
  set ζ := Complex.exp (2 * Real.pi * Complex.I / n) with hζdef
  set d : Fin n → ℕ := fun j => Module.finrank ℂ (s.eigenspace (ζ ^ (j : ℕ))) with hd
  set k : ℝ := (Module.finrank ℂ W : ℝ) with hkdef
  have hkpos : 0 < k := by
    simp only [hkdef]
    exact_mod_cast Nat.pos_of_ne_zero hk
  set c : ℂ := LinearMap.trace ℂ W s / k with hc
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hck : LinearMap.trace ℂ W s = c * k := by
    rw [hc, div_mul_cancel₀ _ hk0]
  have hcnorm : ‖c‖ = 1 := by
    rw [hc, norm_div, htr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkpos]
    exact div_self hkpos.ne'
  have hroot : ∀ j : Fin n, ‖ζ ^ (j : ℕ)‖ = 1 := fun j => by
    rw [norm_pow, hζ.norm'_eq_one hn, one_pow]
  have hre : ∑ j, (d j : ℝ) * (starRingEnd ℂ c * ζ ^ (j : ℕ)).re = k := by
    have h1 : ∑ j, (d j : ℝ) * (starRingEnd ℂ c * ζ ^ (j : ℕ)).re =
        (starRingEnd ℂ c * LinearMap.trace ℂ W s).re := by
      rw [htrace, Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show starRingEnd ℂ c * (ζ ^ (j : ℕ) * (d j : ℂ)) =
        ((d j : ℝ) : ℂ) * (starRingEnd ℂ c * ζ ^ (j : ℕ)) by push_cast; ring,
        Complex.re_ofReal_mul]
    rw [h1, hck, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      hcnorm]
    simp
  have hkey : ∑ j, (d j : ℝ) * (1 - (starRingEnd ℂ c * ζ ^ (j : ℕ)).re) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [hre]
    simp only [hd]
    rw [hsum]
    ring
  have hle : ∀ j : Fin n, (starRingEnd ℂ c * ζ ^ (j : ℕ)).re ≤ 1 := by
    intro j
    calc (starRingEnd ℂ c * ζ ^ (j : ℕ)).re ≤ ‖starRingEnd ℂ c * ζ ^ (j : ℕ)‖ :=
          Complex.re_le_norm _
      _ = 1 := by rw [norm_mul, Complex.norm_conj, hcnorm, hroot j, one_mul]
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (d j : ℝ) * (1 - (starRingEnd ℂ c * ζ ^ (j : ℕ)).re) := fun j _ =>
    mul_nonneg (Nat.cast_nonneg _) (by linarith [hle j])
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hkey
  have hval : ∀ j : Fin n, d j ≠ 0 → ζ ^ (j : ℕ) = c := by
    intro j hj
    have h := hzero j (Finset.mem_univ j)
    have hdpos : (0 : ℝ) < d j := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hre1 : (starRingEnd ℂ c * ζ ^ (j : ℕ)).re = 1 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hdpos.ne'
      · linarith
    have hnorm1 : ‖starRingEnd ℂ c * ζ ^ (j : ℕ)‖ = 1 := by
      rw [norm_mul, Complex.norm_conj, hcnorm, hroot j, one_mul]
    have h1 := complex_eq_one_of_norm_eq_one_of_re_eq_one hnorm1 hre1
    have hcc : c * starRingEnd ℂ c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hcnorm]
      simp
    calc ζ ^ (j : ℕ) = c * (starRingEnd ℂ c * ζ ^ (j : ℕ)) := by
          rw [← mul_assoc, hcc, one_mul]
      _ = c := by rw [h1, mul_one]
  refine ⟨c, apply_eq_of_isInternal hint s c fun j v hv => ?_⟩
  by_cases hdj : d j = 0
  · have hbot : s.eigenspace (ζ ^ (j : ℕ)) = ⊥ := Submodule.finrank_eq_zero.mp hdj
    rw [hbot, Submodule.mem_bot] at hv
    rw [hv, map_zero, smul_zero]
  · rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv, hval j hdj]

end Scalar

theorem faithful_involution_eigenspace_extremal_trace_centralization {K V : Type*} [Group K]
    [Finite K] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ K V) (hfaith : Function.Injective ρ) {x : K} (hx : orderOf x = 2)
    (R : Subgroup K) (hR : R ≤ Subgroup.centralizer {x})
    (hconst : ∀ r ∈ R, ρ.character (x * r) = ρ.character x) :
    (∀ r ∈ R, LinearMap.ker (ρ x - 1) ≤ (LinearMap.ker (ρ x - 1)).comap (ρ r)) ∧
    (∀ r ∈ R, (∀ v ∈ LinearMap.ker (ρ x - 1), ρ r v = v) → r = 1) ∧
    2 * (Module.finrank ℂ (LinearMap.ker (ρ x - 1)) : ℂ) =
      Module.finrank ℂ V + ρ.character x ∧
    (Module.finrank ℂ (LinearMap.ker (ρ x - 1)) = 0 → R = ⊥) ∧
    ∀ h ∈ Subgroup.centralizer {x}, h ∈ Subgroup.normalizer (R : Set K) →
      ‖ρ.character h + ρ.character (x * h)‖ =
        2 * Module.finrank ℂ (LinearMap.ker (ρ x - 1)) →
      ∀ r ∈ R, h * r * h⁻¹ * r⁻¹ = 1 := by
  classical
  have hx2 : ρ x ^ 2 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hN := isInternal_eigenspaces_involution hx2
  let ev : Fin 2 → ℂ := ![1, -1]
  let E : Fin 2 → Submodule ℂ V := fun j => Module.End.eigenspace (ρ x) (ev j)
  have hVp : LinearMap.ker (ρ x - 1) = E 0 := by
    ext v
    simp only [E, ev, LinearMap.mem_ker, Module.End.mem_eigenspace_iff, Matrix.cons_val_zero,
      one_smul, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hcomm : ∀ c ∈ Subgroup.centralizer {x}, Commute (ρ x) (ρ c) := fun c hc => by
    change ρ x * ρ c = ρ c * ρ x
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_singleton_iff.mp hc)]
  let T : Subgroup.centralizer {x} → Fin 2 → ℂ := fun c j => LinearMap.trace ℂ (E j)
    ((ρ c).restrict (mapsTo_eigenspace (hcomm c c.2) (ev j)))
  have hsplit : ∀ c : Subgroup.centralizer {x}, ρ.character c = T c 0 + T c 1 ∧
      ρ.character (x * c) = T c 0 - T c 1 := by
    intro c
    have h0 := trace_mul_pow_eq_sum_of_isInternal (hcomm c c.2) ev hN 0
    have h1 := trace_mul_pow_eq_sum_of_isInternal (hcomm c c.2) ev hN 1
    rw [Fin.sum_univ_two] at h0 h1
    simp only [pow_zero, pow_one, mul_one, one_mul] at h0 h1
    refine ⟨h0, ?_⟩
    have hxc : x * (c : K) = c * x := (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
    change LinearMap.trace ℂ V (ρ (x * c)) = _
    rw [hxc, map_mul, h1]
    change (1 : ℂ) * T c 0 + (-1) * T c 1 = _
    ring
  have hdim : ∀ j : Fin 2, T 1 j = Module.finrank ℂ (E j) := by
    intro j
    change LinearMap.trace ℂ _ ((ρ 1).restrict _) = _
    rw [show (ρ 1).restrict (mapsTo_eigenspace (hcomm 1 (Subgroup.one_mem _)) (ev j)) = 1 from by
      ext v; simp [LinearMap.restrict_apply], LinearMap.trace_one]
  have hfin : Module.finrank ℂ V = Module.finrank ℂ (E 0) + Module.finrank ℂ (E 1) := by
    have h := finrank_eq_sum_of_isInternal ev hN
    rw [Fin.sum_univ_two] at h
    exact h
  have hchix : ρ.character x = (Module.finrank ℂ (E 0) : ℂ) - Module.finrank ℂ (E 1) := by
    have h := (hsplit 1).2
    rw [Subgroup.coe_one, mul_one, hdim 0, hdim 1] at h
    exact h
  have hfaithful : ∀ r ∈ R, (∀ v ∈ E 0, ρ r v = v) → r = 1 := by
    intro r hr htriv
    let rc : Subgroup.centralizer {x} := ⟨r, hR hr⟩
    have hT0 : T rc 0 = Module.finrank ℂ (E 0) := by
      change LinearMap.trace ℂ _ ((ρ r).restrict _) = _
      rw [show (ρ r).restrict (mapsTo_eigenspace (hcomm rc rc.2) (ev 0)) = 1 from by
        ext v; simp [LinearMap.restrict_apply, htriv v v.2], LinearMap.trace_one]
    have hT1 : T rc 1 = Module.finrank ℂ (E 1) := by
      have h := (hsplit rc).2
      change ρ.character (x * r) = _ at h
      rw [hconst r hr, hchix, hT0] at h
      linear_combination h
    have hord : (ρ r) ^ orderOf r = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hres1 : (ρ r).restrict (mapsTo_eigenspace (hcomm rc rc.2) (ev 1)) = 1 :=
      CFSG.Section1.finite_order_eq_one_of_trace_eq_finrank _ (orderOf_pos r).ne'
        (restrict_pow_eq_one _ _ hord) hT1
    have hall : ρ r = 1 := by
      ext v
      have hv := apply_eq_of_isInternal hN (ρ r) 1 (fun j w hw => by
        fin_cases j
        · rw [one_smul]
          exact htriv w hw
        · have h := congrArg (fun f => (f ⟨w, hw⟩ : V)) hres1
          simpa [LinearMap.restrict_apply] using h) v
      rw [hv, one_smul, Module.End.one_apply]
    exact hfaith (hall.trans (map_one ρ).symm)
  refine ⟨fun r hr => ?_, fun r hr htriv => hfaithful r hr (fun v hv => htriv v (hVp ▸ hv)),
    ?_, fun hk0 => ?_, fun h hh hhN hnorm r hr => ?_⟩
  · rw [hVp]
    exact fun v hv => mapsTo_eigenspace (hcomm r (hR hr)) (ev 0) v hv
  · rw [hVp, hchix, hfin]
    push_cast
    ring
  · rw [hVp] at hk0
    have hbot : E 0 = ⊥ := Submodule.finrank_eq_zero.mp hk0
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    refine hfaithful r hr fun v hv => ?_
    rw [hbot, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  ·
    let hc : Subgroup.centralizer {x} := ⟨h, hh⟩
    rw [hVp] at hnorm
    have htrace : ρ.character h + ρ.character (x * h) = 2 * T hc 0 := by
      have h1 := (hsplit hc).1
      have h2 := (hsplit hc).2
      change ρ.character h = _ at h1
      change ρ.character (x * h) = _ at h2
      rw [h1, h2]
      ring
    rw [htrace, norm_mul, Complex.norm_two] at hnorm
    have hnorm' : ‖T hc 0‖ = Module.finrank ℂ (E 0) := by linarith
    have hord : (ρ h) ^ orderOf h = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    obtain ⟨c, hcs⟩ := exists_smul_of_norm_trace_eq_finrank
      ((ρ h).restrict (mapsTo_eigenspace (hcomm h hh) (ev 0))) (orderOf_pos h).ne'
        (restrict_pow_eq_one _ _ hord) hnorm'
    have hscalar : ∀ w ∈ E 0, ρ h w = c • w := by
      intro w hw
      have h' := congrArg Subtype.val (hcs ⟨w, hw⟩)
      simpa [LinearMap.restrict_apply] using h'
    have hmem : ∀ g ∈ Subgroup.centralizer {x}, ∀ w ∈ E 0, ρ g w ∈ E 0 :=
      fun g hg w hw => mapsTo_eigenspace (hcomm g hg) (ev 0) w hw
    have hcommR : h * r * h⁻¹ * r⁻¹ ∈ R := by
      have hhr : h * r * h⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hhN r).mp hr
      exact R.mul_mem hhr (R.inv_mem hr)
    refine hfaithful _ hcommR fun v hv => ?_
    have hw : ρ (h⁻¹ * r⁻¹) v ∈ E 0 :=
      hmem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) (Subgroup.inv_mem _ (hR hr))) v hv
    have hrw : ρ r (ρ (h⁻¹ * r⁻¹) v) ∈ E 0 := hmem r (hR hr) _ hw
    calc ρ (h * r * h⁻¹ * r⁻¹) v = ρ h (ρ r (ρ (h⁻¹ * r⁻¹) v)) := by
          rw [show h * r * h⁻¹ * r⁻¹ = h * r * (h⁻¹ * r⁻¹) by group, map_mul, map_mul]
          rfl
      _ = c • ρ r (ρ (h⁻¹ * r⁻¹) v) := hscalar _ hrw
      _ = ρ r (c • ρ (h⁻¹ * r⁻¹) v) := by rw [map_smul]
      _ = ρ r (ρ h (ρ (h⁻¹ * r⁻¹) v)) := by rw [hscalar _ hw]
      _ = v := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
            show r * h * (h⁻¹ * r⁻¹) = 1 by group, map_one, Module.End.one_apply]

end CFSG.Wreathed

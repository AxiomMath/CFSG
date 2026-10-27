module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenInr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec9ci_ext {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V} {g g' : OGroup Q}
    (h : ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = (g' : V ≃ₗ[ZMod 3] V) (b i)) : g = g' := by
  exact Subtype.ext (b.ext' h)

theorem sec9ci_perm_conj_diag {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V} {g d : OGroup Q}
    {σ : Equiv.Perm (Fin n)} {S : Finset (Fin n)}
    (hg : ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = b (σ i))
    (hd : ∀ i, (d : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ S then (-1 : ZMod 3) else 1) • b i) :
    ∀ i, ((g * d * g⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) (b i) =
      (if i ∈ S.map σ.toEmbedding then (-1 : ZMod 3) else 1) • b i := by
  intro i
  set k : Fin n := σ.symm i with hk
  have hgk : (g : V ≃ₗ[ZMod 3] V) (b k) = b i := by
    rw [hg k]
    simp [hk]
  have hginv : ((g⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) (b i) = b k := by
    rw [Subgroup.coe_inv]
    exact (LinearEquiv.symm_apply_eq _).2 hgk.symm
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hginv, Subgroup.coe_mul, LinearEquiv.mul_apply,
    hd k, map_smul, hgk]
  congr 1
  have hiff : (i ∈ S.map σ.toEmbedding) ↔ (k ∈ S) := Finset.mem_map_equiv
  by_cases h : i ∈ S.map σ.toEmbedding
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hk' => h (hiff.mpr hk'))]

private theorem sec9ci_norm_sub {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    (hpol : ∀ i j : Fin n, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0)
    (hc : ∀ i j : Fin n, Q (b i) = Q (b j)) {x y : Fin n} (hxy : x ≠ y) :
    Q (b x - b y) = (2 : ZMod 3) * Q (b x) := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q (b x) (-(b y)), QuadraticMap.map_neg,
    QuadraticMap.polar_neg_right, hpol x y hxy, hc y x, neg_zero, add_zero]
  ring

private theorem sec9ci_polar_sub {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    (hpol : ∀ i j : Fin n, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0)
    (hc : ∀ i j : Fin n, Q (b i) = Q (b j)) {x y i : Fin n} (hxy : x ≠ y) :
    QuadraticMap.polar Q (b x - b y) (b i) =
      (if i = x then (2 : ZMod 3) * Q (b x)
        else if i = y then -((2 : ZMod 3) * Q (b x)) else 0) := by
  rw [QuadraticMap.polar_sub_left]
  split_ifs with hix hiy
  · rw [hix, QuadraticMap.polar_self, hpol y x hxy.symm, sub_zero]
    ring
  · rw [hiy, hpol x y hxy, QuadraticMap.polar_self, hc y x, zero_sub]
    ring
  · rw [hpol x i (fun h => hix h.symm), hpol y i (fun h => hiy h.symm), sub_zero]

private theorem sec9ci_refl_sub {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    (hpol : ∀ i j : Fin n, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0)
    (hc : ∀ i j : Fin n, Q (b i) = Q (b j)) {x y : Fin n} (hxy : x ≠ y)
    (hd : Q (b x - b y) ≠ 0) :
    ∀ i, ((reflOf Q (b x - b y) hd : OGroup Q) : V ≃ₗ[ZMod 3] V) (b i) =
      b (Equiv.swap x y i) := by
  intro i
  rw [coe_reflOf_apply (b x - b y) hd (b i)]
  have h2 : (2 : ZMod 3) * Q (b x) ≠ 0 := by
    rwa [sec9ci_norm_sub hpol hc hxy] at hd
  by_cases hix : i = x
  · rw [hix, sec9ci_polar_sub hpol hc hxy, if_pos rfl, sec9ci_norm_sub hpol hc hxy,
      div_self h2, one_smul, Equiv.swap_apply_left]
    abel
  · by_cases hiy : i = y
    · rw [hiy, sec9ci_polar_sub hpol hc hxy, if_neg (fun h : y = x => hxy h.symm), if_pos rfl,
        sec9ci_norm_sub hpol hc hxy, neg_div, div_self h2, neg_one_smul,
        Equiv.swap_apply_right]
      abel
    · rw [sec9ci_polar_sub hpol hc hxy, if_neg hix, if_neg hiy,
        Equiv.swap_apply_of_ne_of_ne hix hiy]
      simp

private theorem sec9ci_cycle_cube_apply {α : Type*} [DecidableEq α] {u v w : α}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (i : α) :
    (Equiv.swap u w * Equiv.swap u v)
      ((Equiv.swap u w * Equiv.swap u v)
        ((Equiv.swap u w * Equiv.swap u v) i)) = i := by
  have h := Equiv.Perm.congr_fun (sec9ci_cycle_cube huv huw hvw) i
  simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h

theorem sec9ci_exists_cycle (hQ : Q.Nondegenerate) {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    (hpol : ∀ i j : Fin n, i ≠ j → QuadraticMap.polar Q (b i) (b j) = 0)
    (hc : ∀ i j : Fin n, Q (b i) = Q (b j)) (hne : ∀ i : Fin n, Q (b i) ≠ 0) {u v w : Fin n}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ∃ g ∈ omegaGroup hQ, (∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) =
      b ((Equiv.swap u w * Equiv.swap u v) i)) ∧ g * g * g = 1 := by
  have h2c : (2 : ZMod 3) * Q (b u) ≠ 0 := mul_ne_zero (by decide) (hne u)
  have hv : Q (b u - b v) ≠ 0 := by
    rw [sec9ci_norm_sub hpol hc huv]; exact h2c
  have hw : Q (b u - b w) ≠ 0 := by
    rw [sec9ci_norm_sub hpol hc huw]; exact h2c
  have hnorm : Q (b u - b w) = Q (b u - b v) := by
    rw [sec9ci_norm_sub hpol hc huw, sec9ci_norm_sub hpol hc huv]
  set g : OGroup Q := reflOf Q (b u - b w) hw * reflOf Q (b u - b v) hv with hgdef
  have hgact : ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) =
      b ((Equiv.swap u w * Equiv.swap u v) i) := by
    intro i
    rw [hgdef, Subgroup.coe_mul, LinearEquiv.mul_apply,
      sec9ci_refl_sub hpol hc huv hv i, sec9ci_refl_sub hpol hc huw hw]
    rfl
  have hgmem : g ∈ omegaGroup hQ := by
    rw [hgdef]
    exact reflOf_mul_reflOf_mem_omegaGroup hQ _ _ hw hv hnorm
  refine ⟨g, hgmem, hgact, ?_⟩
  apply sec9ci_ext (b := b)
  intro i
  rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    hgact, hgact, hgact]
  rw [sec9ci_cycle_cube_apply huv huw hvw i]
  simp [Subgroup.coe_one, LinearEquiv.refl_apply]

end CFSG.OddStandard.SmallF3.Omega

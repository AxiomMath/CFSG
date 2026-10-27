module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.F2

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def fixSub (E : Subgroup (V ≃ₗ[K] V)) : Submodule K V where
  carrier := {v | ∀ g ∈ E, g v = v}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  smul_mem' := fun c x hx g hg => by rw [map_smul, hx g hg]

theorem mem_fixSub {E : Subgroup (V ≃ₗ[K] V)} {v : V} : v ∈ fixSub E ↔ ∀ g ∈ E, g v = v :=
  Iff.rfl

variable (Q : QuadraticForm K V)

@[expose] def perpSub (W : Submodule K V) : Submodule K V where
  carrier := {v | ∀ w ∈ W, polar Q v w = 0}
  add_mem' := fun {a b} ha hb w hw => by rw [polar_add_left, ha w hw, hb w hw, add_zero]
  zero_mem' := fun w _ => polar_zero_left Q w
  smul_mem' := fun c x hx w hw => by rw [polar_smul_left_eq, hx w hw, mul_zero]

variable {Q}

theorem mem_perpSub {W : Submodule K V} {v : V} : v ∈ perpSub Q W ↔ ∀ w ∈ W, polar Q v w = 0 :=
  Iff.rfl

theorem isCompl_perpSub [FiniteDimensional K V] {W : Submodule K V} (hW : PolarNondegOn Q W) :
    IsCompl W (perpSub Q W) := by
  have hrefl : (polarBilin Q).IsRefl := fun x y h => by
    rw [polarBilin_apply_apply] at h ⊢
    rw [polar_comm]
    exact h
  have hnd : (LinearMap.BilinForm.restrict (polarBilin Q) W).Nondegenerate := by
    have := nondegenerate_polarBilin_restrict hW
    constructor
    · intro x hx
      refine Subtype.ext (hW x x.2 fun y hy => ?_)
      have := hx ⟨y, hy⟩
      simpa [polarBilin_apply_apply] using this
    · intro y hy
      refine Subtype.ext (hW y y.2 fun x hx => ?_)
      have := hy ⟨x, hx⟩
      rw [polar_comm]
      simpa [polarBilin_apply_apply] using this
  have h := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd
  convert h using 2
  ext v
  simp [perpSub, LinearMap.BilinForm.mem_orthogonal_iff, polarBilin_apply_apply, polar_comm Q v]

section Averaging

variable [IsF2 K] [FiniteDimensional K V]

theorem finite_linearEquiv : Finite (V ≃ₗ[K] V) := by
  have : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective

theorem natCast_eq_one_of_odd {n : ℕ} (hn : Odd n) : (n : K) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  push_cast
  rw [IsF2.two_eq_zero, zero_mul, zero_add]

theorem odd_natCard_of_pow_eq_one {G : Type*} [Group G] [Finite G] {N : ℕ} (hN : Odd N)
    (h : ∀ g : G, g ^ N = 1) : Odd (Nat.card G) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card G := by
    rcases Nat.even_or_odd (Nat.card G) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have : 2 ∣ N := hx ▸ orderOf_dvd_of_pow_eq_one (h x)
  exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr this)

theorem odd_natCard_subgroup_of_pow_eq_one {E : Subgroup (V ≃ₗ[K] V)} {N : ℕ} (hN : Odd N)
    (hE : ∀ g ∈ E, g ^ N = 1) : Odd (Nat.card E) := by
  have := finite_linearEquiv (K := K) (V := V)
  have : Finite E := inferInstance
  refine odd_natCard_of_pow_eq_one hN fun g => ?_
  have := hE g g.2
  exact Subtype.ext (by simpa using this)

@[expose] noncomputable def avgOp (E : Subgroup (V ≃ₗ[K] V)) (v : V) : V :=
  ∑ᶠ g : E, (g : V ≃ₗ[K] V) v

omit [IsF2 K] [FiniteDimensional K V] in
theorem avgOp_eq_sum (E : Subgroup (V ≃ₗ[K] V)) [Fintype E] (v : V) :
    avgOp E v = ∑ g : E, (g : V ≃ₗ[K] V) v :=
  finsum_eq_sum_of_fintype _

theorem avgOp_mem_fixSub (E : Subgroup (V ≃ₗ[K] V)) (v : V) : avgOp E v ∈ fixSub E := by
  have := finite_linearEquiv (K := K) (V := V)
  have : Finite E := inferInstance
  have := Fintype.ofFinite E
  intro h hh
  rw [avgOp_eq_sum, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : E)) _ _ fun g => rfl

theorem polar_avgOp {E : Subgroup (V ≃ₗ[K] V)} (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hodd : Odd (Nat.card E)) (v : V) {w : V} (hw : w ∈ fixSub E) :
    polar Q (avgOp E v) w = polar Q v w := by
  have := finite_linearEquiv (K := K) (V := V)
  have : Finite E := inferInstance
  have := Fintype.ofFinite E
  rw [avgOp_eq_sum, ← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
  have : ∀ g : E, polarBilin Q ((g : V ≃ₗ[K] V) v) w = polarBilin Q v w := fun g => by
    rw [polarBilin_apply_apply, polarBilin_apply_apply]
    conv_lhs => rw [← hw g g.2]
    exact polar_map_of_mem (hEO g.2) v w
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, natCast_eq_one_of_odd hodd, one_smul,
    polarBilin_apply_apply]

end Averaging

section Commute

theorem apply_mem_fixSub_of_commute {E : Subgroup (V ≃ₗ[K] V)} {g : V ≃ₗ[K] V}
    (hc : ∀ h ∈ E, g * h = h * g) {v : V} (hv : v ∈ fixSub E) : g v ∈ fixSub E := by
  intro h hh
  rw [← LinearEquiv.mul_apply, ← hc h hh, LinearEquiv.mul_apply, hv h hh]

theorem apply_mem_perpSub_fixSub_of_commute {E : Subgroup (V ≃ₗ[K] V)} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hc : ∀ h ∈ E, g * h = h * g) {x : V}
    (hx : x ∈ perpSub Q (fixSub E)) : g x ∈ perpSub Q (fixSub E) := by
  intro w hw
  have hw' : g⁻¹ w ∈ fixSub E := by
    intro h hh
    apply g.injective
    rw [← LinearEquiv.mul_apply, hc h hh, LinearEquiv.mul_apply, LinearEquiv.apply_inv_apply',
      hw h hh]
  have := polar_map_of_mem hg x (g⁻¹ w)
  rw [LinearEquiv.apply_inv_apply'] at this
  rw [this]
  exact hx _ hw'

end Commute

section Fixed

variable [IsF2 K] [FiniteDimensional K V]

theorem polarNondegOn_fixSub (hQ : (polarBilin Q).Nondegenerate) {E : Subgroup (V ≃ₗ[K] V)}
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card E)) :
    PolarNondegOn Q (fixSub E) := by
  intro x hx hxx
  apply eq_zero_of_polar_eq_zero hQ
  intro v
  have h := polar_avgOp hEO hodd v hx
  rw [polar_comm Q x v, ← h, polar_comm]
  exact hxx _ (avgOp_mem_fixSub E v)

theorem isCompl_fixSub_perpSub (hQ : (polarBilin Q).Nondegenerate) {E : Subgroup (V ≃ₗ[K] V)}
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card E)) :
    IsCompl (fixSub E) (perpSub Q (fixSub E)) :=
  isCompl_perpSub (polarNondegOn_fixSub hQ hEO hodd)

theorem fixSub_inf_perpSub_fixSub (hQ : (polarBilin Q).Nondegenerate)
    {E : Subgroup (V ≃ₗ[K] V)} (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hodd : Odd (Nat.card E)) : fixSub E ⊓ perpSub Q (fixSub E) = ⊥ :=
  (isCompl_fixSub_perpSub hQ hEO hodd).inf_eq_bot

theorem eq_zero_of_mem_perpSub_fixSub (hQ : (polarBilin Q).Nondegenerate)
    {E : Subgroup (V ≃ₗ[K] V)} (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hodd : Odd (Nat.card E)) {x : V} (hx : x ∈ perpSub Q (fixSub E))
    (hfix : ∀ g ∈ E, g x = x) : x = 0 := by
  have : x ∈ fixSub E ⊓ perpSub Q (fixSub E) := ⟨hfix, hx⟩
  rw [fixSub_inf_perpSub_fixSub hQ hEO hodd] at this
  exact this

omit [IsF2 K] [FiniteDimensional K V] in
theorem zpow_apply_eq_of_apply_eq {g : V ≃ₗ[K] V} {x : V} (hgx : g x = x) (k : ℤ) :
    (g ^ k) x = x := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, LinearEquiv.mul_apply, hgx, ih]
  | pred n ih =>
    rw [zpow_sub_one, LinearEquiv.mul_apply]
    have : g⁻¹ x = x := by
      conv_lhs => rw [← hgx]
      exact LinearEquiv.inv_apply_apply' g x
    rw [this, ih]

theorem eq_zero_of_mem_perpSub_fixSub_of_apply_eq (hQ : (polarBilin Q).Nondegenerate)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {N : ℕ} (hN : Odd N)
    (hgN : g ^ N = 1) {x : V} (hx : x ∈ perpSub Q (fixSub (Subgroup.zpowers g)))
    (hgx : g x = x) : x = 0 := by
  have hEO : Subgroup.zpowers g ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.zpowers_le).mpr hg
  refine eq_zero_of_mem_perpSub_fixSub hQ hEO ?_ hx ?_
  · refine odd_natCard_subgroup_of_pow_eq_one hN fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgN, one_zpow]
  · intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact zpow_apply_eq_of_apply_eq hgx k

omit [IsF2 K] [FiniteDimensional K V] in
theorem mem_fixSub_zpowers {g : V ≃ₗ[K] V} {v : V} :
    v ∈ fixSub (Subgroup.zpowers g) ↔ g v = v := by
  refine ⟨fun h => h g (Subgroup.mem_zpowers g), fun hgv h hh => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact zpow_apply_eq_of_apply_eq hgv k

end Fixed

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPOmegaPlusCount
public import CFSG.LieType.BorelTits.OrthogonalForm

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.LieType.BorelTits

theorem omegaPlus_card_mul_eq_zero (F : Type*) [Field F] [Finite F] :
    Nat.card {p : F × F // p.1 * p.2 = 0} = 2 * Nat.card F - 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hset : (Finset.univ.filter fun p : F × F => p.1 * p.2 = 0) =
      (Finset.univ.filter fun p : F × F => p.1 = 0) ∪
        (Finset.univ.filter fun p : F × F => p.2 = 0) := by
    ext p
    simp [mul_eq_zero]
  have hA : (Finset.univ.filter fun p : F × F => p.1 = 0) =
      ({0} : Finset F) ×ˢ (Finset.univ : Finset F) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]
  have hB : (Finset.univ.filter fun p : F × F => p.2 = 0) =
      (Finset.univ : Finset F) ×ˢ ({0} : Finset F) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, true_and]
  have hAB : (Finset.univ.filter fun p : F × F => p.1 = 0) ∩
      (Finset.univ.filter fun p : F × F => p.2 = 0) = {((0 : F), (0 : F))} := by
    ext p
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Prod.ext_iff]
  have h := Finset.card_union_add_card_inter (Finset.univ.filter fun p : F × F => p.1 = 0)
    (Finset.univ.filter fun p : F × F => p.2 = 0)
  rw [← hset, hAB, hA, hB] at h
  simp only [Finset.card_product, Finset.card_singleton, Finset.card_univ, one_mul,
    mul_one] at h
  omega

variable {F V : Type*} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [Module.Finite F V] (Φ : QuadForm F V)

theorem omegaPlus_polar_smul_smul (a b : F) (u v : V) :
    Φ.polar.β (a • u) (b • v) = a * b * Φ.polar.β u v := by
  rw [Φ.polar.smul_left, Φ.polar_σ, RingEquiv.refl_apply, Φ.polar.smul_right]
  ring

theorem omegaPlus_polar_self_eq_zero {z : V} (hz : Φ.Q z = 0) : Φ.polar.β z z = 0 := by
  rw [Φ.polar_self, hz, mul_zero]

theorem omegaPlus_exists_fixed_polar_ne_zero {r e : ℕ} (hr : r.Prime) (g : V →ₗ[F] V)
    (hg : g ^ r = 1) (he : 3 ≤ e) (hord : ∀ m : ℕ, r ∣ Nat.card F ^ m - 1 ↔ e ∣ m)
    (hdim : Module.finrank F V = e + 2) (hg1 : g ≠ 1) (hQ : ∀ v, Φ.Q (g v) = Φ.Q v)
    {z : V} (hz0 : z ≠ 0) (hgz : g z = z) :
    ∃ y ∈ LinearMap.ker (g - 1), Φ.polar.β z y ≠ 0 := by
  by_contra hno
  push Not at hno
  have hPz : ∀ v ∈ Φ.polar.perp (F ∙ z), g v ∈ Φ.polar.perp (F ∙ z) := by
    intro v hv
    rw [Φ.polar.mem_perp_span_singleton] at hv ⊢
    have h := Φ.polar_map_of_Q hQ z v
    rw [hgz] at h
    rw [h]
    exact hv
  have h1 := Φ.polar.finrank_perp (F ∙ z)
  have h2 : Module.finrank F (F ∙ z) = 1 := finrank_span_singleton hz0
  have hdimP : Module.finrank F (Φ.polar.perp (F ∙ z)) = e + 1 := by omega
  have hle : LinearMap.ker (g - 1) ≤ Φ.polar.perp (F ∙ z) := fun y hy =>
    Φ.polar.mem_perp_span_singleton.mpr (hno y hy)
  have hinf : Φ.polar.perp (F ∙ z) ⊓ LinearMap.ker (g - 1) = LinearMap.ker (g - 1) :=
    inf_eq_right.mpr hle
  have hd := omegaPlus_dvd_finrank_sub hr g hg (by omega) hord _ hPz
  rw [hinf, omegaPlus_finrank_ker_eq_two hr g hg he hord hdim hg1, hdimP] at hd
  have := Nat.le_of_dvd (by omega) hd
  omega

theorem omegaPlus_card_fixed_singular_eq {r e : ℕ} (hr : r.Prime) (g : V →ₗ[F] V) (hg : g ^ r = 1)
    (he : 3 ≤ e) (hord : ∀ m : ℕ, r ∣ Nat.card F ^ m - 1 ↔ e ∣ m)
    (hdim : Module.finrank F V = e + 2) (hg1 : g ≠ 1) {z w : V} (hz : Φ.Q z = 0)
    (hw : Φ.Q w = 0) (hzw : Φ.polar.β z w = 1) (hgz : g z = z) (hgw : g w = w) :
    Nat.card {v : V // Φ.Q v = 0 ∧ g v = v} = 2 * Nat.card F - 1 := by
  classical
  let φ : F × F →ₗ[F] V :=
    (LinearMap.toSpanSingleton F V z).coprod (LinearMap.toSpanSingleton F V w)
  have hφ : ∀ p : F × F, φ p = p.1 • z + p.2 • w := fun p => by simp [φ]
  have hwz : Φ.polar.β w z = 1 := by rw [Φ.polar_symm, hzw]
  have hQφ : ∀ p : F × F, Φ.Q (φ p) = p.1 * p.2 := by
    intro p
    rw [hφ, Φ.Q_add, Φ.Q_smul, Φ.Q_smul, hz, hw, omegaPlus_polar_smul_smul Φ, hzw]
    ring
  have hβz : ∀ p : F × F, Φ.polar.β z (φ p) = p.2 := by
    intro p
    rw [hφ, Φ.polar.add_right, Φ.polar.smul_right, Φ.polar.smul_right,
      omegaPlus_polar_self_eq_zero Φ hz, hzw]
    ring
  have hβw : ∀ p : F × F, Φ.polar.β w (φ p) = p.1 := by
    intro p
    rw [hφ, Φ.polar.add_right, Φ.polar.smul_right, Φ.polar.smul_right,
      omegaPlus_polar_self_eq_zero Φ hw, hwz]
    ring
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have h1 := hβz p
    have h2 := hβw p
    rw [hp, Φ.polar.β_zero_right] at h1 h2
    exact Prod.ext h2.symm h1.symm
  have hfix : ∀ p : F × F, g (φ p) = φ p := by
    intro p
    rw [hφ, map_add, map_smul, map_smul, hgz, hgw]
  have hzC : z ∈ LinearMap.ker (g - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hgz, Module.End.one_apply, sub_self]
  have hwC : w ∈ LinearMap.ker (g - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hgw, Module.End.one_apply, sub_self]
  have hrange_le : LinearMap.range φ ≤ LinearMap.ker (g - 1) := by
    rintro _ ⟨p, rfl⟩
    rw [hφ]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hzC) (Submodule.smul_mem _ _ hwC)
  have hrange_dim : Module.finrank F (LinearMap.range φ) = 2 := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_self]
  have hrange : LinearMap.range φ = LinearMap.ker (g - 1) :=
    Submodule.eq_of_le_of_finrank_eq hrange_le
      (by rw [hrange_dim, omegaPlus_finrank_ker_eq_two hr g hg he hord hdim hg1])
  let f : {p : F × F // p.1 * p.2 = 0} → {v : V // Φ.Q v = 0 ∧ g v = v} := fun p =>
    ⟨φ p.1, by rw [hQφ]; exact p.2, hfix p.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p p' hpp'
      exact Subtype.ext (hinj (congrArg Subtype.val hpp'))
    · intro v
      have hv : v.1 ∈ LinearMap.range φ := by
        rw [hrange, LinearMap.mem_ker, LinearMap.sub_apply, v.2.2, Module.End.one_apply, sub_self]
      obtain ⟨p, hp⟩ := hv
      refine ⟨⟨p, ?_⟩, Subtype.ext hp⟩
      rw [← hQφ, hp]
      exact v.2.1
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  exact omegaPlus_card_mul_eq_zero F

theorem omegaPlus_not_exists_fixed_singular {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (g : V →ₗ[F] V)
    (hg : g ^ r = 1) (he : 3 ≤ e) (hord : ∀ m : ℕ, r ∣ Nat.card F ^ m - 1 ↔ e ∣ m)
    (hdim : Module.finrank F V = e + 2) (hg1 : g ≠ 1) (hQ : ∀ v, Φ.Q (g v) = Φ.Q v)
    (hS : Nat.card {v : V // Φ.Q v = 0} ≡ 1 [MOD r]) {z : V} (hz0 : z ≠ 0) (hz : Φ.Q z = 0)
    (hgz : g z = z) : False := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  obtain ⟨y, hyC, hβ⟩ := omegaPlus_exists_fixed_polar_ne_zero Φ hr g hg he hord hdim hg1 hQ hz0 hgz
  have hgy : g y = y := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hyC
    exact hyC
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : V, y₁ = (Φ.polar.β z y)⁻¹ • y := ⟨_, rfl⟩
  have hzy₁ : Φ.polar.β z y₁ = 1 := by
    rw [hy₁, Φ.polar.smul_right, inv_mul_cancel₀ hβ]
  have hy₁z : Φ.polar.β y₁ z = 1 := by rw [Φ.polar_symm, hzy₁]
  have hgy₁ : g y₁ = y₁ := by rw [hy₁, map_smul, hgy]
  obtain ⟨w, hw⟩ : ∃ w : V, w = y₁ + Φ.Q y₁ • z := ⟨_, rfl⟩
  have hgw : g w = w := by rw [hw, map_add, map_smul, hgy₁, hgz]
  have hQw : Φ.Q w = 0 := by
    rw [hw, Φ.Q_add, Φ.Q_smul, hz, Φ.polar.smul_right, hy₁z]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (Φ.Q y₁) * h2
  have hzw : Φ.polar.β z w = 1 := by
    rw [hw, Φ.polar.add_right, Φ.polar.smul_right, omegaPlus_polar_self_eq_zero Φ hz, hzy₁]
    ring
  have hcard := omegaPlus_card_fixed_singular_eq Φ hr g hg he hord hdim hg1 hz hQw hzw hgz hgw
  have hgit : ∀ x, (⇑g)^[r] x = x := fun x => by
    rw [← Module.End.pow_apply, hg]
    rfl
  have hmod := omegaPlus_card_invariant_modEq_card_fixed hr (⇑g) hgit {v : V | Φ.Q v = 0}
    (fun v hv => by
      show Φ.Q (g v) = 0
      rw [hQ]
      exact hv)
  have hmod' : Nat.card {v : V // Φ.Q v = 0} ≡ Nat.card {v : V // Φ.Q v = 0 ∧ g v = v}
      [MOD r] := hmod
  rw [hcard] at hmod'
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have h1 : 1 ≡ 2 * Nat.card F - 1 [MOD r] := hS.symm.trans hmod'
  have h2 : r ∣ 2 * Nat.card F - 1 - 1 := (Nat.modEq_iff_dvd' (by omega)).1 h1
  have h3 : 2 * Nat.card F - 1 - 1 = 2 * (Nat.card F - 1) := by omega
  rw [h3] at h2
  rcases (Nat.Prime.dvd_mul hr).1 h2 with h | h
  · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
  · have h4 : r ∣ Nat.card F ^ 1 - 1 := by simpa using h
    have h5 := Nat.le_of_dvd one_pos ((hord 1).1 h4)
    omega

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

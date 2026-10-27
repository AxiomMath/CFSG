module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveFixedPoints
public import CFSG.LinearAlgebra.SquareZeroPowers
public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics

public section

namespace CFSG.LinearGroups

open scoped IsMulCommutative

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Quadratic

theorem generalLinearGroup_inv_apply_apply (g : LinearMap.GeneralLinearGroup K V) (x : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((g : V →ₗ[K] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

theorem generalLinearGroup_apply_inv_apply' (g : LinearMap.GeneralLinearGroup K V) (x : V) :
    (g : V →ₗ[K] V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) = x :=
  CFSG.LinearGroups.generalLinearGroup_apply_inv_apply g x

theorem quadratic_linear_p_elements (p : ℕ) [Fact p.Prime] [CharP K p] [FiniteDimensional K V]
    (a : LinearMap.GeneralLinearGroup K V) (ha : ((a : V →ₗ[K] V) - 1) ^ 2 = 0) :
    a ^ p = 1 ∧ ∀ g : LinearMap.GeneralLinearGroup K V,
      (((g⁻¹ * a * g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) - 1) ^ 2 = 0 := by
  refine ⟨?_, fun g => ?_⟩
  · apply Units.ext
    have h1 : (a : V →ₗ[K] V) = 1 + ((a : V →ₗ[K] V) - 1) := by abel
    have hp : (p : Module.End K V) = 0 := by
      rw [← map_natCast (algebraMap K (Module.End K V)), CharP.cast_eq_zero, map_zero]
    rw [Units.val_pow_eq_pow_val, h1, one_add_pow_of_sq_eq_zero ha, hp, zero_mul, add_zero,
      Units.val_one]
  · have h2 : ((g⁻¹ * a * g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) - 1 =
        ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) * ((a : V →ₗ[K] V) - 1) *
          (g : V →ₗ[K] V) := by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
    rw [h2, sq]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
    rw [← mul_assoc ((a : V →ₗ[K] V) - 1), ← sq, ha, zero_mul, mul_zero]

end Quadratic

section Induced

variable (H : Subgroup (LinearMap.GeneralLinearGroup K V)) (W : Submodule K V)

@[expose] noncomputable def invariantRestrict
    (hW : ∀ g ∈ H, ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W) : H →* LinearMap.GeneralLinearGroup K W where
  toFun g :=
    { val := (g.1 : V →ₗ[K] V).restrict (hW g.1 g.2)
      inv := ((g⁻¹).1 : V →ₗ[K] V).restrict (hW _ (g⁻¹).2)
      val_inv := LinearMap.ext fun w => Subtype.ext (generalLinearGroup_apply_inv_apply' g.1 w)
      inv_val := LinearMap.ext fun w => Subtype.ext (generalLinearGroup_inv_apply_apply g.1 w) }
  map_one' := Units.ext (LinearMap.ext fun _ => Subtype.ext rfl)
  map_mul' _ _ := Units.ext (LinearMap.ext fun _ => Subtype.ext rfl)

theorem coe_invariantRestrict_apply (hW : ∀ g ∈ H, ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W) (g : H)
    (w : W) : (((invariantRestrict H W hW g : LinearMap.GeneralLinearGroup K W) : W →ₗ[K] W) w :
      V) = (g.1 : V →ₗ[K] V) w :=
  rfl

@[expose] noncomputable def invariantQuotient
    (hW : ∀ g ∈ H, ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W) :
    H →* LinearMap.GeneralLinearGroup K (V ⧸ W) where
  toFun g :=
    { val := W.mapQ W (g.1 : V →ₗ[K] V) (by intro w hw; exact hW g.1 g.2 w hw)
      inv := W.mapQ W ((g⁻¹).1 : V →ₗ[K] V) (by intro w hw; exact hW _ (g⁻¹).2 w hw)
      val_inv := by
        ext v
        simp [Submodule.mapQ_apply, generalLinearGroup_apply_inv_apply']
      inv_val := by
        ext v
        simp [Submodule.mapQ_apply, generalLinearGroup_inv_apply_apply] }
  map_one' := by
    ext v
    simp [Submodule.mapQ_apply]
  map_mul' _ _ := by
    ext v
    simp [Submodule.mapQ_apply]

theorem invariantQuotient_apply_mk (hW : ∀ g ∈ H, ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W) (g : H)
    (v : V) : ((invariantQuotient H W hW g : LinearMap.GeneralLinearGroup K (V ⧸ W)) :
      (V ⧸ W) →ₗ[K] V ⧸ W) (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk ((g.1 : V →ₗ[K] V) v) :=
  rfl

theorem linear_p_extension (p : ℕ) [Fact p.Prime] [CharP K p] [FiniteDimensional K V] [Finite H]
    (hW : ∀ g ∈ H, ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W)
    (h1 : IsPGroup p (invariantRestrict H W hW).range)
    (h2 : IsPGroup p (invariantQuotient H W hW).range) : IsPGroup p H := by
  intro g
  obtain ⟨k₁, hk₁⟩ := h1 ⟨_, g, rfl⟩
  obtain ⟨k₂, hk₂⟩ := h2 ⟨_, g, rfl⟩
  have hk₁' : invariantRestrict H W hW (g ^ p ^ (k₁ + k₂)) = 1 := by
    have := congrArg Subtype.val hk₁
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    rw [map_pow, pow_add, pow_mul, this, one_pow]
  have hk₂' : invariantQuotient H W hW (g ^ p ^ (k₁ + k₂)) = 1 := by
    have := congrArg Subtype.val hk₂
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    rw [map_pow, pow_add, mul_comm, pow_mul, this, one_pow]
  obtain ⟨u, hu⟩ : ∃ u : H, u = g ^ p ^ (k₁ + k₂) := ⟨_, rfl⟩
  rw [← hu] at hk₁' hk₂'
  have hW1 : ∀ w ∈ W, (u.1 : V →ₗ[K] V) w = w := fun w hw => by
    have := congrArg (fun φ : LinearMap.GeneralLinearGroup K W =>
      ((φ : W →ₗ[K] W) ⟨w, hw⟩ : V)) hk₁'
    rw [coe_invariantRestrict_apply] at this
    simpa using this
  have hW2 : ∀ v, (u.1 : V →ₗ[K] V) v - v ∈ W := fun v => by
    have := congrArg (fun φ : LinearMap.GeneralLinearGroup K (V ⧸ W) =>
      (φ : (V ⧸ W) →ₗ[K] V ⧸ W) (Submodule.Quotient.mk v)) hk₂'
    simp only [invariantQuotient_apply_mk, Units.val_one, Module.End.one_apply] at this
    exact (Submodule.Quotient.eq W).mp this
  have hsq : ((u.1 : V →ₗ[K] V) - 1) ^ 2 = 0 := by
    ext v
    rw [sq, Module.End.mul_apply, LinearMap.zero_apply]
    have := hW1 _ (hW2 v)
    simpa [sub_eq_zero] using this
  refine ⟨k₁ + k₂ + 1, Subtype.ext ?_⟩
  rw [pow_succ, pow_mul, ← hu, SubgroupClass.coe_pow, (quadratic_linear_p_elements p u.1 hsq).1,
    OneMemClass.coe_one]

end Induced

section ElementaryQuotient

variable (p : ℕ) [Fact p.Prime] {P : Type*} [Group P] (N : Subgroup P) [N.Normal]
  [IsElementaryAbelian p (P ⧸ N)]

@[expose] noncomputable def quotientLinearMap (α : MulAut P) (hα : N ≤ N.comap α.toMonoidHom) :
    Module.End (ZMod p) (Additive (P ⧸ N)) :=
  (MonoidHom.toAdditive (QuotientGroup.map N N α.toMonoidHom hα)).toZModLinearMap p

theorem quotientLinearMap_apply (α : MulAut P) (hα : N ≤ N.comap α.toMonoidHom) (u : P) :
    quotientLinearMap p N α hα (Additive.ofMul (u : P ⧸ N)) =
      Additive.ofMul ((α u : P) : P ⧸ N) :=
  rfl

omit [Fact p.Prime] [N.Normal] [IsElementaryAbelian p (P ⧸ N)] in
theorem le_comap_of_map_eq {α : MulAut P} (hα : N.map α.toMonoidHom = N) :
    N ≤ N.comap α.toMonoidHom := by
  rw [← Subgroup.map_le_iff_le_comap, hα]

theorem quadratic_elementary_quotient [Finite P] (α : MulAut P) (hα : N.map α.toMonoidHom = N)
    (hfix : ∀ u : P, α (u⁻¹ * α u) = u⁻¹ * α u) :
    (quotientLinearMap p N α (le_comap_of_map_eq N hα) - 1) ^ 2 = 0 := by
  have hstep : ∀ x : P, (quotientLinearMap p N α (le_comap_of_map_eq N hα) - 1)
      (Additive.ofMul (x : P ⧸ N)) = Additive.ofMul ((x⁻¹ * α x : P) : P ⧸ N) := by
    intro x
    rw [LinearMap.sub_apply, Module.End.one_apply, quotientLinearMap_apply, ← ofMul_div]
    congr 1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, div_eq_mul_inv, mul_comm]
  ext v
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  obtain rfl : v = Additive.ofMul (u : P ⧸ N) := by rw [hu]; rfl
  rw [sq, Module.End.mul_apply, hstep, hstep, hfix, inv_mul_cancel, QuotientGroup.mk_one,
    ofMul_one, LinearMap.zero_apply]

end ElementaryQuotient

section TwoQuadratic

variable [FiniteDimensional K V]

theorem inv_mapsTo_of_mapsTo (g : LinearMap.GeneralLinearGroup K V) {W : Submodule K V}
    (hg : ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W) :
    ∀ w ∈ W, ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) w ∈ W := by
  have hle : W.map (g : V →ₗ[K] V) ≤ W := Submodule.map_le_iff_le_comap.mpr fun w hw => hg w hw
  have heq : W.map (g : V →ₗ[K] V) = W :=
    Submodule.eq_of_le_of_finrank_eq hle
      (LinearEquiv.finrank_map_eq (LinearMap.GeneralLinearGroup.generalLinearEquiv K V g) W)
  intro w hw
  rw [← heq] at hw
  obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hw
  rw [generalLinearGroup_inv_apply_apply]
  exact hw'

theorem mapsTo_of_mem_closure {S : Set (LinearMap.GeneralLinearGroup K V)} {W : Submodule K V}
    (hS : ∀ s ∈ S, ∀ w ∈ W, (s : V →ₗ[K] V) w ∈ W) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ Subgroup.closure S) : ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact fun w hw => hw
  | mul x y _ _ hx hy => exact fun w hw => hx _ (hy w hw)
  | inv x _ hx => exact inv_mapsTo_of_mapsTo x hx

omit [FiniteDimensional K V] in
theorem apply_apply_of_quadratic {a : V →ₗ[K] V} (ha : (a - 1) ^ 2 = 0) (x : V) :
    a (a x) = (2 : K) • a x - x := by
  have := congrArg (fun φ : Module.End K V => φ x) ha
  simp only [sq, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
    LinearMap.zero_apply] at this
  linear_combination (norm := module) this

theorem two_quadratic_irreducible_dimension [IsAlgClosed K] [Nontrivial V]
    (a b : LinearMap.GeneralLinearGroup K V) (ha : ((a : V →ₗ[K] V) - 1) ^ 2 = 0)
    (hb : ((b : V →ₗ[K] V) - 1) ^ 2 = 0)
    (hirr : ∀ W : Submodule K V, (∀ g ∈ Subgroup.closure
      ({a, b} : Set (LinearMap.GeneralLinearGroup K V)), ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    Module.finrank K V ≤ 2 := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((b : V →ₗ[K] V) * (a : V →ₗ[K] V))
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw0 : w ≠ 0 := hw.2
  have hbaw : (b : V →ₗ[K] V) ((a : V →ₗ[K] V) w) = μ • w := hw.apply_eq_smul
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hbaw
    have h1 := generalLinearGroup_inv_apply_apply b ((a : V →ₗ[K] V) w)
    rw [hbaw, map_zero] at h1
    have h2 := generalLinearGroup_inv_apply_apply a w
    rw [← h1, map_zero] at h2
    exact hw0 h2.symm
  have hbw : (b : V →ₗ[K] V) w = (μ⁻¹ * (2 * μ)) • w + (-μ⁻¹) • (a : V →ₗ[K] V) w := by
    have h := apply_apply_of_quadratic hb ((a : V →ₗ[K] V) w)
    rw [hbaw, map_smul] at h
    calc (b : V →ₗ[K] V) w = μ⁻¹ • (μ • (b : V →ₗ[K] V) w) := by
          rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = _ := by
          rw [h]
          module
  set W := Submodule.span K {w, (a : V →ₗ[K] V) w} with hW
  have haW : ∀ z ∈ W, (a : V →ₗ[K] V) z ∈ W := by
    intro z hz
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
    refine Submodule.mem_span_pair.mpr ⟨-t, s + 2 * t, ?_⟩
    rw [map_add, map_smul, map_smul, apply_apply_of_quadratic ha]
    module
  have hbW : ∀ z ∈ W, (b : V →ₗ[K] V) z ∈ W := by
    intro z hz
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
    refine Submodule.mem_span_pair.mpr ⟨s * (μ⁻¹ * (2 * μ)) + t * μ, s * -μ⁻¹, ?_⟩
    rw [map_add, map_smul, map_smul, hbw, hbaw]
    module
  have hinv : ∀ g ∈ Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)),
      ∀ z ∈ W, (g : V →ₗ[K] V) z ∈ W := fun g hg =>
    mapsTo_of_mem_closure (by
      rintro s (rfl | rfl)
      · exact haW
      · exact hbW) hg
  rcases hirr W hinv with hbot | htop
  · exact absurd (hbot ▸ Submodule.subset_span (by simp) : w ∈ (⊥ : Submodule K V))
      (by simpa using hw0)
  · have hrange : Set.range ![w, (a : V →ₗ[K] V) w] = {w, (a : V →ₗ[K] V) w} := by
      ext x
      simp [eq_comm, or_comm]
    have hle := finrank_range_le_card (R := K) ![w, (a : V →ₗ[K] V) w]
    rw [Set.finrank, hrange, ← hW, htop, finrank_top, Fintype.card_fin] at hle
    exact hle

end TwoQuadratic

section SolvableProjective

open scoped LinearAlgebra.Projectivization MatrixGroups commutatorElement

theorem exists_abelian_normalized_of_isSolvable {G : Type*} [Group G] (H : Subgroup G)
    [Group.IsSolvable H] (hH : H ≠ ⊥) :
    ∃ A : Subgroup G, A ≤ H ∧ A ≠ ⊥ ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      ∀ g ∈ H, ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
  classical
  have hex : ∃ n, derivedSeries H n = ⊥ := Group.IsSolvable.solvable
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    have htop := Nat.find_spec hex
    rw [h0, derivedSeries_zero] at htop
    apply hH
    rw [eq_bot_iff]
    intro g hg
    have : (⟨g, hg⟩ : H) ∈ (⊥ : Subgroup H) := htop ▸ Subgroup.mem_top _
    rw [Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hDk : derivedSeries H k ≠ ⊥ := Nat.find_min hex (by omega)
  have hDk1 : derivedSeries H (k + 1) = ⊥ := by rw [← hk]; exact Nat.find_spec hex
  refine ⟨(derivedSeries H k).map H.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hab : ⁅a, b⁆ ∈ derivedSeries H (k + 1) := by
      rw [derivedSeries_succ]
      exact Subgroup.commutator_mem_commutator ha hb
    rw [hDk1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
    exact congrArg Subtype.val hab
  · rintro g hg _ ⟨a, ha, rfl⟩
    exact ⟨⟨g, hg⟩ * a * ⟨g, hg⟩⁻¹, (derivedSeries_normal H k).conj_mem a ha ⟨g, hg⟩, rfl⟩

theorem perm_eq_one_of_pow_prime_pow {α : Type*} [Finite α] (hα : Nat.card α = 4) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {σ : Equiv.Perm α} {k : ℕ} (hσ : σ ^ p ^ k = 1) : σ = 1 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hσ)
  have hdvd : p ^ i ∣ 24 := by
    have := orderOf_dvd_natCard σ
    rwa [Nat.card_perm, hα, hi] at this
  rcases i with _ | i
  · rwa [pow_zero, orderOf_eq_one_iff] at hi
  · have hp24 : p ∣ 2 ^ 3 * 3 := (dvd_pow_self p (Nat.succ_ne_zero i)).trans hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hp24 with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega

variable {K : Type*} [Field K]

theorem solvable_projective_p_generated_fixed_point [IsAlgClosed K] {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) [CharP K p] (H : Subgroup PGL(Fin 2, K)) [Finite H] [Group.IsSolvable H]
    (hgen : H = Subgroup.closure {h | h ∈ H ∧ ∃ k : ℕ, h ^ p ^ k = 1})
    (halt : 5 ≤ p ∨ Odd (Nat.card H)) :
    ∃ x : ℙ K (Fin 2 → K), ∀ h ∈ H, h • x = x := by
  classical
  by_cases hH : H = ⊥
  · refine ⟨Projectivization.mk K ![1, 0] (by simp), fun h hh => ?_⟩
    rw [hH, Subgroup.mem_bot] at hh
    rw [hh, one_smul]
  obtain ⟨A, hAH, hA0, hAc, hAn⟩ := exists_abelian_normalized_of_isSolvable H hH
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA0
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have han0 : orderOf a ≠ 0 := by
    rw [← Subgroup.orderOf_mk a (hAH haA)]
    exact (orderOf_pos _).ne'
  have han1 : orderOf a ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  set r := (orderOf a).minFac with hr_def
  have hr : r.Prime := Nat.minFac_prime han1
  obtain ⟨b, hb⟩ : ∃ b, b = a ^ (orderOf a / r) := ⟨_, rfl⟩
  have hbord : orderOf b = r := by rw [hb]; exact orderOf_pow_orderOf_div han0 (Nat.minFac_dvd _)
  have hbA : b ∈ A := by rw [hb]; exact A.pow_mem haA _
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hbord
    exact hr.one_lt.ne hbord
  have hbr : b ^ r = 1 := by rw [← hbord]; exact pow_orderOf_eq_one b
  obtain ⟨R, hR⟩ : ∃ R : Subgroup PGL(Fin 2, K), ∀ x, x ∈ R ↔ x ∈ A ∧ x ^ r = 1 :=
    ⟨{ carrier := {x | x ∈ A ∧ x ^ r = 1}
       one_mem' := ⟨A.one_mem, one_pow r⟩
       mul_mem' := fun {x y} hx hy => ⟨A.mul_mem hx.1 hy.1, by
         rw [Commute.mul_pow (hAc x hx.1 y hy.1) r, hx.2, hy.2, one_mul]⟩
       inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ },
      fun x => Iff.rfl⟩
  have hRH : R ≤ H := fun x hx => hAH ((hR x).mp hx).1
  have hRn : ∀ g ∈ H, ∀ x ∈ R, g * x * g⁻¹ ∈ R := fun g hg x hx => by
    obtain ⟨hxA, hxr⟩ := (hR x).mp hx
    exact (hR _).mpr ⟨hAn g hg x hxA, by rw [conj_pow, hxr, mul_one, mul_inv_cancel]⟩
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    hAc x ((hR x).mp hx).1 y ((hR y).mp hy).1
  have hbR : b ∈ R := (hR b).mpr ⟨hbA, hbr⟩
  have : Finite R := Finite.of_injective _ (Subgroup.inclusion_injective hRH)
  by_cases hrp : r = p
  ·
    obtain ⟨-, x₀, hx₀, huniq⟩ := projective_p_element_fixed_point hp hb1 (k := 1)
      (by rw [pow_one, ← hrp]; exact hbr)
    refine ⟨x₀, fun g hg => ?_⟩
    have hconj : g⁻¹ * b * g ∈ R := by
      simpa using hRn g⁻¹ (H.inv_mem hg) b hbR
    have hfix' : (g⁻¹ * b * g) • x₀ = x₀ := by
      apply huniq
      rw [smul_smul, hRc _ hbR _ hconj, mul_smul, hx₀]
    apply huniq
    calc b • g • x₀ = g • (g⁻¹ * b * g) • x₀ := by
          rw [smul_smul, smul_smul]
          group
      _ = g • x₀ := by rw [hfix']
  ·
    exfalso
    obtain ⟨x, y, hxy, hfix⟩ :=
      projective_coprime_prime_fixed_points hp hr (Ne.symm hrp) hbord
    have : Nontrivial R := ⟨⟨⟨b, hbR⟩, 1, fun h => hb1 (congrArg Subtype.val h)⟩⟩
    have : IsElementaryAbelian r R :=
      { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hRc x.1 x.2 y.1 y.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (by simpa using ((hR x.1).mp x.2).2) }
    have hrank := projective_elementary_abelian_coprime_rank hp hr (Ne.symm hrp) R
    have hconjfix : ∀ g ∈ H, (∃ k : ℕ, g ^ p ^ k = 1) →
        (g⁻¹ * b * g) • x = x ∧ (g⁻¹ * b * g) • y = y := by
      intro g hg ⟨k, hk⟩
      rcases hrank with hcard | ⟨hr2, hcard⟩
      ·
        have hzp : Subgroup.zpowers b = R := by
          refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hbR) ?_
          rw [Nat.card_zpowers, hbord, hcard]
        have hmem : g⁻¹ * b * g ∈ Subgroup.zpowers b := by
          rw [hzp]
          simpa using hRn g⁻¹ (H.inv_mem hg) b hbR
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hbx : b • x = x := (hfix x).mpr (Or.inl rfl)
        have hby : b • y = y := (hfix y).mpr (Or.inr rfl)
        rw [← hj]
        exact ⟨(MulAction.mem_stabilizer_iff.mp
            (zpow_mem (MulAction.mem_stabilizer_iff.mpr hbx) j)),
          (MulAction.mem_stabilizer_iff.mp (zpow_mem (MulAction.mem_stabilizer_iff.mpr hby) j))⟩
      ·
        have hp5 : 5 ≤ p := by
          rcases halt with h5 | hoddH
          · exact h5
          · exfalso
            have h4 : 4 ∣ Nat.card H := hcard ▸ Subgroup.card_dvd_of_le hRH
            obtain ⟨m, hm⟩ := hoddH
            omega
        let σ : Equiv.Perm R :=
          { toFun := fun z => ⟨g * z * g⁻¹, hRn g hg z z.2⟩
            invFun := fun z => ⟨g⁻¹ * z * g, by simpa using hRn g⁻¹ (H.inv_mem hg) z z.2⟩
            left_inv := fun z => Subtype.ext (by simp [mul_assoc])
            right_inv := fun z => Subtype.ext (by simp [mul_assoc]) }
        have hσpow : ∀ n : ℕ, ∀ z : R, (((σ ^ n) z : R) : PGL(Fin 2, K)) =
            g ^ n * z * (g ^ n)⁻¹ := by
          intro n
          induction n with
          | zero => intro z; simp
          | succ n ih =>
            intro z
            rw [pow_succ', Equiv.Perm.mul_apply]
            change g * (((σ ^ n) z : R) : PGL(Fin 2, K)) * g⁻¹ = _
            rw [ih, pow_succ']
            group
        have hσ1 : σ ^ p ^ k = 1 := by
          ext z
          rw [hσpow, hk, one_mul, inv_one, mul_one]
          rfl
        have hσ := perm_eq_one_of_pow_prime_pow hcard hp hp5 hσ1
        have hgb : g * b * g⁻¹ = b := by
          have := congrArg (fun τ : Equiv.Perm R => ((τ ⟨b, hbR⟩ : R) : PGL(Fin 2, K))) hσ
          simpa [σ] using this
        have hgb' : g⁻¹ * b * g = b := by
          calc g⁻¹ * b * g = g⁻¹ * (g * b * g⁻¹) * g := by rw [hgb]
            _ = b := by group
        rw [hgb']
        exact ⟨(hfix x).mpr (Or.inl rfl), (hfix y).mpr (Or.inr rfl)⟩
    have htriv : ∀ g ∈ H, (∃ k : ℕ, g ^ p ^ k = 1) → g = 1 := by
      intro g hg hpk
      obtain ⟨k, hk⟩ := hpk
      obtain ⟨hcx, hcy⟩ := hconjfix g hg ⟨k, hk⟩
      have hmove : ∀ z : ℙ K (Fin 2 → K), (g⁻¹ * b * g) • z = z → b • g • z = g • z :=
          fun z hz => by
        calc b • g • z = g • (g⁻¹ * b * g) • z := by
              rw [smul_smul, smul_smul]
              group
          _ = g • z := by rw [hz]
      refine projective_p_element_two_set_trivial hp hodd hk hxy ?_
      rintro z (rfl | rfl)
      · exact (hfix _).mp (hmove _ hcx)
      · exact (hfix _).mp (hmove _ hcy)
    have hbot : H = ⊥ := by
      rw [hgen, Subgroup.closure_eq_bot_iff]
      rintro g ⟨hg, hpk⟩
      exact htriv g hg hpk
    exact hH hbot

end SolvableProjective

end CFSG.LinearGroups

module

public import CFSG.LieType.Steinberg.CentralExt.TrialityTorus
public import CFSG.LieType.Steinberg.CentralExt.TorusLift
public import CFSG.LieType.Steinberg.CentralExt.AlternatingPairing

public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.TrialityClosed

attribute [local instance] TorusLift.centerCommGroup

section General

variable {E G : Type*} [Group E] [Group G] {π : E →* G} (hcen : π.ker ≤ Subgroup.center E)
include hcen

theorem commute_lift_of_rev_sep (hπ : Function.Surjective π) {k : Type*} [Field k] {x : k → G}
    (hx : ∀ s t, x (s + t) = x s * x t) {z : E} (hxz : ∀ s, x s * π z = π z * x s) {g : G}
    {a : k} (ha : a ≠ 1) (h1 : ∀ s, g * x s * g⁻¹ = x (a * s)) (h2 : g * π z * g⁻¹ = π z)
    {y : E} {s : k} (hy : π y = x s) : y * z = z * y := by
  set φ : k → E := fun s => ⁅TorusLift.lift hπ (x s), z⁆ with hφ
  have hc : ∀ s, φ s ∈ Subgroup.center E := fun s => hcen (by
    rw [MonoidHom.mem_ker, hφ, map_commutatorElement, TorusLift.map_lift,
      commutatorElement_eq_one_iff_mul_comm]
    exact hxz s)
  have hadd : ∀ s s', φ (s + s') = φ s * φ s' := fun s s' => by
    have e1 : φ (s + s') = ⁅TorusLift.lift hπ (x s) * TorusLift.lift hπ (x s'), z⁆ :=
      TorusLift.commutatorElement_eq_of_map_eq hcen (by
        rw [map_mul, TorusLift.map_lift, TorusLift.map_lift, TorusLift.map_lift, hx]) rfl
    rw [e1]
    exact TorusLift.commutatorElement_mul_left_of_central (hc s')
  have hinv : ∀ s, φ (a * s) = φ s := fun s => by
    set e := TorusLift.lift hπ g
    have e1 : e * φ s * e⁻¹ = φ (a * s) := by
      simp only [hφ]
      rw [conjugate_commutatorElement]
      exact TorusLift.commutatorElement_eq_of_map_eq hcen (by
        rw [map_mul, map_mul, map_inv, TorusLift.map_lift, TorusLift.map_lift, h1,
          TorusLift.map_lift]) (by rw [map_mul, map_mul, map_inv, TorusLift.map_lift, h2])
    rw [← e1, Subgroup.mem_center_iff.1 (hc s) e, mul_inv_cancel_right]
  have h0 : ∀ s, φ ((a - 1) * s) = 1 := fun s => by
    have h := hadd ((a - 1) * s) s
    rw [show (a - 1) * s + s = a * s by ring, hinv] at h
    exact right_eq_mul.1 h
  have h0s := h0 ((a - 1)⁻¹ * s)
  rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 ha), one_mul] at h0s
  have hyz : ⁅y, z⁆ = φ s :=
    TorusLift.commutatorElement_eq_of_map_eq hcen (by rw [hy, TorusLift.map_lift]) rfl
  rw [← commutatorElement_eq_one_iff_mul_comm, hyz, h0s]

theorem commute_of_map_eq_commutator {z a b w : E} (ha : z * a = a * z) (hb : z * b = b * z)
    (hw : π w = ⁅π a, π b⁆) : z * w = w * z := by
  have hc : ⁅a, b⁆⁻¹ * w ∈ Subgroup.center E := hcen (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_commutatorElement, hw, inv_mul_cancel])
  have hzc : Commute z ⁅a, b⁆ := by
    have ha' : Commute z a := ha
    have hb' : Commute z b := hb
    rw [commutatorElement_def]
    exact ((ha'.mul_right hb').mul_right ha'.inv_right).mul_right hb'.inv_right
  have hcz := Subgroup.mem_center_iff.1 hc z
  calc z * w = z * ⁅a, b⁆ * (⁅a, b⁆⁻¹ * w) := by group
    _ = ⁅a, b⁆ * (z * (⁅a, b⁆⁻¹ * w)) := by rw [hzc.eq, mul_assoc]
    _ = ⁅a, b⁆ * ((⁅a, b⁆⁻¹ * w) * z) := by rw [hcz]
    _ = w * z := by group

end General

abbrev r10 : Fin (Tag.rank .G2) → ℤ := g2Root 0
abbrev r01 : Fin (Tag.rank .G2) → ℤ := g2Root 1
abbrev r11 : Fin (Tag.rank .G2) → ℤ := g2Root 4
abbrev r12 : Fin (Tag.rank .G2) → ℤ := g2Root 8
abbrev r13 : Fin (Tag.rank .G2) → ℤ := g2Root 3
abbrev r23 : Fin (Tag.rank .G2) → ℤ := g2Root 7

abbrev d10 : Fin d4.rank → ℤ := d4Root 2
abbrev d01 : Fin d4.rank → ℤ := d4Root 0
abbrev d11 : Fin d4.rank → ℤ := d4Root 5
abbrev d12 : Fin d4.rank → ℤ := d4Root 12
abbrev d13 : Fin d4.rank → ℤ := d4Root 19
abbrev d23 : Fin d4.rank → ℤ := d4Root 22
abbrev n13 : Fin d4.rank → ℤ := d4Root 21
abbrev n10 : Fin d4.rank → ℤ := d4Root 8

theorem rho_d10 : rho d10 = d10 := by decide
theorem rho_d13 : rho d13 = d13 := by decide
theorem rho_d23 : rho d23 = d23 := by decide
theorem rho_n13 : rho n13 = n13 := by decide
theorem rho_n10 : rho n10 = n10 := by decide
theorem rho_d01 : rho d01 ≠ d01 := by decide
theorem rho_d11 : rho d11 ≠ d11 := by decide
theorem rho_d12 : rho d12 ≠ d12 := by decide

theorem proj_d10 : proj d10 = r10 := by decide
theorem proj_d01 : proj d01 = r01 := by decide
theorem proj_d11 : proj d11 = r11 := by decide
theorem proj_d12 : proj d12 = r12 := by decide
theorem proj_d13 : proj d13 = r13 := by decide
theorem proj_d23 : proj d23 = r23 := by decide

theorem pr_d10 : pr (nd 0) d10 = -1 ∧ pr (nd 1) d10 = -1 ∧ pr (nd 2) d10 = 2 ∧
    pr (nd 3) d10 = -1 := by decide
theorem pr_d01 : pr (nd 0) d01 = 2 ∧ pr (nd 1) d01 = 0 ∧ pr (nd 2) d01 = -1 ∧
    pr (nd 3) d01 = 0 := by decide
theorem pr_d11 : pr (nd 0) d11 = 1 ∧ pr (nd 1) d11 = -1 ∧ pr (nd 2) d11 = 1 ∧
    pr (nd 3) d11 = -1 := by decide
theorem pr_d12 : pr (nd 0) d12 = 1 ∧ pr (nd 1) d12 = 1 ∧ pr (nd 2) d12 = 0 ∧
    pr (nd 3) d12 = -1 := by decide
theorem pr_d13 : pr (nd 0) d13 = 1 ∧ pr (nd 1) d13 = 1 ∧ pr (nd 2) d13 = -1 ∧
    pr (nd 3) d13 = 1 := by decide
theorem pr_d23 : pr (nd 0) d23 = 0 ∧ pr (nd 1) d23 = 0 ∧ pr (nd 2) d23 = 1 ∧
    pr (nd 3) d23 = 0 := by decide
theorem pr_n13 : pr (nd 0) n13 = -1 ∧ pr (nd 1) n13 = -1 ∧ pr (nd 2) n13 = 1 ∧
    pr (nd 3) n13 = -1 := by decide
theorem pr_n10 : pr (nd 0) n10 = 1 ∧ pr (nd 1) n10 = 1 ∧ pr (nd 2) n10 = -2 ∧
    pr (nd 3) n10 = 1 := by decide

section Chars

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

local notation "σu" => Units.map (RingHom.toMonoidHom σ)

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_pow,
    ofMul_zpow, ofMul_one, zero_zsmul, one_zsmul, neg_zsmul, zero_add, add_zero]
    <;> abel))

include hσ in
theorem units_map_three (t : Kˣ) : σu (σu (σu t)) = t := Units.ext (hσ t)

theorem chi_d10 (s t : Kˣ) : chi σ s t d10 = s ^ 2 * (normU σ t)⁻¹ := by
  obtain ⟨h0, h1, h2, h3⟩ := pr_d10
  rw [chi, h0, h1, h2, h3, normU]
  comm_group

theorem chi_d01 (s t : Kˣ) : chi σ s t d01 = s⁻¹ * t ^ 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := pr_d01
  rw [chi, h0, h1, h2, h3]
  comm_group

theorem chi_d11 (s t : Kˣ) : chi σ s t d11 = s * t * (σu t)⁻¹ * (σu (σu t))⁻¹ := by
  obtain ⟨h0, h1, h2, h3⟩ := pr_d11
  rw [chi, h0, h1, h2, h3]
  comm_group

theorem chi_d12 (s t : Kˣ) : chi σ s t d12 = t * σu t * (σu (σu t))⁻¹ := by
  obtain ⟨h0, h1, h2, h3⟩ := pr_d12
  rw [chi, h0, h1, h2, h3]
  comm_group

theorem chi_d13 (s t : Kˣ) : chi σ s t d13 = s⁻¹ * normU σ t := by
  obtain ⟨h0, h1, h2, h3⟩ := pr_d13
  rw [chi, h0, h1, h2, h3, normU]
  comm_group

theorem chi_d23 (s t : Kˣ) : chi σ s t d23 = s := by
  obtain ⟨h0, h1, h2, h3⟩ := pr_d23
  rw [chi, h0, h1, h2, h3]
  comm_group

theorem chi_n13 (s t : Kˣ) : chi σ s t n13 = s * (normU σ t)⁻¹ := by
  obtain ⟨h0, h1, h2, h3⟩ := pr_n13
  rw [chi, h0, h1, h2, h3, normU]
  comm_group

theorem chi_n10 (s t : Kˣ) : chi σ s t n10 = (s ^ 2)⁻¹ * normU σ t := by
  obtain ⟨h0, h1, h2, h3⟩ := pr_n10
  rw [chi, h0, h1, h2, h3, normU]
  comm_group

theorem normU_pow_two (u : Kˣ) : normU σ (u ^ 2) = normU σ u ^ 2 := by
  rw [normU, normU, map_pow, map_pow]
  comm_group

theorem chi_d01_sq (u : Kˣ) : chi σ 1 u d01 = u ^ 2 := by
  rw [chi_d01, inv_one, one_mul]

theorem chi_d11_sq (u : Kˣ) : chi σ (normU σ u) u d11 = u ^ 2 := by
  rw [chi_d11, normU]
  comm_group

include hσ in
theorem chi_d12_sq (u : Kˣ) : chi σ 1 (u * σu (σu u)) d12 = u ^ 2 := by
  rw [chi_d12]
  simp only [map_mul, units_map_three hσ]
  comm_group

@[expose] def nu (u : Kˣ) : fixedUnits σ := ⟨normU σ u, normU_mem_fixedUnits hσ u⟩

theorem nu_val (u : Kˣ) : ((nu hσ u : fixedUnits σ) : Kˣ) = normU σ u := rfl

theorem chi_one_d23 (u : Kˣ) : chi σ 1 u d23 = 1 := by rw [chi_d23]

theorem chiF_ne_one {α : Fin d4.rank → ℤ} (hfix : rho α = α) {s : fixedUnits σ} {t : Kˣ}
    (h : chi σ s t α ≠ 1) : chiF hσ hfix s t ≠ 1 := fun h1 =>
  h (Units.ext (by rw [← chiF_val hσ hfix, h1]; rfl))

theorem chiF_eq_one {α : Fin d4.rank → ℤ} (hfix : rho α = α) {s : fixedUnits σ} {t : Kˣ}
    (h : chi σ s t α = 1) : chiF hσ hfix s t = 1 :=
  Subtype.ext (by rw [chiF_val hσ hfix, h]; rfl)

end Chars

section Roots


theorem isRoot_d10 : IsRoot d4 d10 := isRoot_d4Root (by decide)
theorem isRoot_d01 : IsRoot d4 d01 := isRoot_d4Root (by decide)
theorem isRoot_d11 : IsRoot d4 d11 := isRoot_d4Root (by decide)
theorem isRoot_d12 : IsRoot d4 d12 := isRoot_d4Root (by decide)
theorem isRoot_d13 : IsRoot d4 d13 := isRoot_d4Root (by decide)
theorem isRoot_d23 : IsRoot d4 d23 := isRoot_d4Root (by decide)
theorem isRoot_n13 : IsRoot d4 n13 := isRoot_d4Root (by decide)
theorem isRoot_n10 : IsRoot d4 n10 := isRoot_d4Root (by decide)

theorem not_isRoot_of_cert {v : Fin d4.rank → ℤ}
    (h : ∀ k < (Tag.rootCertificate d4).roots.length, (Tag.rootCertificate d4).root k ≠ v) :
    ¬IsRoot d4 v := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check d4)]
  rintro ⟨k, hk, hv⟩
  exact h k hk hv

end Roots

local notation "𝕩" => xPar (rootOperatorFamily d4)

variable {K : Type} [Field K]

theorem commutator_xPar_d10_d13 (a b : K) : ⁅𝕩 d10 a, 𝕩 d13 b⁆ = 𝕩 d23 (a * b) := by
  have h2 : 2 < (Tag.rootCertificate d4).roots.length := by decide
  have h19 : 19 < (Tag.rootCertificate d4).roots.length := by decide
  have h22 : 22 < (Tag.rootCertificate d4).roots.length := by decide
  have hcheck : RootOps.repCheck d4 2 19 [(1, 1, 22, 1)] = true := by decide +kernel
  have key := commutator_eltElement_of_repCheck (τ := d4)
    (RootOps.d4_allValid : RootOps.allValid d4 = true) hcheck h22
    (α := ⟨d4Root 2, isRoot_d4Root h2⟩) (β := ⟨d4Root 19, isRoot_d4Root h19⟩)
    (RootOps.rootPos_eq h2 rfl) (RootOps.rootPos_eq h19 rfl) a b
  rw [commutatorElement_def, xPar_of_isRoot (isRoot_d4Root h2),
    xPar_of_isRoot (isRoot_d4Root h19), xPar_of_isRoot (isRoot_d4Root h22), key]
  congr 1
  push_cast
  ring

theorem commutator_xPar_d23_n10 (a b : K) : ⁅𝕩 d23 a, 𝕩 n10 b⁆ = 𝕩 d13 (-(a * b)) := by
  have h8 : 8 < (Tag.rootCertificate d4).roots.length := by decide
  have h19 : 19 < (Tag.rootCertificate d4).roots.length := by decide
  have h22 : 22 < (Tag.rootCertificate d4).roots.length := by decide
  have hcheck : RootOps.repCheck d4 22 8 [(1, 1, 19, -1)] = true := by decide +kernel
  have key := commutator_eltElement_of_repCheck (τ := d4)
    (RootOps.d4_allValid : RootOps.allValid d4 = true) hcheck h19
    (α := ⟨d4Root 22, isRoot_d4Root h22⟩) (β := ⟨d4Root 8, isRoot_d4Root h8⟩)
    (RootOps.rootPos_eq h22 rfl) (RootOps.rootPos_eq h8 rfl) a b
  rw [commutatorElement_def, xPar_of_isRoot (isRoot_d4Root h22),
    xPar_of_isRoot (isRoot_d4Root h8), xPar_of_isRoot (isRoot_d4Root h19), key]
  congr 1
  push_cast
  ring

variable {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
  {E : Type*} [Group E] {π : E →* twistedGroup σ} (hcen : π.ker ≤ Subgroup.center E)
  (hπ : Function.Surjective π)

local notation "σu" => Units.map (RingHom.toMonoidHom σ)

section Commute

include hσ

theorem commute_xL_d10_d23 (a b : fixedField σ) :
    xL hσ isRoot_d10 rho_d10 a * xL hσ isRoot_d23 rho_d23 b =
      xL hσ isRoot_d23 rho_d23 b * xL hσ isRoot_d10 rho_d10 a :=
  Subtype.ext (commute_xPar isRoot_d10 isRoot_d23 (by decide) (by decide)
    (not_isRoot_of_cert (by decide)) _ _).eq

theorem commute_xL_d13_d23 (a b : fixedField σ) :
    xL hσ isRoot_d13 rho_d13 a * xL hσ isRoot_d23 rho_d23 b =
      xL hσ isRoot_d23 rho_d23 b * xL hσ isRoot_d13 rho_d13 a :=
  Subtype.ext (commute_xPar isRoot_d13 isRoot_d23 (by decide) (by decide)
    (not_isRoot_of_cert (by decide)) _ _).eq

theorem commute_xL_d23_d10 (a b : fixedField σ) :
    xL hσ isRoot_d23 rho_d23 a * xL hσ isRoot_d10 rho_d10 b =
      xL hσ isRoot_d10 rho_d10 b * xL hσ isRoot_d23 rho_d23 a :=
  (commute_xL_d10_d23 hσ b a).symm

theorem commute_xL_n13_d10 (a b : fixedField σ) :
    xL hσ isRoot_n13 rho_n13 a * xL hσ isRoot_d10 rho_d10 b =
      xL hσ isRoot_d10 rho_d10 b * xL hσ isRoot_n13 rho_n13 a :=
  Subtype.ext (commute_xPar isRoot_n13 isRoot_d10 (by decide) (by decide)
    (not_isRoot_of_cert (by decide)) _ _).eq

theorem commute_xL_d23_d13 (a b : fixedField σ) :
    xL hσ isRoot_d23 rho_d23 a * xL hσ isRoot_d13 rho_d13 b =
      xL hσ isRoot_d13 rho_d13 b * xL hσ isRoot_d23 rho_d23 a :=
  (commute_xL_d13_d23 hσ b a).symm

theorem commute_xL_n10_d13 (a b : fixedField σ) :
    xL hσ isRoot_n10 rho_n10 a * xL hσ isRoot_d13 rho_d13 b =
      xL hσ isRoot_d13 rho_d13 b * xL hσ isRoot_n10 rho_n10 a :=
  Subtype.ext (commute_xPar isRoot_n10 isRoot_d13 (by decide) (by decide)
    (not_isRoot_of_cert (by decide)) _ _).eq

end Commute

include hcen in
theorem commPairing_xS_eq_zero [Finite K] (hK4 : Nat.card K ≠ 4) (hK9 : Nat.card K ≠ 9)
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α)
    (hsq : ∀ u : Kˣ, ∃ s : fixedUnits σ, ∃ t : Kˣ, chi σ s t α = u ^ 2) :
    TorusLift.commPairing hcen hπ (xS_add hσ hα hne) = 0 := by
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := K)
  refine Pairing.pairing_eq_zero_of_sq p hK4 hK9
    (TorusLift.commPairing_self hcen hπ (xS_add hσ hα hne)) fun u hu s t => ?_
  obtain ⟨s₀, t₀, h⟩ := hsq (Units.mk0 u hu)
  have hval : (chi σ s₀ t₀ α : K) = u ^ 2 := by
    rw [h, Units.val_pow_eq_pow_val, Units.val_mk0]
  refine TorusLift.commPairing_smul hcen hπ (xS_add hσ hα hne) (g := tor hσ s₀ t₀)
    (fun c => ?_) s t
  rw [tor_conj_xS, hval]

include hcen in
theorem commPairing_xL_eq_zero_of {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hfix : rho α = α)
    (hcomm : ∀ s t : fixedField σ, ∃ a b : E, π ⁅a, b⁆ = xL hσ hα hfix t ∧
      TorusLift.lift hπ (xL hσ hα hfix s) * a = a * TorusLift.lift hπ (xL hσ hα hfix s) ∧
      TorusLift.lift hπ (xL hσ hα hfix s) * b = b * TorusLift.lift hπ (xL hσ hα hfix s)) :
    TorusLift.commPairing hcen hπ (xL_add hσ hα hfix) = 0 := by
  refine AddMonoidHom.ext fun s => AddMonoidHom.ext fun t => ?_
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [TorusLift.commPairing_apply, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, toMul_zero,
    Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm]
  obtain ⟨a, b, hab, ha, hb⟩ := hcomm s t
  exact commute_of_map_eq_commutator hcen ha hb (by
    rw [TorusLift.map_lift, ← hab, map_commutatorElement])

theorem tor_conj_xL_of_eq_one {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hfix : rho α = α)
    {s : fixedUnits σ} {t : Kˣ} (h : chi σ s t α = 1) (c : fixedField σ) :
    tor hσ s t * xL hσ hα hfix c * (tor hσ s t)⁻¹ = xL hσ hα hfix c := by
  rw [tor_conj_xL, chiF_eq_one hσ hfix h, one_mul]

include hcen hπ in
theorem commute_lift_xL {α β : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hfix : rho α = α)
    (hβ : IsRoot d4 β) (hfixβ : rho β = β)
    (hc : ∀ a b : fixedField σ, xL hσ hβ hfixβ a * xL hσ hα hfix b =
      xL hσ hα hfix b * xL hσ hβ hfixβ a)
    {s : fixedUnits σ} {t : Kˣ} (hβ1 : chi σ s t β ≠ 1) (hα1 : chi σ s t α = 1)
    (c' : fixedField σ) {y : E} {c : fixedField σ} (hy : π y = xL hσ hβ hfixβ c) :
    y * TorusLift.lift hπ (xL hσ hα hfix c') = TorusLift.lift hπ (xL hσ hα hfix c') * y :=
  commute_lift_of_rev_sep hcen hπ (xL_add hσ hβ hfixβ) (fun a => by rw [TorusLift.map_lift]; exact hc a c')
    (chiF_ne_one hσ hfixβ hβ1) (tor_conj_xL hσ hβ hfixβ s t)
    (by rw [TorusLift.map_lift]; exact tor_conj_xL_of_eq_one hσ hα hfix hα1 c') hy

theorem coe_commutatorElement (a b : twistedGroup σ) :
    ((⁅a, b⁆ : twistedGroup σ) : adjointGroup d4 K) =
      ⁅(a : adjointGroup d4 K), (b : adjointGroup d4 K)⁆ := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]


include hcen hπ in
theorem commPairing_xL_d23_eq_zero {u : Kˣ} (hu : normU σ u ≠ 1) :
    TorusLift.commPairing hcen hπ (xL_add hσ isRoot_d23 rho_d23) = 0 := by
  refine commPairing_xL_eq_zero_of hσ hcen hπ isRoot_d23 rho_d23 fun s t => ?_
  refine ⟨TorusLift.lift hπ (xL hσ isRoot_d10 rho_d10 t),
    TorusLift.lift hπ (xL hσ isRoot_d13 rho_d13 1), ?_, ?_, ?_⟩
  · rw [map_commutatorElement, TorusLift.map_lift, TorusLift.map_lift]
    refine Subtype.ext ?_
    rw [coe_commutatorElement, xL_val, xL_val, xL_val, Subfield.coe_one,
      commutator_xPar_d10_d13 (K := K), mul_one]
  · exact (commute_lift_xL hσ hcen hπ isRoot_d23 rho_d23 isRoot_d10 rho_d10
      (commute_xL_d10_d23 hσ) (s := 1) (t := u) (by rw [chi_d10]; simpa using hu)
      (chi_one_d23 u) s (TorusLift.map_lift hπ _)).symm
  · exact (commute_lift_xL hσ hcen hπ isRoot_d23 rho_d23 isRoot_d13 rho_d13
      (commute_xL_d13_d23 hσ) (s := 1) (t := u) (by rw [chi_d13]; simpa using hu)
      (chi_one_d23 u) s (TorusLift.map_lift hπ _)).symm

include hcen hπ in
theorem commPairing_xL_d10_eq_zero {u : Kˣ} (hu : normU σ u ≠ 1) :
    TorusLift.commPairing hcen hπ (xL_add hσ isRoot_d10 rho_d10) = 0 := by
  refine commPairing_xL_eq_zero_of hσ hcen hπ isRoot_d10 rho_d10 fun s t => ?_
  have h10 : chi σ (nu hσ u) (u ^ 2) d10 = 1 := by
    rw [chi_d10, nu_val, normU_pow_two, mul_inv_cancel]
  refine ⟨TorusLift.lift hπ (xL hσ isRoot_d23 rho_d23 t),
    TorusLift.lift hπ (xL hσ isRoot_n13 rho_n13 1), ?_, ?_, ?_⟩
  · rw [map_commutatorElement, TorusLift.map_lift, TorusLift.map_lift]
    refine Subtype.ext ?_
    rw [coe_commutatorElement, xL_val, xL_val, xL_val, Subfield.coe_one]
    have h := commutator_xPar_d4Root (K := K) (t : K) 1
    rw [mul_one, ← d4Root_two] at h
    exact h
  · exact (commute_lift_xL hσ hcen hπ isRoot_d10 rho_d10 isRoot_d23 rho_d23
      (commute_xL_d23_d10 hσ) (by rw [chi_d23, nu_val]; exact hu) h10 s
      (TorusLift.map_lift hπ _)).symm
  · exact (commute_lift_xL hσ hcen hπ isRoot_d10 rho_d10 isRoot_n13 rho_n13
      (commute_xL_n13_d10 hσ) (by
        rw [chi_n13, nu_val, normU_pow_two, sq, mul_inv_rev, mul_inv_cancel_left]
        exact inv_ne_one.2 hu) h10 s (TorusLift.map_lift hπ _)).symm

include hcen hπ in
theorem commPairing_xL_d13_eq_zero {u : Kˣ} (hu : normU σ u ≠ 1) :
    TorusLift.commPairing hcen hπ (xL_add hσ isRoot_d13 rho_d13) = 0 := by
  refine commPairing_xL_eq_zero_of hσ hcen hπ isRoot_d13 rho_d13 fun s t => ?_
  have h13 : chi σ (nu hσ u) u d13 = 1 := by rw [chi_d13, nu_val, inv_mul_cancel]
  refine ⟨TorusLift.lift hπ (xL hσ isRoot_d23 rho_d23 (-t)),
    TorusLift.lift hπ (xL hσ isRoot_n10 rho_n10 1), ?_, ?_, ?_⟩
  · rw [map_commutatorElement, TorusLift.map_lift, TorusLift.map_lift]
    refine Subtype.ext ?_
    rw [coe_commutatorElement, xL_val, xL_val, xL_val, Subfield.coe_one, Subfield.coe_neg,
      commutator_xPar_d23_n10 (K := K), mul_one, neg_neg]
  · exact (commute_lift_xL hσ hcen hπ isRoot_d13 rho_d13 isRoot_d23 rho_d23
      (commute_xL_d23_d13 hσ) (by rw [chi_d23, nu_val]; exact hu) h13 s
      (TorusLift.map_lift hπ _)).symm
  · exact (commute_lift_xL hσ hcen hπ isRoot_d13 rho_d13 isRoot_n10 rho_n10
      (commute_xL_n10_d13 hσ) (by
        rw [chi_n10, nu_val, sq, mul_inv_rev, inv_mul_cancel_right]
        exact inv_ne_one.2 hu) h13 s (TorusLift.map_lift hπ _)).symm

variable (π) in
@[expose] def IsShortLift {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α)
    (Y : K → E) : Prop :=
  (∀ c d, Y (c + d) = Y c * Y d) ∧ (∀ c, π (Y c) = xS hσ hα hne c) ∧
    ∀ (s : fixedUnits σ) (t : Kˣ) (e : E), π e = tor hσ s t →
      ∀ c, e * Y c * e⁻¹ = Y ((chi σ s t α : K) * c)

variable (π) in
@[expose] def IsLongLift {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hfix : rho α = α)
    (Y : fixedField σ → E) : Prop :=
  (∀ c d, Y (c + d) = Y c * Y d) ∧ (∀ c, π (Y c) = xL hσ hα hfix c) ∧
    ∀ (s : fixedUnits σ) (t : Kˣ) (e : E), π e = tor hσ s t →
      ∀ c, e * Y c * e⁻¹ = Y (chiF hσ hfix s t * c)

theorem tor_conj_tor (s s' : fixedUnits σ) (t t' : Kˣ) :
    tor hσ s t * tor hσ s' t' * (tor hσ s t)⁻¹ = tor hσ s' t' := by
  rw [tor_commute hσ s s' t t', mul_inv_cancel_right]

include hcen in
theorem exists_isShortLift {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α)
    (h0 : TorusLift.commPairing hcen hπ (xS_add hσ hα hne) = 0) (s₀ : fixedUnits σ) (t₀ : Kˣ)
    (h1 : (chi σ s₀ t₀ α : K) ≠ 1) : ∃ Y : K → E, IsShortLift hσ π hα hne Y :=
  ⟨TorusLift.canonLift hπ (x := xS hσ hα hne) (tor hσ s₀ t₀) (chi σ s₀ t₀ α),
    TorusLift.canonLift_add hcen hπ (xS_add hσ hα hne) h0 (tor_conj_xS hσ hα hne s₀ t₀) h1,
    TorusLift.map_canonLift hπ (xS_add hσ hα hne) (tor_conj_xS hσ hα hne s₀ t₀) h1,
    fun s t _ he c => TorusLift.conj_canonLift hcen hπ (tor_conj_tor hσ s s₀ t t₀)
      (tor_conj_xS hσ hα hne s t) he c⟩

include hcen in
theorem exists_isLongLift {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hfix : rho α = α)
    (h0 : TorusLift.commPairing hcen hπ (xL_add hσ hα hfix) = 0) (s₀ : fixedUnits σ) (t₀ : Kˣ)
    (h1 : chi σ s₀ t₀ α ≠ 1) : ∃ Y : fixedField σ → E, IsLongLift hσ π hα hfix Y :=
  ⟨TorusLift.canonLift hπ (x := xL hσ hα hfix) (tor hσ s₀ t₀) (chiF hσ hfix s₀ t₀),
    TorusLift.canonLift_add hcen hπ (xL_add hσ hα hfix) h0 (tor_conj_xL hσ hα hfix s₀ t₀)
      (chiF_ne_one hσ hfix h1),
    TorusLift.map_canonLift hπ (xL_add hσ hα hfix) (tor_conj_xL hσ hα hfix s₀ t₀)
      (chiF_ne_one hσ hfix h1),
    fun s t _ he c => TorusLift.conj_canonLift hcen hπ (tor_conj_tor hσ s s₀ t t₀)
      (tor_conj_xL hσ hα hfix s t) he c⟩

end CFSG.LieType.Steinberg.CentralExt.TrialityClosed

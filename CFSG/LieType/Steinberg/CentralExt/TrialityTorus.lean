module

public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime

public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint

namespace CFSG.LieType.Steinberg.CentralExt.TrialityClosed

theorem sum_d4 (f : Fin d4.rank → ℤ) : ∑ j, f j = f (nd 0) + f (nd 1) + f (nd 2) + f (nd 3) :=
  Fin.sum_univ_four f

@[expose] def pr (i : Fin d4.rank) (α : Fin d4.rank → ℤ) : ℤ := ∑ j, d4.cartan i j * α j

theorem pr_eq (α : Fin d4.rank → ℤ) :
    pr (nd 0) α = 2 * α (nd 0) - α (nd 2) ∧ pr (nd 1) α = 2 * α (nd 1) - α (nd 2) ∧
      pr (nd 2) α = 2 * α (nd 2) - α (nd 0) - α (nd 1) - α (nd 3) ∧
      pr (nd 3) α = 2 * α (nd 3) - α (nd 2) := by
  have c00 : d4.cartan (nd 0) (nd 0) = 2 := by decide
  have c01 : d4.cartan (nd 0) (nd 1) = 0 := by decide
  have c02 : d4.cartan (nd 0) (nd 2) = -1 := by decide
  have c03 : d4.cartan (nd 0) (nd 3) = 0 := by decide
  have c10 : d4.cartan (nd 1) (nd 0) = 0 := by decide
  have c11 : d4.cartan (nd 1) (nd 1) = 2 := by decide
  have c12 : d4.cartan (nd 1) (nd 2) = -1 := by decide
  have c13 : d4.cartan (nd 1) (nd 3) = 0 := by decide
  have c20 : d4.cartan (nd 2) (nd 0) = -1 := by decide
  have c21 : d4.cartan (nd 2) (nd 1) = -1 := by decide
  have c22 : d4.cartan (nd 2) (nd 2) = 2 := by decide
  have c23 : d4.cartan (nd 2) (nd 3) = -1 := by decide
  have c30 : d4.cartan (nd 3) (nd 0) = 0 := by decide
  have c31 : d4.cartan (nd 3) (nd 1) = 0 := by decide
  have c32 : d4.cartan (nd 3) (nd 2) = -1 := by decide
  have c33 : d4.cartan (nd 3) (nd 3) = 2 := by decide
  simp only [pr, sum_d4, c00, c01, c02, c03, c10, c11, c12, c13, c20, c21, c22, c23, c30, c31,
    c32, c33]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem pr_rho (α : Fin d4.rank → ℤ) :
    pr (nd 0) (rho α) = pr (nd 3) α ∧ pr (nd 1) (rho α) = pr (nd 0) α ∧
      pr (nd 2) (rho α) = pr (nd 2) α ∧ pr (nd 3) (rho α) = pr (nd 1) α := by
  have hr : ∀ j, rho α j = α (rhoPerm.symm j) := fun j => rfl
  have h0 : rhoPerm.symm (nd 0) = nd 3 := by decide
  have h1 : rhoPerm.symm (nd 1) = nd 0 := by decide
  have h2 : rhoPerm.symm (nd 2) = nd 2 := by decide
  have h3 : rhoPerm.symm (nd 3) = nd 1 := by decide
  obtain ⟨a0, a1, a2, a3⟩ := pr_eq α
  obtain ⟨b0, b1, b2, b3⟩ := pr_eq (rho α)
  simp only [hr, h0, h1, h2, h3] at b0 b1 b2 b3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

variable {K : Type} [Field K]

@[expose] def chi (σ : K →+* K) (s t : Kˣ) (α : Fin d4.rank → ℤ) : Kˣ :=
  s ^ pr (nd 2) α * (t ^ pr (nd 0) α * Units.map σ.toMonoidHom t ^ pr (nd 1) α *
    Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t) ^ pr (nd 3) α)

theorem chi_rho {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) {s : Kˣ} (hs : σ s = s) (t : Kˣ)
    (α : Fin d4.rank → ℤ) :
    Units.map σ.toMonoidHom (chi σ s t α) = chi σ s t (rho α) := by
  obtain ⟨h0, h1, h2, h3⟩ := pr_rho α
  have hs' : Units.map σ.toMonoidHom s = s := Units.ext hs
  have ht : Units.map σ.toMonoidHom (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)) = t :=
    Units.ext (hσ t)
  simp only [chi, map_mul, map_zpow, hs', ht, h0, h1, h2, h3]
  ac_rfl

theorem chi_mem_fixedField {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) {s : Kˣ} (hs : σ s = s)
    (t : Kˣ) {α : Fin d4.rank → ℤ} (hfix : rho α = α) : ((chi σ s t α : Kˣ) : K) ∈ fixedField σ := by
  have h := congrArg (fun u : Kˣ => (u : K)) (chi_rho hσ hs t α)
  simp only [hfix, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] at h
  exact h

@[expose] def chiF {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) {α : Fin d4.rank → ℤ}
    (hfix : rho α = α) (s : fixedUnits σ) (t : Kˣ) : fixedField σ :=
  ⟨chi σ s t α, chi_mem_fixedField hσ ((mem_fixedUnits σ).1 s.2) t hfix⟩

theorem chiF_val {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) {α : Fin d4.rank → ℤ}
    (hfix : rho α = α) (s : fixedUnits σ) (t : Kˣ) : (chiF hσ hfix s t : K) = chi σ s t α :=
  rfl

@[expose] def normU (σ : K →+* K) (t : Kˣ) : Kˣ :=
  t * Units.map σ.toMonoidHom t * Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)

theorem normU_mem_fixedUnits {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (t : Kˣ) :
    normU σ t ∈ fixedUnits σ := by
  rw [mem_fixedUnits]
  simp only [normU, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, map_mul, hσ]
  ring

theorem exists_phi (σ : K →+* K) : ∃ f : K →ₗ[fixedField σ] fixedField σ, f 1 = 1 := by
  have h := (Module.forall_dual_apply_eq_zero_iff (fixedField σ) (1 : K)).not.2 one_ne_zero
  push Not at h
  obtain ⟨f, hf⟩ := h
  exact ⟨(f 1)⁻¹ • f, by simp [hf]⟩

@[expose] noncomputable def phi (σ : K →+* K) : K →ₗ[fixedField σ] fixedField σ :=
  (exists_phi σ).choose

theorem phi_one (σ : K →+* K) : phi σ 1 = 1 := (exists_phi σ).choose_spec

theorem phi_coe (σ : K →+* K) (a : fixedField σ) : phi σ (a : K) = a := by
  have h : (a : K) = a • (1 : K) := by rw [Algebra.smul_def, mul_one]; rfl
  rw [h, map_smul, phi_one, smul_eq_mul, mul_one]

theorem phi_surjective (σ : K →+* K) : Function.Surjective (phi σ) := fun a =>
  ⟨a, phi_coe σ a⟩

theorem phi_mul (σ : K →+* K) (a : fixedField σ) (c : K) : phi σ ((a : K) * c) = a * phi σ c := by
  have h : (a : K) * c = a • c := by rw [Algebra.smul_def]; rfl
  rw [h, map_smul, smul_eq_mul]

section Units

variable [Finite K] {σ : K →+* K} {q : ℕ} (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q)
include hK

theorem exists_unit_pow_ne_one {m : ℕ} (hm : 0 < m) (hlt : m < q ^ 3 - 1) :
    ∃ u : Kˣ, u ^ m ≠ 1 := by
  classical
  have : Fintype Kˣ := Fintype.ofFinite _
  by_contra h
  push Not at h
  have hle := IsCyclic.card_pow_eq_one_le (α := Kˣ) hm
  have hall : (Finset.univ.filter fun a : Kˣ => a ^ m = 1) = Finset.univ :=
    Finset.filter_true_of_mem fun a _ => h a
  rw [hall, Finset.card_univ, Fintype.card_eq_nat_card, Nat.card_units, hK] at hle
  omega

include hσq

omit [Finite K] hK in
theorem units_map_eq_pow (t : Kˣ) : Units.map σ.toMonoidHom t = t ^ q :=
  Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hσq t)

omit [Finite K] hK in
theorem normU_eq_pow (t : Kˣ) : normU σ t = t ^ (1 + q + q ^ 2) := by
  rw [normU, units_map_eq_pow hσq, units_map_eq_pow hσq, ← pow_mul, pow_add, pow_add,
    pow_one, sq]

theorem exists_normU_ne_one (hq : 3 ≤ q) : ∃ u : Kˣ, normU σ u ≠ 1 := by
  obtain ⟨u, hu⟩ := exists_unit_pow_ne_one hK (m := 1 + q + q ^ 2) (by omega) (by
    have h1 : q ^ 3 = q * q ^ 2 := by ring
    have h2 : 3 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq
    have h3 : 3 * q ≤ q ^ 2 := by nlinarith
    omega)
  exact ⟨u, by rwa [normU_eq_pow hσq]⟩

theorem exists_normU_eq_one (hq : 2 ≤ q) : ∃ t : Kˣ, normU σ t = 1 ∧ t ^ 2 ≠ 1 := by
  obtain ⟨v, hv⟩ := exists_unit_pow_ne_one hK (m := 2 * (q - 1)) (by omega) (by
    have h1 : q ^ 3 = q * q ^ 2 := by ring
    have h2 : 2 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq
    have h3 : 2 * q ≤ q ^ 2 := by nlinarith
    omega)
  refine ⟨v ^ (q - 1), ?_, by rwa [← pow_mul, mul_comm]⟩
  classical
  have : Fintype Kˣ := Fintype.ofFinite _
  have hcard : Fintype.card Kˣ = (q - 1) * (1 + q + q ^ 2) := by
    rw [Fintype.card_eq_nat_card, Nat.card_units, hK]
    have : 1 ≤ q := by omega
    zify [this, Nat.one_le_pow 3 q (by omega)]
    ring
  rw [normU_eq_pow hσq, ← pow_mul, ← hcard, pow_card_eq_one]

end Units

local notation "𝕩" => xPar (rootOperatorFamily d4)

theorem torusElement_conj_xPar (i : Fin d4.rank) (t : Kˣ) {α : Fin d4.rank → ℤ}
    (hα : IsRoot d4 α) (c : K) :
    torusElement d4 K i t * 𝕩 α c * (torusElement d4 K i t)⁻¹ =
      𝕩 α (((t ^ pr i α : Kˣ) : K) * c) := by
  rw [xPar_of_isRoot hα, xPar_of_isRoot hα]
  exact (rootOperatorFamily d4).torusElement_mul_eltElement_mul_inv i t ⟨α, hα⟩ c

@[expose] def torE (σ : K →+* K) (s t : Kˣ) : adjointGroup d4 K :=
  torusElement d4 K (nd 2) s * hShortHom σ t

theorem torE_conj_xPar (σ : K →+* K) (s t : Kˣ) {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α)
    (c : K) : torE σ s t * 𝕩 α c * (torE σ s t)⁻¹ = 𝕩 α ((chi σ s t α : K) * c) := by
  have e : ∀ a b d f x : adjointGroup d4 K, a * (b * d * f) * x * (a * (b * d * f))⁻¹ =
      a * (b * (d * (f * x * f⁻¹) * d⁻¹) * b⁻¹) * a⁻¹ := fun _ _ _ _ _ => by group
  rw [torE, hShortHom_apply, e, torusElement_conj_xPar _ _ hα, torusElement_conj_xPar _ _ hα,
    torusElement_conj_xPar _ _ hα, torusElement_conj_xPar _ _ hα]
  congr 1
  simp only [chi, Units.val_mul]
  ring

theorem torE_commute (σ : K →+* K) (s t s' t' : Kˣ) : Commute (torE σ s t) (torE σ s' t') := by
  have h4 : ∀ g : adjointGroup d4 K, (∀ i v, Commute (torusElement d4 K i v) g) →
      ∀ s t, Commute (torE σ s t) g := fun g hg s t => by
    rw [torE, hShortHom_apply]
    exact (hg _ _).mul_left (((hg _ _).mul_left (hg _ _)).mul_left (hg _ _))
  exact h4 _ (fun i v => (h4 _ (fun j w => torusElement_commute j i w v) s' t').symm) s t

variable {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem torE_conj_xOrbit {s : Kˣ} (hs : σ s = s) (t : Kˣ) {α : Fin d4.rank → ℤ}
    (hα : IsRoot d4 α) (c : K) :
    torE σ s t * xOrbit σ α c * (torE σ s t)⁻¹ = xOrbit σ α ((chi σ s t α : K) * c) := by
  have h1 := isRoot_rho hα
  have h2 := isRoot_rho h1
  have e : ∀ g a b d : adjointGroup d4 K, g * (a * b * d) * g⁻¹ =
      (g * a * g⁻¹) * (g * b * g⁻¹) * (g * d * g⁻¹) := fun _ _ _ _ => by group
  have r1 : (chi σ s t (rho α) : K) = σ (chi σ s t α) := by
    rw [← chi_rho hσ hs t α]
    rfl
  have r2 : (chi σ s t (rho (rho α)) : K) = σ (σ (chi σ s t α)) := by
    rw [← chi_rho hσ hs t (rho α), ← chi_rho hσ hs t α]
    rfl
  rw [xOrbit, xOrbit, e, torE_conj_xPar σ s t hα, torE_conj_xPar σ s t h1,
    torE_conj_xPar σ s t h2, r1, r2]
  simp only [map_mul]
  ring_nf

omit hσ in
theorem torusElement_mem_hHatE (s : fixedUnits σ) :
    torusElement d4 K (nd 2) (s : Kˣ) ∈ hHatE σ (ng 0) := by
  show _ ∈ (hLongHom σ).range
  exact ⟨s, rfl⟩

omit hσ in
theorem hShortHom_mem_hHatE (t : Kˣ) : hShortHom σ t ∈ hHatE σ (ng 1) := by
  show _ ∈ (hShortHom σ).range
  exact ⟨t, rfl⟩

@[expose] def tor (s : fixedUnits σ) (t : Kˣ) : twistedGroup σ :=
  ⟨torE σ s t, mul_mem (hHatE_le_twistedGroup hσ (ng 0) (torusElement_mem_hHatE s))
    (hHatE_le_twistedGroup hσ (ng 1) (hShortHom_mem_hHatE t))⟩

theorem tor_val (s : fixedUnits σ) (t : Kˣ) : (tor hσ s t : adjointGroup d4 K) = torE σ s t :=
  rfl

theorem tor_commute (s s' : fixedUnits σ) (t t' : Kˣ) :
    tor hσ s t * tor hσ s' t' = tor hσ s' t' * tor hσ s t :=
  Subtype.ext (torE_commute σ s t s' t').eq

@[expose] def xS {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α) (c : K) :
    twistedGroup σ :=
  ⟨xOrbit σ α c, twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj hα)
    (xOrbit_mem hσ hα hne c)⟩

@[expose] def xL {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hfix : rho α = α)
    (c : fixedField σ) : twistedGroup σ :=
  ⟨𝕩 α (c : K), twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj hα)
    (xPar_mem_of_fixed hσ hα hfix c.2)⟩

section Elements

variable {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α)

theorem xS_val (hne : rho α ≠ α) (c : K) : (xS hσ hα hne c : adjointGroup d4 K) = xOrbit σ α c :=
  rfl

theorem xL_val (hfix : rho α = α) (c : fixedField σ) :
    (xL hσ hα hfix c : adjointGroup d4 K) = 𝕩 α (c : K) :=
  rfl

theorem xS_add (hne : rho α ≠ α) (c d : K) : xS hσ hα hne (c + d) = xS hσ hα hne c * xS hσ hα hne d :=
  Subtype.ext (xOrbit_add σ hα hne c d)

theorem xL_add (hfix : rho α = α) (c d : fixedField σ) :
    xL hσ hα hfix (c + d) = xL hσ hα hfix c * xL hσ hα hfix d :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, xL_val, xL_val, xL_val, Subfield.coe_add, xPar_add])

theorem xS_eq_one (hne : rho α ≠ α) {c : K} (h : xS hσ hα hne c = 1) : c = 0 := by
  have h' : xOrbit σ α c = xOrbit σ α 0 := by
    rw [xOrbit_zero]
    exact congrArg Subtype.val h
  exact xOrbit_injective σ hα hne h'

theorem xL_eq_one (hfix : rho α = α) {c : fixedField σ} (h : xL hσ hα hfix c = 1) : c = 0 := by
  have h' : 𝕩 α (c : K) = 𝕩 α 0 := by
    rw [xPar_zero]
    exact congrArg Subtype.val h
  exact Subtype.ext (xPar_injective hα h')

theorem tor_conj_xS (hne : rho α ≠ α) (s : fixedUnits σ) (t : Kˣ) (c : K) :
    tor hσ s t * xS hσ hα hne c * (tor hσ s t)⁻¹ = xS hσ hα hne ((chi σ s t α : K) * c) :=
  Subtype.ext (torE_conj_xOrbit hσ ((mem_fixedUnits σ).1 s.2) t hα c)

theorem tor_conj_xL (hfix : rho α = α) (s : fixedUnits σ) (t : Kˣ) (c : fixedField σ) :
    tor hσ s t * xL hσ hα hfix c * (tor hσ s t)⁻¹ = xL hσ hα hfix (chiF hσ hfix s t * c) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, tor_val, xL_val, xL_val,
      torE_conj_xPar σ s t hα]
    rfl)

theorem mem_iff_xS (hne : rho α ≠ α) {β : Fin (Tag.rank .G2) → ℤ} (hp : proj α = β)
    (g : twistedGroup σ) : g ∈ twistedRootGroup σ β ↔ ∃ c, xS hσ hα hne c = g := by
  rw [mem_twistedRootGroup, mem_twistedRootSubgroupD4_iff_of_orbit hσ hα hp hne]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, Subtype.ext hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, by rw [← hc]; rfl⟩⟩

theorem mem_iff_xL (hfix : rho α = α) {β : Fin (Tag.rank .G2) → ℤ} (hp : proj α = β)
    (g : twistedGroup σ) : g ∈ twistedRootGroup σ β ↔ ∃ c, xL hσ hα hfix c = g := by
  rw [mem_twistedRootGroup, mem_twistedRootSubgroupD4_iff_of_fixed hσ hα hp hfix]
  exact ⟨fun ⟨c, hc, hg⟩ => ⟨⟨c, hc⟩, Subtype.ext hg.symm⟩,
    fun ⟨c, hc⟩ => ⟨c, c.2, by rw [← hc]; rfl⟩⟩

end Elements

end CFSG.LieType.Steinberg.CentralExt.TrialityClosed

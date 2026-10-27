module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorus
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabTwo
import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.Timmesfeld.ClassicalOrders

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

omit [Finite K] [CharP K 2] in
private theorem normPlaneTorus_char_eq_one_iff {p : ℕ} [Fact p.Prime]
    {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    (a : Multiplicative (ZMod p)) : (χ a : K) = 1 ↔ a = 1 := by
  constructor
  · intro h
    exact hχ (by rw [map_one]; exact Units.ext h)
  · rintro rfl
    simp

omit [Finite K] [CharP K 2] in
private theorem normPlaneTorus_char_ne_one {p : ℕ} [Fact p.Prime]
    {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ) :
    (χ (Multiplicative.ofAdd 1) : K) ≠ 1 := by
  intro h
  have h1 : (Multiplicative.ofAdd (1 : ZMod p)) = 1 :=
    (normPlaneTorus_char_eq_one_iff hχ _).mp h
  have h2 : (1 : ZMod p) = 0 := by
    simpa using congrArg Multiplicative.toAdd h1
  exact one_ne_zero h2

private theorem normPlaneTorus_char_mul_sigma {p : ℕ} [Fact p.Prime] (hpq : p ∣ 2 ^ f + 1)
    {χ : Multiplicative (ZMod p) →* Kˣ} (a : Multiplicative (ZMod p)) :
    (χ a : K) * unitaryInvolution K 2 f (χ a : K) = 1 := by
  have h : (χ a) ^ (2 ^ f + 1) = 1 :=
    zmodHom_pow_eq_one_of_dvd hpq χ a
  have h' : ((χ a : K)) ^ (2 ^ f + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  rw [unitaryInvolution_apply, ← pow_succ', h']

private theorem normPlaneTorus_char_sigma_eq_inv {p : ℕ} [Fact p.Prime] (hpq : p ∣ 2 ^ f + 1)
    {χ : Multiplicative (ZMod p) →* Kˣ} (a : Multiplicative (ZMod p)) :
    unitaryInvolution K 2 f (χ a : K) = ((χ a : K))⁻¹ :=
  eq_inv_of_mul_eq_one_right (normPlaneTorus_char_mul_sigma hpq a)

private theorem normPlaneTorus_char_add_inv_mem_range (E : QuadExt F K (unitaryInvolution K 2 f))
    {p : ℕ} [Fact p.Prime] (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} :
    ∃ s : F, algebraMap F K s =
      (χ (Multiplicative.ofAdd 1) : K) + ((χ (Multiplicative.ofAdd 1) : K))⁻¹ := by
  refine E.exists_of_fix _ ?_
  rw [map_add, map_inv₀, normPlaneTorus_char_sigma_eq_inv hpq (Multiplicative.ofAdd 1),
    inv_inv, add_comm]

omit [Finite K] [CharP K 2] in
private theorem normPlaneTorus_char_sq {p : ℕ} [Fact p.Prime]
    {χ : Multiplicative (ZMod p) →* Kˣ} {s : F}
    (hs : algebraMap F K s =
      (χ (Multiplicative.ofAdd 1) : K) + ((χ (Multiplicative.ofAdd 1) : K))⁻¹) :
    (χ (Multiplicative.ofAdd 1) : K) * (χ (Multiplicative.ofAdd 1) : K) + 1 =
      algebraMap F K s * (χ (Multiplicative.ofAdd 1) : K) := by
  rw [hs, add_mul, inv_mul_cancel₀ (Units.ne_zero _)]


private theorem normPlaneTorus_coe_apply_inv {m : ℕ} (u : normOmega E m)
    (z : (F × F) × (Fin m → K)) : u.1 ((u⁻¹ : normOmega E m).1 z) = z := by
  have h : u.1 * ((u⁻¹ : normOmega E m)).1 =
      (1 : (((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))) := by
    rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
  calc u.1 (((u⁻¹ : normOmega E m)).1 z) = (u.1 * ((u⁻¹ : normOmega E m)).1) z :=
        (LinearEquiv.mul_apply _ _ _).symm
    _ = (1 : (((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))) z := by rw [h]
    _ = z := rfl

private theorem normPlaneTorus_conj_apply {m p : ℕ} (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    {χ : Multiplicative (ZMod p) →* Kˣ} {u : normOmega E m}
    {t t' : Fin m → Multiplicative (ZMod p)}
    (h : u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ t')
    (v : (F × F) × (Fin m → K)) :
    u.1 ((normPlaneTorus E hm hpq χ t : normOmega E m).1 v) =
      (normPlaneTorus E hm hpq χ t' : normOmega E m).1 (u.1 v) := by
  have hcoe : u.1 * (normPlaneTorus E hm hpq χ t : normOmega E m).1 * u.1⁻¹ =
      (normPlaneTorus E hm hpq χ t' : normOmega E m).1 := by
    rw [← h]
    simp
  have hmul : u.1 * (normPlaneTorus E hm hpq χ t : normOmega E m).1 =
      (normPlaneTorus E hm hpq χ t' : normOmega E m).1 * u.1 := by
    calc u.1 * (normPlaneTorus E hm hpq χ t : normOmega E m).1
        = u.1 * (normPlaneTorus E hm hpq χ t : normOmega E m).1 * u.1⁻¹ * u.1 := by
          group
      _ = (normPlaneTorus E hm hpq χ t' : normOmega E m).1 * u.1 := by rw [hcoe]
  calc u.1 ((normPlaneTorus E hm hpq χ t : normOmega E m).1 v)
      = (u.1 * (normPlaneTorus E hm hpq χ t : normOmega E m).1) v :=
        (LinearEquiv.mul_apply _ _ _).symm
    _ = ((normPlaneTorus E hm hpq χ t' : normOmega E m).1 * u.1) v := by rw [hmul]
    _ = (normPlaneTorus E hm hpq χ t' : normOmega E m).1 (u.1 v) :=
        LinearEquiv.mul_apply _ _ _

private theorem normPlaneTorus_sub_apply {m p : ℕ} (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    (χ : Multiplicative (ZMod p) →* Kˣ) (s : Fin m → Multiplicative (ZMod p))
    (v : (F × F) × (Fin m → K)) :
    (normPlaneTorus E hm hpq χ s : normOmega E m).1 v - v =
      ((0, 0), fun j => ((χ (s j) : K) - 1) * v.2 j) := by
  show ((v.1, fun j => (χ (s j) : K) * v.2 j) : (F × F) × (Fin m → K)) - v = _
  refine Prod.ext ?_ ?_
  · show ((v.1, fun j => (χ (s j) : K) * v.2 j) : (F × F) × (Fin m → K)).1 - v.1 =
      ((0, 0) : F × F)
    rw [sub_self]
    rfl
  · show ((v.1, fun j => (χ (s j) : K) * v.2 j) : (F × F) × (Fin m → K)).2 - v.2 =
      (fun j => ((χ (s j) : K) - 1) * v.2 j)
    funext j
    show (χ (s j) : K) * v.2 j - v.2 j = ((χ (s j) : K) - 1) * v.2 j
    rw [sub_mul, one_mul]

omit [Algebra F K] [Finite K] [CharP K 2] in
theorem normPlaneTorus_eq_single_of_coord {m : ℕ} {v : (F × F) × (Fin m → K)}
    {i : Fin m} (h1 : v.1 = 0) (h2 : ∀ j, j ≠ i → v.2 j = 0) :
    v = ((0, 0), Pi.single i (v.2 i)) := by
  refine Prod.ext ?_ ?_
  · show v.1 = ((0, 0) : F × F)
    rw [h1]
    rfl
  · show v.2 = Pi.single i (v.2 i)
    funext j
    by_cases hj : j = i
    · rw [hj]
      exact (Pi.single_eq_same (M := fun _ => K) i (v.2 i)).symm
    · rw [Pi.single_eq_of_ne (M := fun _ => K) hj]
      exact h2 j hj

private theorem normPlaneTorus_single_mem_range {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {s : Fin m → Multiplicative (ZMod p)} {i : Fin m} (hi : s i ≠ 1) (x : K) :
    ((0, 0), Pi.single i x) ∈ Set.range (fun v : (F × F) × (Fin m → K) =>
      (normPlaneTorus E hm hpq χ s : normOmega E m).1 v - v) := by
  have hne : (χ (s i) : K) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hi ((normPlaneTorus_char_eq_one_iff hχ _).mp h)
  refine ⟨((0, 0), Pi.single i (((χ (s i) : K) - 1)⁻¹ * x)), ?_⟩
  show (normPlaneTorus E hm hpq χ s : normOmega E m).1
      ((0, 0), Pi.single i (((χ (s i) : K) - 1)⁻¹ * x)) -
      ((0, 0), Pi.single i (((χ (s i) : K) - 1)⁻¹ * x)) = ((0, 0), Pi.single i x)
  rw [normPlaneTorus_sub_apply]
  refine Prod.ext rfl (funext fun l => ?_)
  by_cases hl : l = i
  · show ((χ (s l) : K) - 1) *
        Pi.single (M := fun _ => K) i (((χ (s i) : K) - 1)⁻¹ * x) l =
      Pi.single (M := fun _ => K) i x l
    rw [hl, Pi.single_eq_same (M := fun _ => K), Pi.single_eq_same (M := fun _ => K)]
    exact mul_inv_cancel_left₀ hne x
  · show ((χ (s l) : K) - 1) * Pi.single (M := fun _ => K) i (((χ (s i) : K) - 1)⁻¹ * x) l =
      Pi.single (M := fun _ => K) i x l
    rw [Pi.single_eq_of_ne (M := fun _ => K) hl, Pi.single_eq_of_ne (M := fun _ => K) hl,
      mul_zero]

theorem normPlaneTorus_image_coord_subset {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {a : normOmega E m}
    {s s' : Fin m → Multiplicative (ZMod p)}
    (h : a * normPlaneTorus E hm hpq χ s * a⁻¹ = normPlaneTorus E hm hpq χ s')
    {i : Fin m} (hi : s i ≠ 1) (x : K) :
    (a.1 ((0, 0), Pi.single i x)).1 = 0 ∧
      ∀ j, s' j = 1 → (a.1 ((0, 0), Pi.single i x)).2 j = 0 := by
  obtain ⟨w, hw⟩ := normPlaneTorus_single_mem_range (E := E) hm hpq hχ hi x
  have hw' : (normPlaneTorus E hm hpq χ s : normOmega E m).1 w - w = ((0, 0), Pi.single i x) := hw
  have hmap := LinearMap.map_sub a.1.toLinearMap
    ((normPlaneTorus E hm hpq χ s : normOmega E m).1 w) w
  have hstep : a.1 ((0, 0), Pi.single i x) =
      (normPlaneTorus E hm hpq χ s' : normOmega E m).1 (a.1 w) - a.1 w :=
    calc a.1 ((0, 0), Pi.single i x) = a.1 ((normPlaneTorus E hm hpq χ s : normOmega E m).1 w - w) := by
          rw [hw']
      _ = a.1 ((normPlaneTorus E hm hpq χ s : normOmega E m).1 w) - a.1 w := hmap
      _ = (normPlaneTorus E hm hpq χ s' : normOmega E m).1 (a.1 w) - a.1 w := by
          rw [normPlaneTorus_conj_apply (E := E) hm hpq h w]
  rw [hstep, normPlaneTorus_sub_apply]
  refine ⟨rfl, fun j hj => ?_⟩
  show ((χ (s' j) : K) - 1) * (a.1 w).2 j = 0
  rw [hj, map_one, Units.val_one, sub_self, zero_mul]


omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem normPlaneTorus_mk_add {m : ℕ} (z₁ z₂ : Fin m → K) :
    (((0, 0) : F × F), z₁ + z₂) = (((0, 0) : F × F), z₁) + (((0, 0) : F × F), z₂) := by
  refine Prod.ext ?_ ?_
  · show ((0, 0) : F × F) = ((0, 0) : F × F) + ((0, 0) : F × F)
    simp
  · rfl

omit [Algebra F K] [Finite K] [CharP K 2] in
private theorem normPlaneTorus_add_single {m : ℕ} {i : Fin m} (z₁ z₂ : K) :
    (((0, 0) : F × F), Pi.single (M := fun _ => K) i z₁) +
        (((0, 0) : F × F), Pi.single (M := fun _ => K) i z₂) =
      (((0, 0) : F × F), Pi.single (M := fun _ => K) i (z₁ + z₂)) := by
  refine Prod.ext ?_ ?_
  · show ((0, 0) : F × F) + ((0, 0) : F × F) = ((0, 0) : F × F)
    simp
  · show (fun l => Pi.single (M := fun _ => K) i z₁ l + Pi.single (M := fun _ => K) i z₂ l) =
      Pi.single (M := fun _ => K) i (z₁ + z₂)
    funext l
    by_cases hl : l = i
    · rw [hl, Pi.single_eq_same (M := fun _ => K), Pi.single_eq_same (M := fun _ => K),
        Pi.single_eq_same (M := fun _ => K)]
    · rw [Pi.single_eq_of_ne (M := fun _ => K) hl, Pi.single_eq_of_ne (M := fun _ => K) hl,
        Pi.single_eq_of_ne (M := fun _ => K) hl, add_zero]

private theorem normPlaneTorus_mulSingle_self_ne_one {m p : ℕ} [Fact p.Prime] (i : Fin m) :
    Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd (1 : ZMod p)) i ≠
      1 := by
  rw [Pi.mulSingle_eq_same]
  intro h
  have h1 : (1 : ZMod p) = 0 := by
    simpa using congrArg Multiplicative.toAdd h
  exact one_ne_zero h1

private theorem normPlaneTorus_inv_image_single {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m} {t' : Fin m → Multiplicative (ZMod p)} {i : Fin m}
    (h' : u⁻¹ * normPlaneTorus E hm hpq χ t' * (u⁻¹)⁻¹ =
      normPlaneTorus E hm hpq χ
        (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)))
    {j : Fin m} (hj : t' j ≠ 1) (y : K) :
    ∃ z : K, (u⁻¹ : normOmega E m).1
        (((0, 0) : F × F), Pi.single (M := fun _ => K) j y) =
      (((0, 0) : F × F), Pi.single (M := fun _ => K) i z) := by
  have hsub := normPlaneTorus_image_coord_subset (E := E) hm hpq hχ (a := u⁻¹) h' hj y
  have hzero : ∀ l, l ≠ i →
      ((u⁻¹ : normOmega E m).1 (((0, 0) : F × F), Pi.single (M := fun _ => K) j y)).2 l = 0 :=
    fun l hl => hsub.2 l (by
      rw [Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod p)) hl])
  exact ⟨_, normPlaneTorus_eq_single_of_coord (i := i) hsub.1 hzero⟩

private theorem normPlaneTorus_inv_image_add {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m} {t' : Fin m → Multiplicative (ZMod p)} {i : Fin m}
    (h' : u⁻¹ * normPlaneTorus E hm hpq χ t' * (u⁻¹)⁻¹ =
      normPlaneTorus E hm hpq χ
        (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)))
    {j₁ j₂ : Fin m} (hj₁ : t' j₁ ≠ 1) (hj₂ : t' j₂ ≠ 1) (y₁ y₂ : K) :
    ∃ z : K, (u⁻¹ : normOmega E m).1
        ((((0, 0) : F × F), Pi.single (M := fun _ => K) j₁ y₁) +
          (((0, 0) : F × F), Pi.single (M := fun _ => K) j₂ y₂)) =
      (((0, 0) : F × F), Pi.single (M := fun _ => K) i z) := by
  obtain ⟨z₁, hz₁⟩ := normPlaneTorus_inv_image_single (E := E) hm hpq hχ h' hj₁ y₁
  obtain ⟨z₂, hz₂⟩ := normPlaneTorus_inv_image_single (E := E) hm hpq hχ h' hj₂ y₂
  exact ⟨z₁ + z₂, by rw [LinearEquiv.map_add, hz₁, hz₂, normPlaneTorus_add_single]⟩

private theorem normPlaneTorus_support_unique {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m} {t' : Fin m → Multiplicative (ZMod p)} {i : Fin m}
    (h : u * normPlaneTorus E hm hpq χ
        (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)) * u⁻¹ =
      normPlaneTorus E hm hpq χ t') :
    ∀ j₁ j₂, t' j₁ ≠ 1 → t' j₂ ≠ 1 → j₁ = j₂ := by
  intro j₁ j₂ hj₁ hj₂
  by_contra hne
  have h' : u⁻¹ * normPlaneTorus E hm hpq χ t' * (u⁻¹)⁻¹ =
      normPlaneTorus E hm hpq χ
        (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)) := by
    rw [← h]
    group
  have hex : ∀ y₁ y₂ : K, ∃ z : K, (u⁻¹ : normOmega E m).1
      ((((0, 0) : F × F), Pi.single (M := fun _ => K) j₁ y₁) +
        (((0, 0) : F × F), Pi.single (M := fun _ => K) j₂ y₂)) =
      (((0, 0) : F × F), Pi.single (M := fun _ => K) i z) :=
    fun y₁ y₂ => normPlaneTorus_inv_image_add (E := E) hm hpq hχ h' hj₁ hj₂ y₁ y₂
  let Φ : K × K → K := fun y => Classical.choose (hex y.1 y.2)
  have hΦ : ∀ y : K × K, (u⁻¹ : normOmega E m).1
      ((((0, 0) : F × F), Pi.single (M := fun _ => K) j₁ y.1) +
        (((0, 0) : F × F), Pi.single (M := fun _ => K) j₂ y.2)) =
        (((0, 0) : F × F), Pi.single (M := fun _ => K) i (Φ y)) :=
    fun y => Classical.choose_spec (hex y.1 y.2)
  have hinj : Function.Injective Φ := by
    intro y y' hyy'
    have hvec : ((((0, 0) : F × F), Pi.single (M := fun _ => K) j₁ y.1) +
        (((0, 0) : F × F), Pi.single (M := fun _ => K) j₂ y.2)) =
        ((((0, 0) : F × F), Pi.single (M := fun _ => K) j₁ y'.1) +
        (((0, 0) : F × F), Pi.single (M := fun _ => K) j₂ y'.2)) := by
      refine (u⁻¹ : normOmega E m).1.injective ?_
      rw [hΦ, hΦ, hyy']
    have h1 := congrArg (fun v : (F × F) × (Fin m → K) => v.2 j₁) hvec
    have h2 := congrArg (fun v : (F × F) × (Fin m → K) => v.2 j₂) hvec
    have h1' : y.1 = y'.1 := by
      simpa [Pi.single_eq_same (M := fun _ => K),
        Pi.single_eq_of_ne (M := fun _ => K) hne, Pi.add_apply] using h1
    have h2' : y.2 = y'.2 := by
      simpa [Pi.single_eq_same (M := fun _ => K),
        Pi.single_eq_of_ne (M := fun _ => K) (Ne.symm hne), Pi.add_apply] using h2
    exact Prod.ext h1' h2'
  have hcard : Nat.card (K × K) ≤ Nat.card K := Nat.card_le_card_of_injective Φ hinj
  rw [Nat.card_prod] at hcard
  have hlt : Nat.card K < Nat.card K * Nat.card K :=
    Nat.lt_mul_self_iff.mpr Finite.one_lt_card
  exact absurd hcard (not_le.mpr hlt)

private theorem normPlaneTorus_support_nonempty {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m} {t' : Fin m → Multiplicative (ZMod p)} {i : Fin m}
    (h : u * normPlaneTorus E hm hpq χ
        (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)) * u⁻¹ =
      normPlaneTorus E hm hpq χ t') :
    ∃ j, t' j ≠ 1 := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  have ht' : t' = 1 := funext hc
  have hD : normPlaneTorus E hm hpq χ
      (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)) = 1 := by
    have h1 : u * normPlaneTorus E hm hpq χ
        (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)) *
        u⁻¹ = 1 := by
      rw [h, ht', map_one]
    calc normPlaneTorus E hm hpq χ
          (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1))
        = u⁻¹ * (u * normPlaneTorus E hm hpq χ
            (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)) *
            u⁻¹) * u := by
          group
      _ = 1 := by rw [h1]; group
  have hD1 : normPlaneTorus E hm hpq χ
      (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)) =
      normPlaneTorus E hm hpq χ (1 : Fin m → Multiplicative (ZMod p)) := by
    rw [hD, map_one]
  have hsingle : Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd (1 : ZMod p)) = 1 :=
    normPlaneTorus_injective E hm hpq hχ hD1
  have hcoord : Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd (1 : ZMod p)) i = 1 := by
    rw [congrFun hsingle i]
    rfl
  exact normPlaneTorus_mulSingle_self_ne_one (p := p) i hcoord


private theorem normPlaneTorus_exists_support_index {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m}
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφ : ∀ t, u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ (φ t)) :
    ∃ πf : Fin m → Fin m, ∀ i j, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) j ≠ 1 ↔ j = πf i := by
  classical
  have hgen : ∀ i, u * normPlaneTorus E hm hpq χ
      (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)) * u⁻¹ =
      normPlaneTorus E hm hpq χ
        (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1))) :=
    fun i => hφ _
  have hex : ∀ i, ∃ j, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) j ≠ 1 :=
    fun i => normPlaneTorus_support_nonempty (E := E) hm hpq hχ (hgen i)
  have huniq : ∀ i, ∀ j₁ j₂, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) j₁ ≠ 1 → φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
        (Multiplicative.ofAdd 1)) j₂ ≠ 1 → j₁ = j₂ :=
    fun i => normPlaneTorus_support_unique (E := E) hm hpq hχ (hgen i)
  refine ⟨fun i => Classical.choose (hex i), ?_⟩
  intro i j
  constructor
  · intro h
    exact huniq i j (Classical.choose (hex i)) h (Classical.choose_spec (hex i))
  · rintro rfl
    exact Classical.choose_spec (hex i)

private theorem normPlaneTorus_image_rev {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m}
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφ : ∀ t, u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ (φ t))
    {πf : Fin m → Fin m}
    (hπf : ∀ i j, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) j ≠ 1 ↔ j = πf i) (i : Fin m) (y : K) :
    ∃ x : K, u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i x) =
      (((0, 0) : F × F), Pi.single (M := fun _ => K) (πf i) y) := by
  have hne : φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) (πf i) ≠ 1 := (hπf i (πf i)).mpr rfl
  have h' : u⁻¹ * normPlaneTorus E hm hpq χ (φ (Pi.mulSingle
      (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1))) * (u⁻¹)⁻¹ =
      normPlaneTorus E hm hpq χ (Pi.mulSingle
        (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)) := by
    rw [← hφ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1))]
    group
  have hsub := normPlaneTorus_image_coord_subset (E := E) hm hpq hχ (a := u⁻¹) h'
    (i := πf i) hne y
  have hz : (u⁻¹ : normOmega E m).1
      (((0, 0) : F × F), Pi.single (M := fun _ => K) (πf i) y) =
      (((0, 0) : F × F), Pi.single (M := fun _ => K) i
        ((((u⁻¹ : normOmega E m).1 (((0, 0) : F × F),
          Pi.single (M := fun _ => K) (πf i) y)).2) i)) :=
    normPlaneTorus_eq_single_of_coord hsub.1 (fun l hl => hsub.2 l (by
      rw [Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod p)) hl]))
  exact ⟨_, by rw [← hz, normPlaneTorus_coe_apply_inv (E := E) u]⟩

private theorem normPlaneTorus_support_index_injective {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m}
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφ : ∀ t, u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ (φ t))
    {πf : Fin m → Fin m}
    (hπf : ∀ i j, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) j ≠ 1 ↔ j = πf i) :
    Function.Injective πf := by
  intro i i' heq
  by_contra hne
  obtain ⟨x, hx⟩ := normPlaneTorus_image_rev (E := E) hm hpq hχ hφ hπf i 1
  obtain ⟨x', hx'⟩ := normPlaneTorus_image_rev (E := E) hm hpq hχ hφ hπf i' 1
  rw [← heq] at hx'
  have hvec : (((0, 0) : F × F), Pi.single (M := fun _ => K) i x) =
      (((0, 0) : F × F), Pi.single (M := fun _ => K) i' x') := by
    refine u.1.injective ?_
    rw [hx, hx']
  have hcoord := congrArg (fun v : (F × F) × (Fin m → K) => v.2 i) hvec
  have hx0 : x = 0 := by
    simpa [Pi.single_eq_same (M := fun _ => K),
      Pi.single_eq_of_ne (M := fun _ => K) hne] using hcoord
  have hzero : (((0, 0) : F × F), Pi.single (M := fun _ => K) (πf i) (1 : K)) = 0 := by
    have hx1 : u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i (0 : K)) =
        (((0, 0) : F × F), Pi.single (M := fun _ => K) (πf i) (1 : K)) := by
      rw [← hx0]
      exact hx
    rw [← hx1]
    have hzero' : (((0, 0) : F × F), Pi.single (M := fun _ => K) i (0 : K)) = 0 := by
      rw [Pi.single_zero]
      rfl
    rw [hzero', map_zero]
  have hcontra := congrArg (fun v : (F × F) × (Fin m → K) => v.2 (πf i)) hzero
  have hone : (1 : K) = 0 := by
    change Pi.single (M := fun _ => K) (πf i) (1 : K) (πf i) = 0 at hcontra
    rw [Pi.single_eq_same (M := fun _ => K)] at hcontra
    exact hcontra
  exact one_ne_zero hone

private theorem normPlaneTorus_exists_coord_perm {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m}
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφ : ∀ t, u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ (φ t)) :
    ∃ π : Equiv.Perm (Fin m), ∀ i j,
      φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)) j ≠ 1 ↔
        j = π i := by
  obtain ⟨πf, hπf⟩ := normPlaneTorus_exists_support_index (E := E) hm hpq hχ hφ
  have hinj := normPlaneTorus_support_index_injective (E := E) hm hpq hχ hφ hπf
  exact ⟨Equiv.ofBijective πf (Finite.injective_iff_bijective.mp hinj), hπf⟩

private theorem normPlaneTorus_apply_pair {m p : ℕ} (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    (χ : Multiplicative (ZMod p) →* Kˣ) (s : Fin m → Multiplicative (ZMod p))
    (v : (F × F) × (Fin m → K)) :
    (normPlaneTorus E hm hpq χ s : normOmega E m).1 v =
      (v.1, fun j => (χ (s j) : K) * v.2 j) := rfl

private theorem normPlaneTorus_apply_piVec {m p : ℕ} (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1)
    (χ : Multiplicative (ZMod p) →* Kˣ) (s : Fin m → Multiplicative (ZMod p)) (j : Fin m)
    (y : K) :
    (normPlaneTorus E hm hpq χ s : normOmega E m).1
        (((0, 0) : F × F), Pi.single (M := fun _ => K) j y) =
      (((0, 0) : F × F), Pi.single (M := fun _ => K) j ((χ (s j) : K) * y)) := by
  rw [normPlaneTorus_apply_pair]
  refine Prod.ext rfl (funext fun l => ?_)
  show (χ (s l) : K) * Pi.single (M := fun _ => K) j y l =
    Pi.single (M := fun _ => K) j ((χ (s j) : K) * y) l
  by_cases hl : l = j
  · rw [hl, Pi.single_eq_same (M := fun _ => K), Pi.single_eq_same (M := fun _ => K)]
  · rw [Pi.single_eq_of_ne (M := fun _ => K) hl, Pi.single_eq_of_ne (M := fun _ => K) hl,
      mul_zero]

private theorem normPlaneTorus_mulSingle_ofAdd_pow {m p : ℕ} [Fact p.Prime] (i : Fin m) (a : ZMod p) :
    Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd a) =
      (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
        (Multiplicative.ofAdd (1 : ZMod p))) ^ a.val := by
  funext j
  rw [Pi.pow_apply]
  by_cases hj : j = i
  · rw [hj, Pi.mulSingle_eq_same (M := fun _ => Multiplicative (ZMod p)),
      Pi.mulSingle_eq_same (M := fun _ => Multiplicative (ZMod p)),
      ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  · rw [Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod p)) hj,
      Pi.mulSingle_eq_of_ne (M := fun _ => Multiplicative (ZMod p)) hj]
    exact (one_pow _).symm

private theorem normPlaneTorus_phi_prod {m p : ℕ} {ι : Type*} [DecidableEq ι]
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφmul : ∀ t s, φ (t * s) = φ t * φ s) (hφone : φ 1 = 1) (s : Finset ι)
    (f : ι → Fin m → Multiplicative (ZMod p)) :
    φ (s.prod f) = s.prod (fun i => φ (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, hφone]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, hφmul, ih]

private theorem normPlaneTorus_phi_pow {m p : ℕ}
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφmul : ∀ t s, φ (t * s) = φ t * φ s) (hφone : φ 1 = 1)
    (t : Fin m → Multiplicative (ZMod p)) (n : ℕ) : φ (t ^ n) = (φ t) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, hφone]
  | succ n ih => rw [pow_succ, pow_succ, hφmul, ih]

private theorem normPlaneTorus_phi_ofAdd {m p : ℕ} [Fact p.Prime]
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφmul : ∀ t s, φ (t * s) = φ t * φ s) (hφone : φ 1 = 1) (i : Fin m) (a : ZMod p) :
    φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd a)) =
      (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
        (Multiplicative.ofAdd (1 : ZMod p)))) ^ a.val := by
  rw [normPlaneTorus_mulSingle_ofAdd_pow, normPlaneTorus_phi_pow hφmul hφone]

private theorem normPlaneTorus_hfun_form {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m}
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφ : ∀ t, u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ (φ t))
    {π : Fin m → Fin m}
    (hπ : ∀ i j, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) j ≠ 1 ↔ j = π i) (i : Fin m) (x : K) :
    u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i x) =
      (((0, 0) : F × F), Pi.single (M := fun _ => K) (π i)
        ((u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i x)).2 (π i))) := by
  have hi := normPlaneTorus_mulSingle_self_ne_one (p := p) i
  have hsub := normPlaneTorus_image_coord_subset (E := E) hm hpq hχ (a := u) (hφ _) hi x
  exact normPlaneTorus_eq_single_of_coord hsub.1 (fun l hl => hsub.2 l (by
    by_contra hc
    exact hl ((hπ i l).mp hc)))

omit [Finite K] [CharP K 2] in
private theorem normPlaneTorus_piVec_smul {m : ℕ} (i : Fin m) (c : F) (x : K) :
    (((0, 0) : F × F), Pi.single (M := fun _ => K) i (algebraMap F K c * x)) =
      c • (((0, 0) : F × F), Pi.single (M := fun _ => K) i x) := by
  refine Prod.ext ?_ ?_
  · show ((0, 0) : F × F) = c • ((0, 0) : F × F)
    simp
  · show Pi.single (M := fun _ => K) i (algebraMap F K c * x) =
      (fun j => c • Pi.single (M := fun _ => K) i x j)
    funext j
    by_cases hj : j = i
    · rw [hj, Pi.single_eq_same (M := fun _ => K), Pi.single_eq_same (M := fun _ => K),
        Algebra.smul_def]
    · rw [Pi.single_eq_of_ne (M := fun _ => K) hj, Pi.single_eq_of_ne (M := fun _ => K) hj,
        smul_zero]

private theorem normPlaneTorus_hfun_add {m : ℕ} (u : normOmega E m) (i j : Fin m) (x y : K) :
    (u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i (x + y))).2 j =
      (u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i x)).2 j +
        (u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i y)).2 j := by
  have hsum : (((0, 0) : F × F), Pi.single (M := fun _ => K) i (x + y)) =
      (((0, 0) : F × F), Pi.single (M := fun _ => K) i x) +
        (((0, 0) : F × F), Pi.single (M := fun _ => K) i y) := by
    rw [normPlaneTorus_add_single]
  rw [hsum, LinearEquiv.map_add]
  rfl

private theorem normPlaneTorus_hfun_smul {m : ℕ} (u : normOmega E m) (i j : Fin m) (c : F) (x : K) :
    (u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i (algebraMap F K c * x))).2 j =
      algebraMap F K c *
        (u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i x)).2 j := by
  rw [normPlaneTorus_piVec_smul, LinearEquiv.map_smul]
  show c • (u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i x)).2 j =
    algebraMap F K c * (u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i x)).2 j
  rw [Algebra.smul_def]

private theorem normPlaneTorus_hfun_one_ne_zero {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m}
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφ : ∀ t, u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ (φ t))
    {π : Fin m → Fin m}
    (hπ : ∀ i j, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) j ≠ 1 ↔ j = π i) (i : Fin m) :
    (u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i (1 : K))).2 (π i) ≠ 0 := by
  intro h
  have hform := normPlaneTorus_hfun_form (E := E) hm hpq hχ hφ hπ i 1
  rw [h] at hform
  have h0 : u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i (1 : K)) = 0 := by
    rw [hform, Pi.single_zero]
    rfl
  have h1 : (((0, 0) : F × F), Pi.single (M := fun _ => K) i (1 : K)) = 0 :=
    u.1.injective (by rw [h0, map_zero])
  have h2 := congrArg (fun v : (F × F) × (Fin m → K) => v.2 i) h1
  simp only [Pi.single_eq_same (M := fun _ => K)] at h2
  exact one_ne_zero h2

private theorem normPlaneTorus_hfun_scale {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m}
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφ : ∀ t, u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ (φ t))
    {π : Fin m → Fin m}
    (hπ : ∀ i j, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) j ≠ 1 ↔ j = π i) (i : Fin m) (a : ZMod p) (x : K) :
    (u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i
        ((χ (Multiplicative.ofAdd a) : K) * x))).2 (π i) =
      (χ (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
        (Multiplicative.ofAdd a)) (π i)) : K) *
        (u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i x)).2 (π i) := by
  have hconj := normPlaneTorus_conj_apply (E := E) hm hpq
    (hφ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd a))) (((0, 0) : F × F), Pi.single (M := fun _ => K) i x)
  rw [normPlaneTorus_apply_piVec (E := E) hm hpq χ
      (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd a)) i x,
    normPlaneTorus_hfun_form (E := E) hm hpq hχ hφ hπ i x,
    normPlaneTorus_apply_piVec (E := E) hm hpq χ
      (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd a)))
      (π i) ((u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i x)).2 (π i))] at hconj
  simpa only [Pi.single_eq_same (M := fun _ => K),
    Pi.mulSingle_eq_same (M := fun _ => Multiplicative (ZMod p))] using
    congrArg (fun v : (F × F) × (Fin m → K) => v.2 (π i)) hconj

omit [Finite K] in
private theorem normPlaneTorus_quadratic_root {p : ℕ} [Fact p.Prime]
    {χ : Multiplicative (ZMod p) →* Kˣ} {s : F}
    (hsq : (χ (Multiplicative.ofAdd 1) : K) * (χ (Multiplicative.ofAdd 1) : K) + 1 =
      algebraMap F K s * (χ (Multiplicative.ofAdd 1) : K))
    (hs : algebraMap F K s =
      (χ (Multiplicative.ofAdd 1) : K) + ((χ (Multiplicative.ofAdd 1) : K))⁻¹)
    {g : K → K} {μ : K}
    (hadd : ∀ x y, g (x + y) = g x + g y)
    (hsmul : ∀ (c : F) (x : K), g (algebraMap F K c * x) = algebraMap F K c * g x)
    (hone : g 1 ≠ 0)
    (hscale : ∀ x, g ((χ (Multiplicative.ofAdd 1) : K) * x) = μ * g x) :
    μ = (χ (Multiplicative.ofAdd 1) : K) ∨ μ = ((χ (Multiplicative.ofAdd 1) : K))⁻¹ := by
  set lam : K := (χ (Multiplicative.ofAdd 1) : K) with hlam
  have hlam2 : lam * lam = algebraMap F K s * lam + 1 := by
    have h2 : lam * lam + (1 + 1) = algebraMap F K s * lam + 1 := by
      rw [← add_assoc, hsq]
    rwa [CharTwo.add_self_eq_zero (1 : K), add_zero] at h2
  have hg1 : ∀ x, g (lam * lam * x) = (μ * μ) * g x := by
    intro x
    rw [mul_assoc, hscale, hscale, mul_assoc]
  have hg2 : ∀ x, g (lam * lam * x) = (algebraMap F K s * μ + 1) * g x := by
    intro x
    rw [hlam2, add_mul, one_mul, hadd, mul_assoc, hsmul, hscale, ← mul_assoc, add_mul, one_mul]
  have hmu : μ * μ = algebraMap F K s * μ + 1 := by
    have h := (hg1 1).symm.trans (hg2 1)
    have h2 : (μ * μ - (algebraMap F K s * μ + 1)) * g 1 = 0 := by
      rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hone
  have hfac : (μ - lam) * (μ + lam - algebraMap F K s) = 0 := by
    linear_combination hmu - hlam2
  rcases mul_eq_zero.mp hfac with h3 | h3
  · left
    rw [sub_eq_zero.mp h3, hlam]
  · right
    have h4 : μ = algebraMap F K s - lam := by linear_combination h3
    rw [h4, hlam, hs]
    ring

private theorem normPlaneTorus_phi_sign {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m}
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφ : ∀ t, u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ (φ t))
    {π : Fin m → Fin m}
    (hπ : ∀ i j, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) j ≠ 1 ↔ j = π i) {s : F}
    (hs : algebraMap F K s =
      (χ (Multiplicative.ofAdd 1) : K) + ((χ (Multiplicative.ofAdd 1) : K))⁻¹)
    (hsq : (χ (Multiplicative.ofAdd 1) : K) * (χ (Multiplicative.ofAdd 1) : K) + 1 =
      algebraMap F K s * (χ (Multiplicative.ofAdd 1) : K))
    (i : Fin m) :
    Multiplicative.toAdd (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
        (Multiplicative.ofAdd 1)) (π i)) = 1 ∨
      Multiplicative.toAdd (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
        (Multiplicative.ofAdd 1)) (π i)) = -1 := by
  have hroot := normPlaneTorus_quadratic_root (s := s) hsq hs
    (g := fun x => (u.1 (((0, 0) : F × F), Pi.single (M := fun _ => K) i x)).2 (π i))
    (μ := (χ (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) (π i)) : K))
    (fun x y => normPlaneTorus_hfun_add (E := E) u i (π i) x y)
    (fun c x => normPlaneTorus_hfun_smul (E := E) u i (π i) c x)
    (normPlaneTorus_hfun_one_ne_zero (E := E) hm hpq hχ hφ hπ i)
    (fun x => normPlaneTorus_hfun_scale (E := E) hm hpq hχ hφ hπ i 1 x)
  rcases hroot with h | h
  · left
    have hu : χ (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
        (Multiplicative.ofAdd 1)) (π i)) = χ (Multiplicative.ofAdd (1 : ZMod p)) := Units.ext h
    rw [hχ hu]
    rfl
  · right
    have hu : χ (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
        (Multiplicative.ofAdd 1)) (π i)) = χ (Multiplicative.ofAdd (-1 : ZMod p)) := by
      apply Units.ext
      rw [h, ofAdd_neg, map_inv, Units.val_inv_eq_inv_val]
    rw [hχ hu]
    rfl

private theorem normPlaneTorus_phi_toAdd {m p : ℕ} [Fact p.Prime]
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφmul : ∀ t s, φ (t * s) = φ t * φ s) (hφone : φ 1 = 1)
    {π : Equiv.Perm (Fin m)}
    (hπ : ∀ i j, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
      (Multiplicative.ofAdd 1)) j ≠ 1 ↔ j = π i)
    (t : Fin m → Multiplicative (ZMod p)) (i : Fin m) :
    Multiplicative.toAdd (φ t (π i)) =
      Multiplicative.toAdd (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
        (Multiplicative.ofAdd 1)) (π i)) * Multiplicative.toAdd (t i) := by
  have hprod : φ t = ∏ j, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) j (t j)) := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle (M := fun _ => Multiplicative (ZMod p)) (f := t)]
    rw [normPlaneTorus_phi_prod hφmul hφone]
  have hgen : ∀ (k : Fin m) (b : ZMod p),
      φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) k (Multiplicative.ofAdd b)) (π i) =
        (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) k
          (Multiplicative.ofAdd 1)) (π i)) ^ b.val := by
    intro k b
    rw [normPlaneTorus_phi_ofAdd hφmul hφone, Pi.pow_apply]
  have hfac : ∀ j, φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) j (t j)) (π i) =
      if j = i then (φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) i
        (Multiplicative.ofAdd 1)) (π i)) ^ (Multiplicative.toAdd (t i)).val else 1 := by
    intro j
    by_cases hj : j = i
    · rw [hj, if_pos rfl,
        show t i = Multiplicative.ofAdd (Multiplicative.toAdd (t i)) from rfl, hgen]
      rfl
    · rw [if_neg hj, show t j = Multiplicative.ofAdd (Multiplicative.toAdd (t j)) from rfl, hgen]
      have hne : π i ≠ π j := fun h => hj (π.injective h).symm
      have h1 : φ (Pi.mulSingle (M := fun _ => Multiplicative (ZMod p)) j
          (Multiplicative.ofAdd 1)) (π i) = 1 := by
        by_contra hc
        exact hne ((hπ j (π i)).mp hc)
      rw [h1, one_pow]
  rw [hprod, Finset.prod_apply,
    Finset.prod_eq_single_of_mem i (Finset.mem_univ i)
      (fun j _ hji => by rw [hfac j, if_neg hji]),
    hfac i, if_pos rfl, toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]


private theorem normPlaneTorus_phi_mul {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m}
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφ : ∀ t, u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ (φ t))
    (t s : Fin m → Multiplicative (ZMod p)) : φ (t * s) = φ t * φ s := by
  refine normPlaneTorus_injective E hm hpq hχ ?_
  rw [← hφ (t * s), map_mul]
  have h1 : u * (normPlaneTorus E hm hpq χ t * normPlaneTorus E hm hpq χ s) * u⁻¹ =
      (u * normPlaneTorus E hm hpq χ t * u⁻¹) *
        (u * normPlaneTorus E hm hpq χ s * u⁻¹) := by
    group
  rw [h1, hφ t, hφ s, map_mul]

private theorem normPlaneTorus_phi_one {m p : ℕ} [Fact p.Prime] (hm : 2 ≤ m)
    (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ} (hχ : Function.Injective χ)
    {u : normOmega E m}
    {φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))}
    (hφ : ∀ t, u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ (φ t)) :
    φ 1 = 1 := by
  refine normPlaneTorus_injective E hm hpq hχ ?_
  rw [← hφ 1, map_one, mul_one, mul_inv_cancel]

theorem normPlaneTorus_exists_signedPerm_of_normalizes {m p : ℕ} [Fact p.Prime]
    (hm : 2 ≤ m) (hpq : p ∣ 2 ^ f + 1) {χ : Multiplicative (ZMod p) →* Kˣ}
    (hχ : Function.Injective χ) (u : normOmega E m)
    (hu : ∀ t, ∃ t', u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ t') :
    ∃ (π : Equiv.Perm (Fin m)) (ε : Fin m → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ t t', u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ t' →
        ∀ i, Multiplicative.toAdd (t' (π i)) = ε i * Multiplicative.toAdd (t i) := by
  classical
  let φ : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p)) :=
    fun t => Classical.choose (hu t)
  have hφ : ∀ t, u * normPlaneTorus E hm hpq χ t * u⁻¹ = normPlaneTorus E hm hpq χ (φ t) :=
    fun t => Classical.choose_spec (hu t)
  have hφmul := normPlaneTorus_phi_mul (E := E) hm hpq hχ hφ
  have hφone := normPlaneTorus_phi_one (E := E) hm hpq hχ hφ
  obtain ⟨π, hπ⟩ := normPlaneTorus_exists_coord_perm (E := E) hm hpq hχ hφ
  obtain ⟨s, hs⟩ := normPlaneTorus_char_add_inv_mem_range (E := E) (χ := χ) hpq
  have hsq := normPlaneTorus_char_sq (χ := χ) (s := s) hs
  refine ⟨π, fun i => Multiplicative.toAdd (φ (Pi.mulSingle
    (M := fun _ => Multiplicative (ZMod p)) i (Multiplicative.ofAdd 1)) (π i)), ?_, ?_⟩
  · exact normPlaneTorus_phi_sign (E := E) hm hpq hχ hφ hπ hs hsq
  · intro t t' ht i
    have h1 : t' = φ t := by
      refine normPlaneTorus_injective E hm hpq hχ ?_
      rw [← ht, hφ t]
    rw [h1]
    exact normPlaneTorus_phi_toAdd hφmul hφone hπ t i

private theorem qTwo_swap_mem_orthogonalGroup
    (E : QuadExt F K (unitaryInvolution K 2 1)) :
    LinearEquiv.funCongrLeft F K (Equiv.swap (0 : Fin 2) (1 : Fin 2)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (Qn E 2) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [Qn_apply, Qn_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, Equiv.swap_apply_def]
  ring

private theorem qTwo_exists_axis_formula
    (E : QuadExt F K (unitaryInvolution K 2 1)) (hK : Nat.card K = 4)
    {h : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K)}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 2)) :
    ∃ (π : Equiv.Perm (Fin 2)) (s : Fin 2 → K) (bar : Fin 2 → Bool),
      ∀ x j, h x j = s j *
        (if bar j then unitaryInvolution K 2 1 (x (π j)) else x (π j)) := by
  classical
  rcases qTwo_isometry_permutes_axes E hK hh with hpres | hswapaxes
  · rcases qTwo_axis_preserving_form E hh hpres.1 hpres.2 with ⟨u, v, _, _, h0, h1⟩
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · refine ⟨Equiv.refl _, fun j => if j = 0 then u else v, fun _ => false, ?_⟩
      intro x j
      fin_cases j
      · exact h0 x
      · exact h1 x
    · refine ⟨Equiv.refl _, fun j => if j = 0 then u else v, fun j => j = 1, ?_⟩
      intro x j
      fin_cases j
      · exact h0 x
      · exact h1 x
    · refine ⟨Equiv.refl _, fun j => if j = 0 then u else v, fun j => j = 0, ?_⟩
      intro x j
      fin_cases j
      · exact h0 x
      · exact h1 x
    · refine ⟨Equiv.refl _, fun j => if j = 0 then u else v, fun _ => true, ?_⟩
      intro x j
      fin_cases j
      · exact h0 x
      · exact h1 x
  · let swapK : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K) :=
      LinearEquiv.funCongrLeft F K (Equiv.swap (0 : Fin 2) (1 : Fin 2))
    let h' : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K) := swapK.trans h
    have hswap : swapK ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 2) :=
      qTwo_swap_mem_orthogonalGroup E
    have hh' : h' ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 2) := by
      refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
      change Qn E 2 (h (swapK x)) = Qn E 2 x
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hh,
        TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hswap]
    have hswap_single0 (a : K) : swapK (Pi.single 0 a) = Pi.single 1 a := by
      ext j
      fin_cases j <;> simp [swapK, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft]
    have hswap_single1 (a : K) : swapK (Pi.single 1 a) = Pi.single 0 a := by
      ext j
      fin_cases j <;> simp [swapK, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft]
    have hpres' : (∀ a : K, h' (Pi.single 0 a) 1 = 0) ∧
        (∀ a : K, h' (Pi.single 1 a) 0 = 0) := by
      constructor
      · intro a
        change h (swapK (Pi.single 0 a)) 1 = 0
        rw [hswap_single0 a]
        exact hswapaxes.2 a
      · intro a
        change h (swapK (Pi.single 1 a)) 0 = 0
        rw [hswap_single1 a]
        exact hswapaxes.1 a
    have hswap_apply (x : Fin 2 → K) (j : Fin 2) :
        swapK x j = x (Equiv.swap (0 : Fin 2) (1 : Fin 2) j) := by
      simp [swapK, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft]
    have hswap_invol (x : Fin 2 → K) : swapK (swapK x) = x := by
      ext j
      simp [swapK, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft]
    have hx_eq : ∀ x : Fin 2 → K, h x = h' (swapK x) := fun x => by
      change h x = h (swapK (swapK x))
      rw [hswap_invol]
    rcases qTwo_axis_preserving_form E hh' hpres'.1 hpres'.2 with ⟨u, v, _, _, h0, h1⟩
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · refine ⟨Equiv.swap (0 : Fin 2) (1 : Fin 2), fun j => if j = 0 then u else v,
        fun _ => false, ?_⟩
      intro x j
      rw [hx_eq x]
      fin_cases j <;> simp [h0, h1, hswap_apply]
    · refine ⟨Equiv.swap (0 : Fin 2) (1 : Fin 2), fun j => if j = 0 then u else v,
        fun j => j = 1, ?_⟩
      intro x j
      rw [hx_eq x]
      fin_cases j <;> simp [h0, h1, hswap_apply]
    · refine ⟨Equiv.swap (0 : Fin 2) (1 : Fin 2), fun j => if j = 0 then u else v,
        fun j => j = 0, ?_⟩
      intro x j
      rw [hx_eq x]
      fin_cases j <;> simp [h0, h1, hswap_apply]
    · refine ⟨Equiv.swap (0 : Fin 2) (1 : Fin 2), fun j => if j = 0 then u else v,
        fun _ => true, ?_⟩
      intro x j
      rw [hx_eq x]
      fin_cases j <;> simp [h0, h1, hswap_apply]

private theorem qTwo_conj_diag_formula
    {h : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K)}
    {π : Equiv.Perm (Fin 2)} {s : Fin 2 → K} {bar : Fin 2 → Bool}
    (hformula : ∀ x j, h x j = s j *
      (if bar j then unitaryInvolution K 2 1 (x (π j)) else x (π j)))
    (χ : Multiplicative (ZMod 3) →* Kˣ) (u : Fin 2 → Multiplicative (ZMod 3)) :
    ∃ u' : Fin 2 → Multiplicative (ZMod 3),
      ∀ y, h (fun i => (χ (u i) : K) * y i) =
        fun j => (χ (u' j) : K) * h y j := by
  classical
  refine ⟨fun j => if bar j then (u (π j))⁻¹ else u (π j), ?_⟩
  intro y
  funext j
  rw [hformula (fun i => (χ (u i) : K) * y i) j, hformula y j]
  cases hbj : bar j
  · simp only [hbj, Bool.false_eq_true, ↓reduceIte]
    ring
  · have hbar := normPlaneTorus_char_sigma_eq_inv (f := 1) (p := 3) (χ := χ)
        (by decide : 3 ∣ 2 ^ 1 + 1) (u (π j))
    simp only [hbj, ↓reduceIte, map_mul, hbar]
    have hci : (χ ((u (π j))⁻¹) : K) = (χ (u (π j)) : K)⁻¹ := by
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [hci]
    ring

theorem normPlaneTorus_normalizes_of_fixes_anchor
    (E : QuadExt F K (unitaryInvolution K 2 1)) (hF : Nat.card F = 2)
    (χ : Multiplicative (ZMod 3) →* Kˣ)
    (g : normOmega E 2)
    (hfix : ∀ w : F × F, g.1 (w, (0 : Fin 2 → K)) = (w, 0)) :
    ∀ u : Fin 2 → Multiplicative (ZMod 3),
      ∃ u' : Fin 2 → Multiplicative (ZMod 3),
        g * normPlaneTorus E (by decide : 2 ≤ 2) (by decide : 3 ∣ 2 ^ 1 + 1) χ u * g⁻¹ =
          normPlaneTorus E (by decide : 2 ≤ 2) (by decide : 3 ∣ 2 ^ 1 + 1) χ u' := by
  classical
  haveI : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have hKcard : Nat.card K = Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), E.finrank_eq]
  have hK : Nat.card K = 4 := by
    rw [hKcard, hF]
    norm_num
  let V := (F × F) × (Fin 2 → K)
  have hgO : (g : V ≃ₗ[F] V) ∈
      TauCeti.QuadraticMap.orthogonalGroup (hypSum (Qn E 2)) := by
    have h := CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup
      (Q := normHypForm E 2) g.2
    simpa [V, normHypForm] using h
  have he : (g : V ≃ₗ[F] V) ((1, 0), (0 : Fin 2 → K)) = ((1, 0), 0) :=
    hfix (1, 0)
  have hf : (g : V ≃ₗ[F] V) ((0, 1), (0 : Fin 2 → K)) = ((0, 1), 0) :=
    hfix (0, 1)
  obtain ⟨h, hh, hg_eq⟩ := exists_hypExt_of_fix (K := F) (W := Fin 2 → K)
    (Q' := Qn E 2) hgO he hf
  obtain ⟨π, s, bar, hformula⟩ := qTwo_exists_axis_formula E hK hh
  intro u
  obtain ⟨u', hu'⟩ := qTwo_conj_diag_formula hformula χ u
  refine ⟨u', ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hg_inv : ((hypExt h : V ≃ₗ[F] V)⁻¹) = hypExt h⁻¹ := by
    change ((LinearEquiv.refl F (F × F)).prodCongr h).symm =
      (LinearEquiv.refl F (F × F)).prodCongr h.symm
    rw [LinearEquiv.prodCongr_symm]
    rfl
  rw [hg_eq, hg_inv]
  simp only [hypExt_apply, normPlaneTorus_apply]
  refine Prod.ext rfl (funext fun i => ?_)
  have := congrFun (hu' (h⁻¹ v.2)) i
  simpa [LinearEquiv.apply_symm_apply] using this


end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end

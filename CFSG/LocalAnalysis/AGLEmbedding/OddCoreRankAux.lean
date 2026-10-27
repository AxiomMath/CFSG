module

public import CFSG.LocalAnalysis.AGLEmbedding.HyperplaneFixedPoint

public section

namespace CFSG.AGLEmbedding

open Subgroup
open scoped commutatorElement

section ClassTwo

variable {D : Type*} [Group D]

theorem commutatorElement_mem_center_of_le (hc : commutator D ≤ center D) (x y : D) :
    ⁅x, y⁆ ∈ center D :=
  hc (by
    rw [_root_.commutator_def]
    exact commutator_mem_commutator (mem_top x) (mem_top y))

theorem commutatorElement_mul_left_of_le (hc : commutator D ≤ center D) (x x' y : D) :
    ⁅x * x', y⁆ = ⁅x', y⁆ * ⁅x, y⁆ := by
  have h := mem_center_iff.1 (commutatorElement_mem_center_of_le hc x' y) x
  simp only [commutatorElement_def] at h ⊢
  calc x * x' * y * (x * x')⁻¹ * y⁻¹ = x * (x' * y * x'⁻¹ * y⁻¹) * y * x⁻¹ * y⁻¹ := by group
    _ = x' * y * x'⁻¹ * y⁻¹ * x * y * x⁻¹ * y⁻¹ := by rw [h]
    _ = x' * y * x'⁻¹ * y⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group

theorem commutatorElement_mul_right_of_le (hc : commutator D ≤ center D) (x y y' : D) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have h := mem_center_iff.1 (commutatorElement_mem_center_of_le hc x y') y
  simp only [commutatorElement_def] at h ⊢
  calc x * (y * y') * x⁻¹ * (y * y')⁻¹ =
        x * y * x⁻¹ * y⁻¹ * (y * (x * y' * x⁻¹ * y'⁻¹)) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ * (x * y' * x⁻¹ * y'⁻¹ * y) * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ * (x * y' * x⁻¹ * y'⁻¹) := by group

theorem commutatorElement_eq_one_of_mem_center_right (x : D) {z : D} (hz : z ∈ center D) :
    ⁅x, z⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz x)

theorem commutatorElement_eq_one_of_mem_center_left {z : D} (hz : z ∈ center D) (y : D) :
    ⁅z, y⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz y).symm

@[expose] def quotientCenterAut : MulAut D →* MulAut (D ⧸ center D) where
  toFun φ := QuotientGroup.congr (center D) (center D) φ
    (characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext v
    induction v using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext v
    induction v using QuotientGroup.induction_on
    rfl

theorem quotientCenterAut_apply_mk (φ : MulAut D) (d : D) :
    quotientCenterAut φ (d : D ⧸ center D) = (φ d : D ⧸ center D) :=
  rfl

theorem pow_apply_eq_mul_pow {φ : MulAut D} {g z : D} (hg : φ g = g * z) (hz : φ z = z)
    (k : ℕ) : (φ ^ k) g = g * z ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hg, hz, mul_assoc, ← pow_succ']

theorem apply_eq_of_mk_apply_eq {s p : ℕ} (hcop : Nat.Coprime p s) (hD : ∀ d : D, d ^ s = 1)
    {φ : MulAut D} (hφ : φ ^ p = 1) (hZ : ∀ z ∈ center D, φ z = z) {d : D}
    (hd : (φ d : D ⧸ center D) = d) : φ d = d := by
  have hz : d⁻¹ * φ d ∈ center D := QuotientGroup.eq.mp hd.symm
  set z := d⁻¹ * φ d with hzdef
  have hg : φ d = d * z := by rw [hzdef, mul_inv_cancel_left]
  have hpow := pow_apply_eq_mul_pow hg (hZ z hz) p
  rw [hφ, MulAut.one_apply, left_eq_mul] at hpow
  have h1 : z ^ Nat.gcd p s = 1 := pow_gcd_eq_one.mpr ⟨hpow, hD z⟩
  rw [hcop.gcd_eq_one, pow_one] at h1
  rw [hg, h1, mul_one]

variable (hc : commutator D ≤ center D)

@[expose] def commRightHom (x : D) : D →* center D :=
  MonoidHom.mk' (fun y => ⟨⁅x, y⁆, commutatorElement_mem_center_of_le hc x y⟩) fun y y' =>
    Subtype.ext (commutatorElement_mul_right_of_le hc x y y')

@[expose] def commRight (x : D) : D ⧸ center D →* center D :=
  QuotientGroup.lift (center D) (commRightHom hc x) fun _ hz =>
    MonoidHom.mem_ker.mpr (Subtype.ext (commutatorElement_eq_one_of_mem_center_right x hz))

open scoped IsMulCommutative in
@[expose] def commPairing : D ⧸ center D →* D ⧸ center D →* center D :=
  QuotientGroup.lift (center D)
    (MonoidHom.mk' (commRight hc) fun x x' => by
      refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun y => Subtype.ext ?_)
      change ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆
      rw [commutatorElement_mul_left_of_le hc]
      exact (mem_center_iff.mp (commutatorElement_mem_center_of_le hc x y) _))
    fun z hz => MonoidHom.mem_ker.mpr (QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun y =>
      Subtype.ext (commutatorElement_eq_one_of_mem_center_left hz y)))

open scoped IsMulCommutative in
theorem commPairing_mk_mk (x y : D) :
    commPairing hc (x : D ⧸ center D) (y : D ⧸ center D) =
      ⟨⁅x, y⁆, commutatorElement_mem_center_of_le hc x y⟩ :=
  rfl

open scoped IsMulCommutative in
theorem commPairing_aut {φ : MulAut D} (hφ : ∀ z ∈ center D, φ z = z) (v w : D ⧸ center D) :
    commPairing hc (quotientCenterAut φ v) (quotientCenterAut φ w) = commPairing hc v w := by
  induction v using QuotientGroup.induction_on with
  | H x =>
    induction w using QuotientGroup.induction_on with
    | H y =>
      rw [quotientCenterAut_apply_mk, quotientCenterAut_apply_mk, commPairing_mk_mk,
        commPairing_mk_mk]
      refine Subtype.ext ?_
      change ⁅φ x, φ y⁆ = ⁅x, y⁆
      rw [← map_commutatorElement]
      exact hφ _ (commutatorElement_mem_center_of_le hc x y)

end ClassTwo

end CFSG.AGLEmbedding

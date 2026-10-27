module

public import CFSG.FeitThompson.Definitions.ExtraspecialFinitePGroup
public import CFSG.FeitThompson.Local.FrattiniQuotientPPowerElementaryAbelian
public import CFSG.FeitThompson.Local.ClassTwoProductPowers
public import CFSG.FeitThompson.Representations.SymplecticBasesAlternatingForms
public import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {p : ℕ} {P : Type u} [Group P]

theorem commutatorElement_mul_left_of_commutator_le_center
    (hcl : commutator P ≤ Subgroup.center P) (x y t : P) :
    ⁅x * y, t⁆ = ⁅x, t⁆ * ⁅y, t⁆ := by
  have hy : ⁅y, t⁆ ∈ Subgroup.center P :=
    commutatorElement_mem_center_of_commutator_le_center hcl y t
  have h' : x * ⁅y, t⁆ * x⁻¹ = ⁅y, t⁆ := by
    rw [Subgroup.mem_center_iff.mp hy x]; group
  rw [commutatorElement_mul_left_eq_conj_mul, h']
  exact (Subgroup.mem_center_iff.mp hy ⁅x, t⁆).symm

theorem commutatorElement_mul_right_of_commutator_le_center
    (hcl : commutator P ≤ Subgroup.center P) (x y t : P) :
    ⁅x, y * t⁆ = ⁅x, y⁆ * ⁅x, t⁆ := by
  have ht : ⁅x, t⁆ ∈ Subgroup.center P :=
    commutatorElement_mem_center_of_commutator_le_center hcl x t
  have h' : y * ⁅x, t⁆ * y⁻¹ = ⁅x, t⁆ := by
    rw [Subgroup.mem_center_iff.mp ht y]; group
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc ⁅x, y⁆ * y * ⁅x, t⁆ * y⁻¹ = ⁅x, y⁆ * (y * ⁅x, t⁆ * y⁻¹) := by group
    _ = ⁅x, y⁆ * ⁅x, t⁆ := by rw [h']

theorem commutatorElement_right_eq_one_of_mem_center {x c : P} (hc : c ∈ Subgroup.center P) :
    ⁅x, c⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.mp hc x)

theorem commutatorElement_left_eq_one_of_mem_center {x c : P} (hc : c ∈ Subgroup.center P) :
    ⁅c, x⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.mp hc x).symm

theorem commutatorElement_mul_center (hcl : commutator P ≤ Subgroup.center P) (a b : P) {u v : P}
    (hu : u ∈ Subgroup.center P) (hv : v ∈ Subgroup.center P) : ⁅a * u, b * v⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_of_commutator_le_center hcl,
    commutatorElement_mul_right_of_commutator_le_center hcl,
    commutatorElement_mul_right_of_commutator_le_center hcl,
    commutatorElement_right_eq_one_of_mem_center hv,
    commutatorElement_left_eq_one_of_mem_center hu,
    commutatorElement_left_eq_one_of_mem_center hu]
  simp

theorem commutatorElement_congr_of_mem_center (hcl : commutator P ≤ Subgroup.center P)
    {a b c d : P} (hac : a⁻¹ * c ∈ Subgroup.center P) (hbd : b⁻¹ * d ∈ Subgroup.center P) :
    ⁅a, b⁆ = ⁅c, d⁆ := by
  conv_rhs => rw [show c = a * (a⁻¹ * c) by group, show d = b * (b⁻¹ * d) by group]
  exact (commutatorElement_mul_center hcl a b hac hbd).symm

noncomputable def zmodLog (p : ℕ) (z g : P) : ZMod p :=
  Function.invFun (fun a : ZMod p => z ^ a.val) g

section zmodLog

variable [NeZero p] {z : P}

theorem pow_val_left_injective (hz : orderOf z = p) :
    Function.Injective (fun a : ZMod p => z ^ a.val) := by
  intro a b hab
  have h : a.val ≡ b.val [MOD orderOf z] := pow_eq_pow_iff_modEq.mp hab
  rw [hz, Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h
  exact ZMod.val_injective p h

theorem pow_val_add_of_orderOf_eq (hz : orderOf z = p) (a b : ZMod p) :
    z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  rw [← pow_add]
  refine pow_eq_pow_iff_modEq.2 ?_
  rw [hz, Nat.ModEq, ZMod.val_add]
  simp [Nat.add_mod]

theorem zmodLog_pow_val (hz : orderOf z = p) (a : ZMod p) : zmodLog p z (z ^ a.val) = a :=
  Function.leftInverse_invFun (pow_val_left_injective hz) a

theorem pow_val_zmodLog (hz : orderOf z = p) {g : P} (hg : g ∈ Subgroup.zpowers z) :
    z ^ (zmodLog p z g).val = g := by
  refine Function.invFun_eq (f := fun a : ZMod p => z ^ a.val) ?_
  obtain ⟨k, hk⟩ := hg
  refine ⟨(k : ZMod p), ?_⟩
  rw [← hk, ← zpow_natCast, zpow_eq_zpow_iff_modEq, hz]
  have h : ((((k : ZMod p).val : ℕ) : ℤ) : ZMod p) = ((k : ℤ) : ZMod p) := by
    push_cast; simp [ZMod.natCast_val]
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h

theorem zmodLog_eq_iff (hz : orderOf z = p) {g : P} (hg : g ∈ Subgroup.zpowers z) {a : ZMod p} :
    zmodLog p z g = a ↔ z ^ a.val = g := by
  refine ⟨fun hlog => hlog ▸ pow_val_zmodLog hz hg, fun hpow => ?_⟩
  rw [← hpow, zmodLog_pow_val hz]

theorem zmodLog_one (hz : orderOf z = p) : zmodLog p z (1 : P) = 0 := by
  simpa using zmodLog_pow_val hz (0 : ZMod p)

theorem zmodLog_mul (hz : orderOf z = p) {g g' : P} (hg : g ∈ Subgroup.zpowers z)
    (hg' : g' ∈ Subgroup.zpowers z) :
    zmodLog p z (g * g') = zmodLog p z g + zmodLog p z g' := by
  rw [zmodLog_eq_iff hz (mul_mem hg hg'), pow_val_add_of_orderOf_eq hz,
    pow_val_zmodLog hz hg, pow_val_zmodLog hz hg']

theorem zmodLog_eq_zero_iff (hz : orderOf z = p) {g : P} (hg : g ∈ Subgroup.zpowers z) :
    zmodLog p z g = 0 ↔ g = 1 := by
  rw [zmodLog_eq_iff hz hg]; simp [eq_comm]

end zmodLog

section CommLog

variable [NeZero p] {z : P} (hcl : commutator P ≤ Subgroup.center P)
  (hz : Subgroup.zpowers z = Subgroup.center P) (hzo : orderOf z = p)
include hcl hz

theorem commutatorElement_mem_zpowers (x y : P) : (⁅x, y⁆ : P) ∈ Subgroup.zpowers z :=
  hz ▸ commutatorElement_mem_center_of_commutator_le_center hcl x y

include hzo

theorem zmodLog_commutatorElement_pow_left (x y : P) (n : ℕ) :
    zmodLog p z ⁅x ^ n, y⁆ = (n : ZMod p) * zmodLog p z ⁅x, y⁆ := by
  induction n with
  | zero =>
      simp [commutatorElement_left_eq_one_of_mem_center (Subgroup.one_mem (Subgroup.center P)),
        zmodLog_one (p := p) hzo]
  | succ k ih =>
      rw [pow_succ, commutatorElement_mul_left_of_commutator_le_center hcl,
        zmodLog_mul hzo (commutatorElement_mem_zpowers hcl hz (x ^ k) y)
          (commutatorElement_mem_zpowers hcl hz x y), ih]
      push_cast
      ring

theorem zmodLog_commutatorElement_pow_right (x y : P) (n : ℕ) :
    zmodLog p z ⁅x, y ^ n⁆ = (n : ZMod p) * zmodLog p z ⁅x, y⁆ := by
  induction n with
  | zero =>
      simp [commutatorElement_right_eq_one_of_mem_center (Subgroup.one_mem (Subgroup.center P)),
        zmodLog_one (p := p) hzo]
  | succ k ih =>
      rw [pow_succ, commutatorElement_mul_right_of_commutator_le_center hcl,
        zmodLog_mul hzo (commutatorElement_mem_zpowers hcl hz x (y ^ k))
          (commutatorElement_mem_zpowers hcl hz x y), ih]
      push_cast
      ring

end CommLog

namespace IsExtraspecial

@[instance_reducible]
def commGroupQuotientCenter (h : IsExtraspecial p P) : CommGroup (P ⧸ Subgroup.center P) where
  mul_comm := isMulCommutative_iff.mp h.isMulCommutative_quotient_center

def QuotientCenter (_h : IsExtraspecial p P) : Type u := Additive (P ⧸ Subgroup.center P)

instance (h : IsExtraspecial p P) : AddCommGroup h.QuotientCenter :=
  letI := h.commGroupQuotientCenter
  inferInstanceAs (AddCommGroup (Additive (P ⧸ Subgroup.center P)))

instance (h : IsExtraspecial p P) : Finite h.QuotientCenter :=
  haveI := h.finite
  inferInstanceAs (Finite (Additive (P ⧸ Subgroup.center P)))

def proj (h : IsExtraspecial p P) (x : P) : h.QuotientCenter :=
  Additive.ofMul (QuotientGroup.mk x : P ⧸ Subgroup.center P)

theorem proj_mul (h : IsExtraspecial p P) (x y : P) :
    h.proj (x * y) = h.proj x + h.proj y := (rfl)

theorem proj_one (h : IsExtraspecial p P) : h.proj 1 = 0 := (rfl)

theorem proj_surjective (h : IsExtraspecial p P) : Function.Surjective h.proj := fun v => by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  refine ⟨x, ?_⟩
  change Additive.ofMul (QuotientGroup.mk x : P ⧸ Subgroup.center P) = v
  rw [hx]; rfl

theorem proj_eq_proj_iff (h : IsExtraspecial p P) {x y : P} :
    h.proj x = h.proj y ↔ x⁻¹ * y ∈ Subgroup.center P := by
  change Additive.ofMul (QuotientGroup.mk x : P ⧸ Subgroup.center P)
      = Additive.ofMul (QuotientGroup.mk y : P ⧸ Subgroup.center P) ↔ _
  rw [Equiv.apply_eq_iff_eq, QuotientGroup.eq]

theorem proj_eq_zero_iff (h : IsExtraspecial p P) {x : P} :
    h.proj x = 0 ↔ x ∈ Subgroup.center P := by
  rw [show (0 : h.QuotientCenter) = h.proj 1 from (h.proj_one).symm, h.proj_eq_proj_iff]
  simp

theorem proj_pow (h : IsExtraspecial p P) (x : P) (n : ℕ) : h.proj (x ^ n) = n • h.proj x := by
  induction n with
  | zero => simpa using h.proj_one
  | succ k ih => rw [pow_succ, proj_mul, ih, succ_nsmul]

theorem pow_mem_center (h : IsExtraspecial p P) (x : P) : x ^ p ∈ Subgroup.center P := by
  obtain ⟨n, hn⟩ := h.exists_card_eq_pow
  rw [h.center_eq_frattini]
  exact pow_mem_frattini h.prime hn x

instance (h : IsExtraspecial p P) : Module (ZMod p) h.QuotientCenter :=
  AddCommGroup.zmodModule (G := h.QuotientCenter) fun v => by
    obtain ⟨x, rfl⟩ := h.proj_surjective v
    rw [← h.proj_pow, h.proj_eq_zero_iff]
    exact h.pow_mem_center x

theorem proj_pow_val_eq_smul (h : IsExtraspecial p P) (a : ZMod p) (x : P) :
    h.proj (x ^ a.val) = a • h.proj x := by
  have := NeZero.of_pos h.prime.pos
  rw [h.proj_pow, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_val, ZMod.cast_id]

theorem nontrivial_quotientCenter (h : IsExtraspecial p P) : Nontrivial h.QuotientCenter := by
  have : Nontrivial (P ⧸ Subgroup.center P) := QuotientGroup.nontrivial_iff.2 h.center_ne_top
  exact inferInstanceAs (Nontrivial (Additive (P ⧸ Subgroup.center P)))

theorem commutator_le_center (h : IsExtraspecial p P) : commutator P ≤ Subgroup.center P :=
  h.center_eq_commutator.ge

theorem commutatorElement_mem_center (h : IsExtraspecial p P) (x y : P) :
    (⁅x, y⁆ : P) ∈ Subgroup.center P :=
  commutatorElement_mem_center_of_commutator_le_center h.commutator_le_center x y

theorem exists_zpowers_eq_center (h : IsExtraspecial p P) :
    ∃ z : P, Subgroup.zpowers z = Subgroup.center P ∧ orderOf z = p := by
  have := Fact.mk h.prime
  obtain ⟨w, hw⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).1 h.isCyclic_center
  exact ⟨w, hw, by rw [← Nat.card_zpowers, hw, h.card_center]⟩

noncomputable def commFormFun (h : IsExtraspecial p P) (z : P) (u v : h.QuotientCenter) :
    ZMod p :=
  zmodLog p z ⁅Function.surjInv h.proj_surjective u, Function.surjInv h.proj_surjective v⁆

theorem commFormFun_proj (h : IsExtraspecial p P) (z : P) (x y : P) :
    h.commFormFun z (h.proj x) (h.proj y) = zmodLog p z ⁅x, y⁆ := by
  refine congrArg (zmodLog p z) (commutatorElement_congr_of_mem_center
    h.commutator_le_center ?_ ?_) <;>
    rw [← h.proj_eq_proj_iff] <;>
    simp only [Function.surjInv_eq h.proj_surjective]

section Bilinear

variable {h : IsExtraspecial p P} {z : P} (hz : Subgroup.zpowers z = Subgroup.center P)
  (hzo : orderOf z = p)
include hz hzo

theorem commFormFun_add_left (u v w : h.QuotientCenter) :
    h.commFormFun z (u + v) w = h.commFormFun z u w + h.commFormFun z v w := by
  have := NeZero.of_pos h.prime.pos
  obtain ⟨x, rfl⟩ := h.proj_surjective u
  obtain ⟨y, rfl⟩ := h.proj_surjective v
  obtain ⟨t, rfl⟩ := h.proj_surjective w
  rw [← h.proj_mul, commFormFun_proj, commFormFun_proj, commFormFun_proj,
    commutatorElement_mul_left_of_commutator_le_center h.commutator_le_center,
    zmodLog_mul hzo (commutatorElement_mem_zpowers h.commutator_le_center hz x t)
      (commutatorElement_mem_zpowers h.commutator_le_center hz y t)]

theorem commFormFun_add_right (u v w : h.QuotientCenter) :
    h.commFormFun z u (v + w) = h.commFormFun z u v + h.commFormFun z u w := by
  have := NeZero.of_pos h.prime.pos
  obtain ⟨x, rfl⟩ := h.proj_surjective u
  obtain ⟨y, rfl⟩ := h.proj_surjective v
  obtain ⟨t, rfl⟩ := h.proj_surjective w
  rw [← h.proj_mul, commFormFun_proj, commFormFun_proj, commFormFun_proj,
    commutatorElement_mul_right_of_commutator_le_center h.commutator_le_center,
    zmodLog_mul hzo (commutatorElement_mem_zpowers h.commutator_le_center hz x y)
      (commutatorElement_mem_zpowers h.commutator_le_center hz x t)]

theorem commFormFun_smul_left (a : ZMod p) (u v : h.QuotientCenter) :
    h.commFormFun z (a • u) v = a • h.commFormFun z u v := by
  have := NeZero.of_pos h.prime.pos
  obtain ⟨x, rfl⟩ := h.proj_surjective u
  obtain ⟨y, rfl⟩ := h.proj_surjective v
  rw [← h.proj_pow_val_eq_smul, commFormFun_proj, commFormFun_proj, smul_eq_mul,
    zmodLog_commutatorElement_pow_left h.commutator_le_center hz hzo, ZMod.natCast_val,
    ZMod.cast_id]

theorem commFormFun_smul_right (a : ZMod p) (u v : h.QuotientCenter) :
    h.commFormFun z u (a • v) = a • h.commFormFun z u v := by
  have := NeZero.of_pos h.prime.pos
  obtain ⟨x, rfl⟩ := h.proj_surjective u
  obtain ⟨y, rfl⟩ := h.proj_surjective v
  rw [← h.proj_pow_val_eq_smul, commFormFun_proj, commFormFun_proj, smul_eq_mul,
    zmodLog_commutatorElement_pow_right h.commutator_le_center hz hzo, ZMod.natCast_val,
    ZMod.cast_id]

end Bilinear

noncomputable def commForm (h : IsExtraspecial p P) {z : P}
    (hz : Subgroup.zpowers z = Subgroup.center P) (hzo : orderOf z = p) :
    LinearMap.BilinForm (ZMod p) h.QuotientCenter :=
  haveI := Fact.mk h.prime
  LinearMap.mk₂ (ZMod p) (h.commFormFun z) (commFormFun_add_left hz hzo)
    (commFormFun_smul_left hz hzo) (commFormFun_add_right hz hzo)
    (commFormFun_smul_right hz hzo)

section Properties

variable {h : IsExtraspecial p P} {z : P} (hz : Subgroup.zpowers z = Subgroup.center P)
  (hzo : orderOf z = p)

@[simp]
theorem commForm_apply (u v : h.QuotientCenter) :
    h.commForm hz hzo u v = h.commFormFun z u v := (rfl)

include hz hzo

theorem commForm_apply_proj_eq_iff {x y : P} {a : ZMod p} :
    h.commForm hz hzo (h.proj x) (h.proj y) = a ↔ z ^ a.val = ⁅x, y⁆ := by
  have := NeZero.of_pos h.prime.pos
  rw [commForm_apply, commFormFun_proj,
    zmodLog_eq_iff hzo (commutatorElement_mem_zpowers h.commutator_le_center hz x y)]

theorem commForm_apply_source {x y : P} {a : ZMod p} :
    h.commForm hz hzo (h.proj x) (h.proj y) = a ↔ z ^ a.val = x⁻¹ * y⁻¹ * x * y := by
  rw [commForm_apply_proj_eq_iff hz hzo,
    inv_mul_inv_mul_mul_eq_commutatorElement_of_mem_center (h.commutatorElement_mem_center x y)]

theorem commForm_self (v : h.QuotientCenter) : h.commForm hz hzo v v = 0 := by
  have := NeZero.of_pos h.prime.pos
  obtain ⟨x, rfl⟩ := h.proj_surjective v
  rw [commForm_apply, commFormFun_proj, commutatorElement_self, zmodLog_one hzo]

theorem commForm_isAlt : (h.commForm hz hzo).IsAlt := commForm_self hz hzo

theorem commForm_eq_zero_of_forall (v : h.QuotientCenter)
    (hv : ∀ w, h.commForm hz hzo v w = 0) : v = 0 := by
  have := NeZero.of_pos h.prime.pos
  obtain ⟨x, rfl⟩ := h.proj_surjective v
  rw [h.proj_eq_zero_iff, Subgroup.mem_center_iff]
  intro y
  have h0 : zmodLog p z ⁅x, y⁆ = 0 := by
    have hw := hv (h.proj y)
    rwa [commForm_apply, commFormFun_proj] at hw
  have h1 : (⁅x, y⁆ : P) = 1 :=
    (zmodLog_eq_zero_iff hzo
      (commutatorElement_mem_zpowers h.commutator_le_center hz x y)).1 h0
  exact (commutatorElement_eq_one_iff_commute.1 h1).symm

theorem commForm_separatingLeft : (h.commForm hz hzo).SeparatingLeft :=
  commForm_eq_zero_of_forall hz hzo

end Properties

theorem exists_finrank_quotientCenter_eq (h : IsExtraspecial p P) :
    ∃ n : ℕ, 1 ≤ n ∧ Module.finrank (ZMod p) h.QuotientCenter = 2 * n := by
  have := Fact.mk h.prime
  have := h.nontrivial_quotientCenter
  have : Module.Finite (ZMod p) h.QuotientCenter := Module.Finite.of_finite
  have : FiniteDimensional (ZMod p) h.QuotientCenter := inferInstance
  obtain ⟨z, hz, hzo⟩ := h.exists_zpowers_eq_center
  obtain ⟨n, hn⟩ := even_finrank_of_isAlt_of_separatingLeft (h.commForm hz hzo)
    (commForm_isAlt hz hzo) (commForm_separatingLeft hz hzo)
  refine ⟨n, ?_, hn⟩
  have hpos : 0 < Module.finrank (ZMod p) h.QuotientCenter := Module.finrank_pos
  omega

theorem exists_card_eq_pow_two_mul_add_one (h : IsExtraspecial p P) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card P = p ^ (2 * n + 1) := by
  have := Fact.mk h.prime
  have := h.finite
  have : Module.Finite (ZMod p) h.QuotientCenter := Module.Finite.of_finite
  obtain ⟨n, hn1, hn⟩ := h.exists_finrank_quotientCenter_eq
  refine ⟨n, hn1, ?_⟩
  have hq : Nat.card h.QuotientCenter = p ^ (2 * n) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := h.QuotientCenter), Nat.card_zmod, hn]
  have hq' : Nat.card (P ⧸ Subgroup.center P) = p ^ (2 * n) := by
    rw [← hq]
    exact Nat.card_congr (Additive.ofMul (α := P ⧸ Subgroup.center P))
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P), hq', h.card_center,
    pow_succ]

end IsExtraspecial

end

end CFSG.FeitThompson

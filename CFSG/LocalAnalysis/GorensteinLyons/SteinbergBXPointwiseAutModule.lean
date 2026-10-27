module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXAltHom
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralLift
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCenterFour
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup Module
open scoped commutatorElement IsMulCommutative

variable {P : Type*} [Group P]

abbrev zIn (K : Subgroup P) (z : P) : Subgroup K := (zpowers z).subgroupOf K

abbrev Vsp (K : Subgroup P) (z : P) [CFSG.IsElementaryAbelian 2 K] : Type _ :=
  Additive (K ⧸ zIn K z)

theorem pow_two_eq_one_of_elementary (K : Subgroup P) [CFSG.IsElementaryAbelian 2 K] (k : K) :
    k ^ 2 = 1 :=
  Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p 2 K) k

@[reducible] noncomputable def quotF2Module (K : Subgroup P) [CFSG.IsElementaryAbelian 2 K]
    (N : Subgroup K) : Module (ZMod 2) (Additive (K ⧸ N)) :=
  AddCommGroup.zmodModule (n := 2) fun x => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have hx : x = Additive.ofMul (QuotientGroup.mk k) := by rw [hk]; rfl
    rw [hx, ← ofMul_pow, ← QuotientGroup.mk_pow, pow_two_eq_one_of_elementary K k]
    rfl

attribute [local instance] quotF2Module

@[expose] def autFixing (K : Subgroup P) : Subgroup (MulAut P) where
  carrier := {α | ∀ k ∈ K, α k = k}
  mul_mem' := fun {α β} hα hβ k hk => by rw [MulAut.mul_apply, hβ k hk, hα k hk]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {α} hα k hk => by
    conv_lhs => rw [← hα k hk]
    exact MulAut.inv_apply_self P α k

@[expose] def autStab (K : Subgroup P) : Subgroup (MulAut P) where
  carrier := {β | K.map β.toMonoidHom = K}
  mul_mem' := fun {α β} hα hβ => by
    change K.map (α * β).toMonoidHom = K
    have : (α * β).toMonoidHom = α.toMonoidHom.comp β.toMonoidHom := rfl
    rw [this, ← Subgroup.map_map, hβ, hα]
  one_mem' := by
    change K.map (1 : MulAut P).toMonoidHom = K
    exact Subgroup.map_id K
  inv_mem' := fun {α} hα => by
    change K.map α⁻¹.toMonoidHom = K
    have h1 : (K.map α.toMonoidHom).map α⁻¹.toMonoidHom = K := by
      rw [Subgroup.map_map]
      have : α⁻¹.toMonoidHom.comp α.toMonoidHom = MonoidHom.id P := by
        ext x
        exact MulAut.inv_apply_self P α x
      rw [this, Subgroup.map_id]
    rw [hα] at h1
    exact h1

@[expose] def innOf (K : Subgroup P) : Subgroup (MulAut P) :=
  K.map MulAut.conj

theorem mem_autStab_iff {K : Subgroup P} {β : MulAut P} :
    β ∈ autStab K ↔ K.map β.toMonoidHom = K :=
  Iff.rfl

structure PtwHyp (P : Type*) [Group P] (w : ℕ) (z : P) (K : Subgroup P) : Prop where
  card : Nat.card P = 2 ^ (1 + 2 * w)
  center_eq : center P = zpowers z
  commutator_eq : commutator P = zpowers z
  orderOf_z : orderOf z = 2
  card_K : Nat.card K = 2 ^ (w + 1)
  z_mem : z ∈ K

open Classical in
@[expose] noncomputable def zlog (z x : P) : ZMod 2 :=
  if x = z then 1 else 0

@[expose] noncomputable def pv (z r k : P) : ZMod 2 :=
  zlog z (r⁻¹ * k⁻¹ * r * k)

namespace PtwHyp

variable {w : ℕ} {z : P} {K : Subgroup P} (H : PtwHyp P w z K)
include H

theorem z_ne_one : z ≠ 1 := by
  intro h
  have := H.orderOf_z
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem z_mul_z : z * z = 1 := by
  rw [← pow_two, ← H.orderOf_z, pow_orderOf_eq_one]

theorem pair_of_mem {x : P} (hx : x ∈ zpowers z) : x = 1 ∨ x = z :=
  eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two H.orderOf_z hx

theorem z_mem_center : z ∈ center P := H.center_eq ▸ mem_zpowers z

theorem comm_pair (a b : P) : ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = z :=
  H.pair_of_mem (H.commutator_eq ▸ commutator_mem_commutator (mem_top a) (mem_top b))

theorem comm_center (a b : P) : ⁅a, b⁆ ∈ center P := by
  rcases H.comm_pair a b with h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact H.z_mem_center

theorem comm_mul_left (a a' b : P) : ⁅a * a', b⁆ = ⁅a, b⁆ * ⁅a', b⁆ := by
  rw [commutatorElement_mul_left_of_mem_center (H.comm_center a' b)]
  exact (mem_center_iff.mp (H.comm_center a' b) _).symm

theorem comm_mul_right (a b b' : P) : ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
  have h1 : ⁅a, b * b'⁆ = ⁅b * b', a⁆⁻¹ := by rw [commutatorElement_inv]
  rw [h1, H.comm_mul_left, mul_inv_rev, commutatorElement_inv, commutatorElement_inv]
  exact mem_center_iff.mp (H.comm_center a b) _

theorem comm_inv_left (a b : P) : ⁅a⁻¹, b⁆ = ⁅a, b⁆ := by
  have h := H.comm_mul_left a a⁻¹ b
  rw [mul_inv_cancel, commutatorElement_one_left] at h
  rcases H.comm_pair a b with h' | h'
  · rw [h', one_mul] at h
    rw [h']
    exact h.symm
  · rw [h'] at h ⊢
    have h2 : z * (z * ⁅a⁻¹, b⁆) = z := by rw [← h, mul_one]
    rw [← mul_assoc, H.z_mul_z, one_mul] at h2
    exact h2

theorem comm_inv_right (a b : P) : ⁅a, b⁻¹⁆ = ⁅a, b⁆ := by
  have h1 : ⁅a, b⁻¹⁆ = ⁅b⁻¹, a⁆⁻¹ := by rw [commutatorElement_inv]
  rw [h1, H.comm_inv_left, commutatorElement_inv]

theorem inv_comm_eq (r k : P) : r⁻¹ * k⁻¹ * r * k = ⁅r, k⁆ := by
  have : r⁻¹ * k⁻¹ * r * k = ⁅r⁻¹, k⁻¹⁆ := by
    rw [commutatorElement_def, inv_inv, inv_inv]
  rw [this, H.comm_inv_left, H.comm_inv_right]

theorem zlog_one : zlog z 1 = 0 := by
  rw [zlog, ite_eq_right (Ne.symm H.z_ne_one)]

omit [Group P] H in
theorem zlog_self : zlog z z = 1 := by
  rw [zlog, ite_eq_left rfl]

theorem eq_zpow_zlog {x : P} (hx : x = 1 ∨ x = z) : x = z ^ (zlog z x).val := by
  rcases hx with h | h <;> rw [h]
  · rw [H.zlog_one, ZMod.val_zero, pow_zero]
  · rw [zlog_self]; exact (pow_one z).symm

theorem zlog_mul {x y : P} (hx : x = 1 ∨ x = z) (hy : y = 1 ∨ y = z) :
    zlog z (x * y) = zlog z x + zlog z y := by
  rcases hx with h | h <;> rcases hy with h' | h' <;> rw [h, h']
  · rw [mul_one, H.zlog_one, add_zero]
  · rw [one_mul, H.zlog_one, zero_add]
  · rw [mul_one, H.zlog_one, add_zero]
  · rw [H.z_mul_z, H.zlog_one, zlog_self]; decide

theorem zlog_eq_zero_iff {x : P} (hx : x = 1 ∨ x = z) : zlog z x = 0 ↔ x = 1 := by
  rcases hx with h | h <;> rw [h]
  · simp [H.zlog_one]
  · rw [zlog_self]; simp [H.z_ne_one]

theorem pv_spec (r k : P) : r⁻¹ * k⁻¹ * r * k = z ^ (pv z r k).val := by
  rw [pv]
  exact H.eq_zpow_zlog (H.inv_comm_eq r k ▸ H.comm_pair r k)

theorem pv_eq_zlog (r k : P) : pv z r k = zlog z ⁅r, k⁆ := by
  rw [pv, H.inv_comm_eq]

theorem pv_mul_left (r s k : P) : pv z (r * s) k = pv z r k + pv z s k := by
  rw [H.pv_eq_zlog, H.pv_eq_zlog, H.pv_eq_zlog, H.comm_mul_left,
    H.zlog_mul (H.comm_pair r k) (H.comm_pair s k)]

theorem pv_mul_right (r k k' : P) : pv z r (k * k') = pv z r k + pv z r k' := by
  rw [H.pv_eq_zlog, H.pv_eq_zlog, H.pv_eq_zlog, H.comm_mul_right,
    H.zlog_mul (H.comm_pair r k) (H.comm_pair r k')]

theorem pv_eq_zero_iff (r k : P) : pv z r k = 0 ↔ r * k = k * r := by
  rw [H.pv_eq_zlog, H.zlog_eq_zero_iff (H.comm_pair r k), commutatorElement_eq_one_iff_mul_comm]

theorem pv_inv_left (r k : P) : pv z r⁻¹ k = pv z r k := by
  rw [H.pv_eq_zlog, H.pv_eq_zlog, H.comm_inv_left]

theorem pv_z_right (r : P) : pv z r z = 0 :=
  (H.pv_eq_zero_iff r z).mpr (mem_center_iff.mp H.z_mem_center r)

theorem sq_mem (r : P) : r ^ 2 ∈ zpowers z := by
  rw [← H.center_eq, mem_center_iff]
  intro s
  have h : ⁅r ^ 2, s⁆ = 1 := by
    rw [pow_two, H.comm_mul_left]
    rcases H.comm_pair r s with h | h <;> rw [h]
    · rw [one_mul]
    · exact H.z_mul_z
  exact ((commutatorElement_eq_one_iff_mul_comm.mp h).symm)

end PtwHyp

section Functionals

variable {w : ℕ} {z : P} {K : Subgroup P} [CFSG.IsElementaryAbelian 2 K]

theorem K_comm (k k' : K) : k * k' = k' * k :=
  (inferInstance : IsMulCommutative K).is_comm.comm k k'

@[expose] noncomputable def pvHom (H : PtwHyp P w z K) (r : P) : K →* Multiplicative (ZMod 2) where
  toFun k := Multiplicative.ofAdd (pv z r k)
  map_one' := by
    rw [OneMemClass.coe_one]
    exact congrArg Multiplicative.ofAdd ((H.pv_eq_zero_iff r 1).mpr (by rw [mul_one, one_mul]))
  map_mul' k k' := by
    rw [Subgroup.coe_mul, H.pv_mul_right]
    rfl

omit [CFSG.IsElementaryAbelian 2 K] in
theorem zIn_le_ker (H : PtwHyp P w z K) (r : P) : zIn K z ≤ (pvHom H r).ker := by
  intro k hk
  rw [MonoidHom.mem_ker]
  have hk' : (k : P) ∈ zpowers z := hk
  rcases H.pair_of_mem hk' with h | h
  · change Multiplicative.ofAdd (pv z r k) = 1
    rw [h, (H.pv_eq_zero_iff r 1).mpr (by rw [mul_one, one_mul])]
    rfl
  · change Multiplicative.ofAdd (pv z r k) = 1
    rw [h, H.pv_z_right]
    rfl

@[expose] noncomputable def fr (H : PtwHyp P w z K) (r : P) : Dual (ZMod 2) (Vsp K z) :=
  (MonoidHom.toAdditiveLeft
    (QuotientGroup.lift (zIn K z) (pvHom H r) (zIn_le_ker H r))).toZModLinearMap 2

theorem fr_apply (H : PtwHyp P w z K) (r : P) (k : K) :
    fr H r (Additive.ofMul (QuotientGroup.mk k)) = pv z r k :=
  rfl

theorem vsp_induction {p : Vsp K z → Prop} (h : ∀ k : K, p (Additive.ofMul (QuotientGroup.mk k)))
    (v : Vsp K z) : p v := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have : v = Additive.ofMul (QuotientGroup.mk k) := by rw [hk]; rfl
  rw [this]
  exact h k

theorem fr_mul (H : PtwHyp P w z K) (r s : P) : fr H (r * s) = fr H r + fr H s := by
  refine LinearMap.ext fun v => ?_
  induction v using vsp_induction with
  | h k => rw [LinearMap.add_apply, fr_apply, fr_apply, fr_apply, H.pv_mul_left]

theorem fr_one (H : PtwHyp P w z K) : fr H 1 = 0 := by
  have h := fr_mul H 1 1
  rw [mul_one] at h
  exact (add_eq_left.mp h.symm)

@[expose] noncomputable def frHom (H : PtwHyp P w z K) :
    P →* Multiplicative (Dual (ZMod 2) (Vsp K z)) where
  toFun r := Multiplicative.ofAdd (fr H r)
  map_one' := by rw [fr_one]; rfl
  map_mul' r s := by rw [fr_mul]; rfl

theorem frHom_apply (H : PtwHyp P w z K) (r : P) :
    frHom H r = Multiplicative.ofAdd (fr H r) :=
  rfl

theorem fr_eq_zero_iff (H : PtwHyp P w z K) (r : P) :
    fr H r = 0 ↔ ∀ k ∈ K, r * k = k * r := by
  constructor
  · intro h k hk
    have := LinearMap.congr_fun h (Additive.ofMul (QuotientGroup.mk ⟨k, hk⟩))
    rw [fr_apply, LinearMap.zero_apply] at this
    exact (H.pv_eq_zero_iff r k).mp this
  · intro h
    refine LinearMap.ext fun v => ?_
    induction v using vsp_induction with
    | h k =>
      rw [fr_apply, LinearMap.zero_apply]
      exact (H.pv_eq_zero_iff r k).mpr (h k k.2)

theorem eq_zero_of_fr (H : PtwHyp P w z K) (v : Vsp K z) (hv : ∀ r, fr H r v = 0) : v = 0 := by
  revert hv
  induction v using vsp_induction with
  | h k => ?_
  intro hk
  have hkc : (k : P) ∈ center P := mem_center_iff.mpr fun r =>
    ((H.pv_eq_zero_iff r k).mp (hk r))
  rw [H.center_eq] at hkc
  have : (QuotientGroup.mk k : K ⧸ zIn K z) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact hkc
  rw [this]
  rfl

end Functionals

section Perfect

variable {w : ℕ} {z : P} {K : Subgroup P} [CFSG.IsElementaryAbelian 2 K]

theorem add_self_eq_zero_zmod2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem fr_inv (H : PtwHyp P w z K) (r : P) : fr H r⁻¹ = fr H r := by
  refine LinearMap.ext fun v => ?_
  induction v using vsp_induction with
  | h k => rw [fr_apply, fr_apply, H.pv_inv_left]

omit [CFSG.IsElementaryAbelian 2 K] in
theorem zIn_card (H : PtwHyp P w z K) : Nat.card (zIn K z) = 2 := by
  have hle : zpowers z ≤ K := by rw [zpowers_le]; exact H.z_mem
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, H.orderOf_z]

theorem card_vsp (H : PtwHyp P w z K) : Nat.card (Vsp K z) = 2 ^ w := by
  have h := card_eq_card_quotient_mul_card_subgroup (zIn K z)
  rw [H.card_K, zIn_card H, pow_succ] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm

theorem finrank_vsp [Finite P] (H : PtwHyp P w z K) : finrank (ZMod 2) (Vsp K z) = w := by
  have h := FiniteField.pow_finrank_eq_natCard 2 (Vsp K z)
  rw [card_vsp H] at h
  exact Nat.pow_right_injective (le_refl 2) h

theorem card_dual_vsp [Finite P] (H : PtwHyp P w z K) :
    Nat.card (Dual (ZMod 2) (Vsp K z)) = 2 ^ w := by
  rw [← Nat.card_congr (finBasis (ZMod 2) (Vsp K z)).toDualEquiv.toEquiv, card_vsp H]

theorem fr_surjective [Finite P] (H : PtwHyp P w z K) : Function.Surjective (fr H) := by
  set S : Submodule (ZMod 2) (Dual (ZMod 2) (Vsp K z)) :=
    Submodule.span (ZMod 2) (Set.range (fr H)) with hSdef
  have hcoann : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    rw [Submodule.mem_bot]
    exact eq_zero_of_fr H v fun r => hv _ (Submodule.subset_span ⟨r, rfl⟩)
  have hS : S = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := S), hcoann,
      Submodule.dualAnnihilator_bot]
  intro f
  have hf : f ∈ S := hS ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨1, fr_one H⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact ⟨r * s, fr_mul H r s⟩
  | smul c x _ hx =>
    obtain ⟨r, rfl⟩ := hx
    fin_cases c
    · exact ⟨1, by rw [fr_one]; exact (zero_smul _ _).symm⟩
    · exact ⟨r, (one_smul _ _).symm⟩

theorem frHom_surjective [Finite P] (H : PtwHyp P w z K) : Function.Surjective (frHom H) :=
  fun f => by
    obtain ⟨r, hr⟩ := fr_surjective H (Multiplicative.toAdd f)
    exact ⟨r, by rw [frHom_apply, hr]; rfl⟩

theorem mem_frHom_ker (H : PtwHyp P w z K) (r : P) : r ∈ (frHom H).ker ↔ fr H r = 0 := by
  rw [MonoidHom.mem_ker, frHom_apply]
  exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => by rw [h]; rfl⟩

theorem frHom_ker [Finite P] (H : PtwHyp P w z K) : (frHom H).ker = K := by
  have hle : K ≤ (frHom H).ker := fun k hk => by
    rw [mem_frHom_ker, fr_eq_zero_iff]
    intro k' hk'
    exact congrArg Subtype.val (K_comm ⟨k, hk⟩ ⟨k', hk'⟩)
  have hidx : (frHom H).ker.index = 2 ^ w := by
    rw [index_ker, MonoidHom.range_eq_top.mpr (frHom_surjective H), card_top]
    exact card_dual_vsp H
  have hcard := (frHom H).ker.card_mul_index
  rw [hidx, H.card] at hcard
  have hker : Nat.card (frHom H).ker = 2 ^ (w + 1) := by
    have : 2 ^ (1 + 2 * w) = 2 ^ (w + 1) * 2 ^ w := by rw [← pow_add]; congr 1; ring
    rw [this] at hcard
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hcard
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hker, H.card_K])).symm

theorem exists_eq_fr_apply [Finite P] (H : PtwHyp P w z K) (l : P →* Multiplicative (ZMod 2))
    (hl : K ≤ l.ker) : ∃ v : Vsp K z, ∀ r, Multiplicative.toAdd (l r) = fr H r v := by
  set e := QuotientGroup.liftEquiv (frHom H).ker (frHom_surjective H) rfl with he
  set μ₀ : P ⧸ (frHom H).ker →* Multiplicative (ZMod 2) :=
    QuotientGroup.lift (frHom H).ker l (by rw [frHom_ker H]; exact hl) with hμ₀
  set μ : Dual (ZMod 2) (Vsp K z) →ₗ[ZMod 2] ZMod 2 :=
    (AddMonoidHom.toMultiplicative.symm (μ₀.comp e.symm.toMonoidHom)).toZModLinearMap 2 with hμ
  refine ⟨(evalEquiv (ZMod 2) (Vsp K z)).symm μ, fun r => ?_⟩
  rw [apply_evalEquiv_symm_apply]
  have h1 : e.symm (frHom H r) = (r : P ⧸ (frHom H).ker) := by
    rw [MulEquiv.symm_apply_eq, he, QuotientGroup.liftEquiv_coe]
  change Multiplicative.toAdd (l r) =
    Multiplicative.toAdd (μ₀ (e.symm (Multiplicative.ofAdd (fr H r))))
  rw [← frHom_apply, h1, hμ₀, QuotientGroup.lift_mk]

end Perfect

section TMaps

variable {w : ℕ} {z : P} {K : Subgroup P} [CFSG.IsElementaryAbelian 2 K]

omit [CFSG.IsElementaryAbelian 2 K] in
theorem aut_apply_z (H : PtwHyp P w z K) (β : MulAut P) : β z = z := by
  have h : β z ∈ center P := by
    rw [mem_center_iff]
    intro g
    have := mem_center_iff.mp H.z_mem_center (β⁻¹ g)
    have h2 := congrArg β this
    rwa [map_mul, map_mul, MulAut.apply_inv_self] at h2
  rw [H.center_eq] at h
  rcases H.pair_of_mem h with h1 | h1
  · exact absurd ((map_eq_one_iff β β.injective).mp h1) H.z_ne_one
  · exact h1

omit [CFSG.IsElementaryAbelian 2 K] in
theorem aut_apply_of_mem_zpowers (H : PtwHyp P w z K) (β : MulAut P) {x : P}
    (hx : x ∈ zpowers z) : β x = x := by
  rcases H.pair_of_mem hx with rfl | rfl
  · exact map_one β
  · exact aut_apply_z H β

omit [CFSG.IsElementaryAbelian 2 K] in
theorem pv_aut (H : PtwHyp P w z K) (β : MulAut P) (r k : P) : pv z (β r) (β k) = pv z r k := by
  rw [H.pv_eq_zlog, H.pv_eq_zlog, ← map_commutatorElement,
    aut_apply_of_mem_zpowers H β (H.commutator_eq ▸ commutator_mem_commutator (mem_top r)
      (mem_top k))]

theorem disp_mem [Finite P] (H : PtwHyp P w z K) {α : MulAut P} (hα : α ∈ autFixing K) (r : P) :
    α r * r⁻¹ ∈ K := by
  rw [← frHom_ker H, mem_frHom_ker, fr_mul, fr_inv]
  have h : fr H (α r) = fr H r := by
    refine LinearMap.ext fun v => ?_
    induction v using vsp_induction with
    | h k =>
      rw [fr_apply, fr_apply]
      conv_lhs => rw [← (hα k k.2 : α k = k)]
      exact pv_aut H α r k
  rw [h, add_self_eq_zero_zmod2]

@[expose] noncomputable def dispHom [Finite P] (H : PtwHyp P w z K) (α : autFixing K) :
    P →* Multiplicative (Vsp K z) where
  toFun r := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk ⟨_, disp_mem H α.2 r⟩))
  map_one' := by
    have : (⟨(α : MulAut P) 1 * 1⁻¹, disp_mem H α.2 1⟩ : K) = 1 :=
      Subtype.ext (show (α : MulAut P) 1 * 1⁻¹ = 1 by rw [map_one, inv_one, mul_one])
    rw [this, QuotientGroup.mk_one]
    rfl
  map_mul' r s := by
    rw [← ofAdd_add, ← ofMul_mul, ← QuotientGroup.mk_mul]
    congr 2
    rw [QuotientGroup.eq]
    show (((α : MulAut P) (r * s) * (r * s)⁻¹)⁻¹ *
      (((α : MulAut P) r * r⁻¹) * ((α : MulAut P) s * s⁻¹))) ∈ zpowers z
    set d := (α : MulAut P) s * s⁻¹ with hd
    have hx : ((α : MulAut P) (r * s) * (r * s)⁻¹)⁻¹ *
        (((α : MulAut P) r * r⁻¹) * ((α : MulAut P) s * s⁻¹)) = ⁅r, d⁻¹⁆ := by
      rw [map_mul, hd, commutatorElement_def]
      group
    rw [hx, ← H.commutator_eq]
    exact commutator_mem_commutator (mem_top r) (mem_top d⁻¹)

theorem dispHom_apply [Finite P] (H : PtwHyp P w z K) (α : autFixing K) (r : P) :
    dispHom H α r =
      Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk ⟨_, disp_mem H α.2 r⟩)) :=
  rfl

theorem le_dispHom_ker [Finite P] (H : PtwHyp P w z K) (α : autFixing K) :
    (frHom H).ker ≤ (dispHom H α).ker := by
  rw [frHom_ker H]
  intro k hk
  rw [MonoidHom.mem_ker, dispHom_apply]
  have : (⟨(α : MulAut P) k * k⁻¹, disp_mem H α.2 k⟩ : K) = 1 :=
    Subtype.ext (show (α : MulAut P) k * k⁻¹ = 1 by rw [α.2 k hk, mul_inv_cancel])
  rw [this, QuotientGroup.mk_one]
  rfl

@[expose] noncomputable def tLin [Finite P] (H : PtwHyp P w z K) (α : autFixing K) :
    Dual (ZMod 2) (Vsp K z) →ₗ[ZMod 2] Vsp K z :=
  AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.toMultiplicative.symm
    ((QuotientGroup.lift (frHom H).ker (dispHom H α) (le_dispHom_ker H α)).comp
      (QuotientGroup.liftEquiv (frHom H).ker (frHom_surjective H) rfl).symm.toMonoidHom))

theorem tLin_fr [Finite P] (H : PtwHyp P w z K) (α : autFixing K) (r : P) :
    tLin H α (fr H r) = Additive.ofMul (QuotientGroup.mk ⟨_, disp_mem H α.2 r⟩) := by
  have h1 : (QuotientGroup.liftEquiv (frHom H).ker (frHom_surjective H) rfl).symm
      (Multiplicative.ofAdd (fr H r)) = (r : P ⧸ (frHom H).ker) := by
    rw [MulEquiv.symm_apply_eq, QuotientGroup.liftEquiv_coe, frHom_apply]
  change Multiplicative.toAdd ((QuotientGroup.lift (frHom H).ker (dispHom H α)
    (le_dispHom_ker H α)) ((QuotientGroup.liftEquiv (frHom H).ker (frHom_surjective H) rfl).symm
      (Multiplicative.ofAdd (fr H r)))) = _
  rw [h1, QuotientGroup.lift_mk, dispHom_apply]
  rfl

theorem tLin_mem_altHom [Finite P] (H : PtwHyp P w z K) (α : autFixing K) :
    tLin H α ∈ altHom (ZMod 2) (Vsp K z) := by
  intro f
  obtain ⟨r, rfl⟩ := fr_surjective H f
  rw [tLin_fr, fr_apply]
  set d := (α : MulAut P) r * r⁻¹ with hd
  have hdK : d ∈ K := disp_mem H α.2 r
  have hsq : (α : MulAut P) (r ^ 2) = r ^ 2 := aut_apply_of_mem_zpowers H _ (H.sq_mem r)
  have hd2 : d * d = 1 := by
    have := pow_two_eq_one_of_elementary K ⟨d, hdK⟩
    rw [pow_two] at this
    exact congrArg Subtype.val this
  have hαr : (α : MulAut P) r = d * r := by rw [hd, inv_mul_cancel_right]
  have hcomm : ⁅r, d⁆ = 1 := by
    rw [map_pow, hαr] at hsq
    have hc := mem_center_iff.mp (H.comm_center r d)
    have h2 : (d * r) ^ 2 = ⁅r, d⁆ * r ^ 2 := by
      calc (d * r) ^ 2 = d * (r * d * r⁻¹) * r ^ 2 := by rw [pow_two, pow_two]; group
        _ = d * (⁅r, d⁆ * d) * r ^ 2 := by rw [commutatorElement_def]; group
        _ = ⁅r, d⁆ * (d * d) * r ^ 2 := by rw [← mul_assoc, hc d]; simp only [mul_assoc]
        _ = ⁅r, d⁆ * r ^ 2 := by rw [hd2, mul_one]
    rw [h2] at hsq
    exact mul_right_cancel (hsq.trans (one_mul _).symm)
  rw [H.pv_eq_zlog, hcomm, H.zlog_one]

end TMaps

section THom

variable {w : ℕ} {z : P} {K : Subgroup P} [CFSG.IsElementaryAbelian 2 K]

theorem ext_dual [Finite P] (H : PtwHyp P w z K)
    {L L' : Dual (ZMod 2) (Vsp K z) →ₗ[ZMod 2] Vsp K z} (h : ∀ r, L (fr H r) = L' (fr H r)) :
    L = L' :=
  LinearMap.ext fun f => by
    obtain ⟨r, rfl⟩ := fr_surjective H f
    exact h r

theorem vsp_mk_eq_zero_iff (k : K) :
    (Additive.ofMul (QuotientGroup.mk k : K ⧸ zIn K z) : Vsp K z) = 0 ↔ (k : P) ∈ zpowers z := by
  change (QuotientGroup.mk k : K ⧸ zIn K z) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  rfl

theorem disp_mul [Finite P] (H : PtwHyp P w z K) (α γ : autFixing K) (r : P) :
    ((α * γ : autFixing K) : MulAut P) r * r⁻¹ =
      ((α : MulAut P) r * r⁻¹) * ((γ : MulAut P) r * r⁻¹) := by
  have hγ : (γ : MulAut P) r * r⁻¹ ∈ K := disp_mem H γ.2 r
  have hfix : (α : MulAut P) ((γ : MulAut P) r * r⁻¹) = (γ : MulAut P) r * r⁻¹ := α.2 _ hγ
  have hcomm := K_comm ⟨_, disp_mem H α.2 r⟩ ⟨_, hγ⟩
  calc ((α * γ : autFixing K) : MulAut P) r * r⁻¹
      = (α : MulAut P) (((γ : MulAut P) r * r⁻¹) * r) * r⁻¹ := by
        rw [Subgroup.coe_mul, MulAut.mul_apply, inv_mul_cancel_right]
    _ = ((γ : MulAut P) r * r⁻¹) * ((α : MulAut P) r * r⁻¹) := by
        rw [map_mul, hfix, mul_assoc]
    _ = ((α : MulAut P) r * r⁻¹) * ((γ : MulAut P) r * r⁻¹) :=
        (congrArg Subtype.val hcomm).symm

@[expose] noncomputable def tHom [Finite P] (H : PtwHyp P w z K) :
    autFixing K →* Multiplicative (altHom (ZMod 2) (Vsp K z)) where
  toFun α := Multiplicative.ofAdd ⟨tLin H α, tLin_mem_altHom H α⟩
  map_one' := by
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    apply Subtype.ext
    refine ext_dual H fun r => ?_
    rw [tLin_fr, ZeroMemClass.coe_zero, LinearMap.zero_apply, vsp_mk_eq_zero_iff]
    change ((1 : MulAut P) r * r⁻¹) ∈ zpowers z
    rw [MulAut.one_apply, mul_inv_cancel]
    exact one_mem _
  map_mul' α γ := by
    rw [← ofAdd_add]
    congr 1
    apply Subtype.ext
    refine ext_dual H fun r => ?_
    rw [Submodule.coe_add, LinearMap.add_apply, tLin_fr, tLin_fr, tLin_fr, ← ofMul_mul,
      ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext (disp_mul H α γ r)

theorem tHom_apply [Finite P] (H : PtwHyp P w z K) (α : autFixing K) :
    ((Multiplicative.toAdd (tHom H α) : altHom (ZMod 2) (Vsp K z)) :
      Dual (ZMod 2) (Vsp K z) →ₗ[ZMod 2] Vsp K z) = tLin H α :=
  rfl

theorem innOf_le_autFixing : innOf K ≤ autFixing K := by
  rintro _ ⟨k, hk, rfl⟩ k' hk'
  rw [MulAut.conj_apply]
  have := congrArg Subtype.val (K_comm ⟨k, hk⟩ ⟨k', hk'⟩)
  change k * k' = k' * k at this
  rw [this, mul_inv_cancel_right]

theorem tHom_ker [Finite P] (H : PtwHyp P w z K) :
    (tHom H).ker = (innOf K).subgroupOf (autFixing K) := by
  ext α
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hα
    have h0 : tLin H α = 0 := by
      have := congrArg (fun x => ((Multiplicative.toAdd x : altHom (ZMod 2) (Vsp K z)) :
        Dual (ZMod 2) (Vsp K z) →ₗ[ZMod 2] Vsp K z)) hα
      exact this
    have hzr : ∀ r, (α : MulAut P) r * r⁻¹ ∈ zpowers z := by
      intro r
      have := LinearMap.congr_fun h0 (fr H r)
      rw [tLin_fr, LinearMap.zero_apply, vsp_mk_eq_zero_iff] at this
      exact this
    let l : P →* Multiplicative (ZMod 2) :=
      { toFun := fun r => Multiplicative.ofAdd (zlog z ((α : MulAut P) r * r⁻¹))
        map_one' := by
          rw [map_one, inv_one, mul_one, H.zlog_one]
          rfl
        map_mul' := fun r s => by
          rw [← ofAdd_add, ← H.zlog_mul (H.pair_of_mem (hzr r)) (H.pair_of_mem (hzr s))]
          congr 2
          have hc := mem_center_iff.mp (H.center_eq ▸ hzr s : (α : MulAut P) s * s⁻¹ ∈ center P)
          calc (α : MulAut P) (r * s) * (r * s)⁻¹
              = (α : MulAut P) r * ((α : MulAut P) s * s⁻¹) * r⁻¹ := by rw [map_mul]; group
            _ = (α : MulAut P) r * (r⁻¹ * ((α : MulAut P) s * s⁻¹)) := by
                rw [mul_assoc, hc r⁻¹]
            _ = (α : MulAut P) r * r⁻¹ * ((α : MulAut P) s * s⁻¹) := by group }
    have hl : K ≤ l.ker := by
      intro k hk
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (zlog z ((α : MulAut P) k * k⁻¹)) = 1
      rw [α.2 k hk, mul_inv_cancel, H.zlog_one]
      rfl
    obtain ⟨v, hv⟩ := exists_eq_fr_apply H l hl
    obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hv' : v = Additive.ofMul (QuotientGroup.mk k₀) := by rw [hk₀]; rfl
    refine ⟨(k₀ : P)⁻¹, inv_mem k₀.2, ?_⟩
    ext r
    have h1 := hv r
    rw [hv', fr_apply] at h1
    change zlog z ((α : MulAut P) r * r⁻¹) = pv z r k₀ at h1
    rw [H.pv_eq_zlog] at h1
    have h2 : (α : MulAut P) r * r⁻¹ = ⁅r, (k₀ : P)⁆ := by
      rcases H.pair_of_mem (hzr r) with h3 | h3 <;> rcases H.comm_pair r k₀ with h4 | h4
      · rw [h3, h4]
      · rw [h3, h4, H.zlog_one, PtwHyp.zlog_self] at h1; exact absurd h1 (by decide)
      · rw [h3, h4, H.zlog_one, PtwHyp.zlog_self] at h1; exact absurd h1 (by decide)
      · rw [h3, h4]
    have h3 : (α : MulAut P) r = ⁅r, (k₀ : P)⁆ * r := by rw [← h2, inv_mul_cancel_right]
    change MulAut.conj (k₀ : P)⁻¹ r = (α : MulAut P) r
    rw [MulAut.conj_apply, h3, inv_inv]
    have h5 : ⁅(k₀ : P)⁻¹, r⁆ = ⁅r, (k₀ : P)⁆ := by
      rw [H.comm_inv_left, ← commutatorElement_inv]
      rcases H.comm_pair r (k₀ : P) with h6 | h6
      · rw [h6, inv_one]
      · rw [h6]; exact (inv_eq_of_mul_eq_one_left H.z_mul_z)
    rw [← h5, commutatorElement_def, inv_inv]
    group
  · rintro ⟨k, hk, hα⟩
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    apply Subtype.ext
    refine ext_dual H fun r => ?_
    rw [tLin_fr, ZeroMemClass.coe_zero, LinearMap.zero_apply, vsp_mk_eq_zero_iff]
    change (α : MulAut P) r * r⁻¹ ∈ zpowers z
    have hαk : (α : MulAut P) = MulAut.conj k := hα.symm
    rw [hαk, MulAut.conj_apply, ← H.commutator_eq]
    have : k * r * k⁻¹ * r⁻¹ = ⁅k, r⁆ := (commutatorElement_def k r).symm
    rw [this]
    exact commutator_mem_commutator (mem_top k) (mem_top r)

theorem exists_quot_injective [Finite P] (H : PtwHyp P w z K) :
    ∃ _ : ((innOf K).subgroupOf (autFixing K)).Normal,
      ∃ φ : autFixing K ⧸ (innOf K).subgroupOf (autFixing K) →*
        Multiplicative (altHom (ZMod 2) (Vsp K z)),
        Function.Injective φ ∧ ∀ α, φ (QuotientGroup.mk α) = tHom H α := by
  have hN : ((innOf K).subgroupOf (autFixing K)).Normal := by
    rw [← tHom_ker H]
    infer_instance
  refine ⟨hN, QuotientGroup.lift _ (tHom H) (tHom_ker H).symm.le, ?_,
    fun _ => rfl⟩
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, tHom_ker H,
    QuotientGroup.map_mk'_self]

end THom

section Equivariance

variable {w : ℕ} {z : P} {K : Subgroup P} [CFSG.IsElementaryAbelian 2 K]

omit [CFSG.IsElementaryAbelian 2 K] in
theorem apply_mem_of_mem_autStab {β : MulAut P} (hβ : β ∈ autStab K) {k : P} (hk : k ∈ K) :
    β k ∈ K := by
  rw [← mem_autStab_iff.mp hβ]
  exact mem_map_of_mem _ hk

@[expose] noncomputable def restrictK {β : MulAut P} (hβ : β ∈ autStab K) : K →* K :=
  (β.toMonoidHom.comp K.subtype).codRestrict K fun k => apply_mem_of_mem_autStab hβ k.2

omit [CFSG.IsElementaryAbelian 2 K] in
theorem zIn_le_comap_restrictK (H : PtwHyp P w z K) {β : MulAut P} (hβ : β ∈ autStab K) :
    zIn K z ≤ (zIn K z).comap (restrictK hβ) := by
  intro k hk
  rw [mem_comap]
  have hk' : (k : P) ∈ zpowers z := hk
  change β k ∈ zpowers z
  rw [aut_apply_of_mem_zpowers H β hk']
  exact hk'

@[expose] noncomputable def hInd (H : PtwHyp P w z K) {β : MulAut P} (hβ : β ∈ autStab K) :
    Vsp K z →ₗ[ZMod 2] Vsp K z :=
  (MonoidHom.toAdditive (QuotientGroup.map (zIn K z) (zIn K z) (restrictK hβ)
    (zIn_le_comap_restrictK H hβ))).toZModLinearMap 2

theorem hInd_mk (H : PtwHyp P w z K) {β : MulAut P} (hβ : β ∈ autStab K) (k : K) :
    hInd H hβ (Additive.ofMul (QuotientGroup.mk k)) =
      Additive.ofMul (QuotientGroup.mk ⟨β k, apply_mem_of_mem_autStab hβ k.2⟩) :=
  rfl

omit [CFSG.IsElementaryAbelian 2 K] in
theorem conj_mem_autFixing {β : MulAut P} (hβ : β ∈ autStab K) {α : MulAut P}
    (hα : α ∈ autFixing K) : β * α * β⁻¹ ∈ autFixing K := by
  intro k hk
  have hk' : β⁻¹ k ∈ K := apply_mem_of_mem_autStab (inv_mem hβ) hk
  rw [MulAut.mul_apply, MulAut.mul_apply, hα _ hk', MulAut.apply_inv_self]

theorem dualMap_hInd_fr (H : PtwHyp P w z K) {β : MulAut P} (hβ : β ∈ autStab K) (r : P) :
    (hInd H hβ).dualMap (fr H r) = fr H (β⁻¹ r) := by
  refine LinearMap.ext fun v => ?_
  induction v using vsp_induction with
  | h k =>
    rw [LinearMap.dualMap_apply, hInd_mk, fr_apply, fr_apply]
    have := pv_aut H β⁻¹ r (β k)
    rw [MulAut.inv_apply_self] at this
    exact this.symm

theorem tLin_conj [Finite P] (H : PtwHyp P w z K) {β : MulAut P} (hβ : β ∈ autStab K)
    (α : autFixing K) :
    tLin H ⟨β * α * β⁻¹, conj_mem_autFixing hβ α.2⟩ =
      hInd H hβ ∘ₗ tLin H α ∘ₗ (hInd H hβ).dualMap := by
  refine ext_dual H fun r => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, dualMap_hInd_fr, tLin_fr, tLin_fr, hInd_mk]
  congr 2
  apply Subtype.ext
  change (β * α * β⁻¹) r * r⁻¹ = β ((α : MulAut P) (β⁻¹ r) * (β⁻¹ r)⁻¹)
  rw [map_mul, map_inv, MulAut.apply_inv_self, MulAut.mul_apply, MulAut.mul_apply]

theorem hInd_comp_mem_altHom (H : PtwHyp P w z K) {β : MulAut P} (hβ : β ∈ autStab K)
    {T : Dual (ZMod 2) (Vsp K z) →ₗ[ZMod 2] Vsp K z} (hT : T ∈ altHom (ZMod 2) (Vsp K z)) :
    hInd H hβ ∘ₗ T ∘ₗ (hInd H hβ).dualMap ∈ altHom (ZMod 2) (Vsp K z) := by
  intro f
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.dualMap_apply]
  exact hT _

end Equivariance

section HEquiv

variable {w : ℕ} {z : P} {K : Subgroup P} [CFSG.IsElementaryAbelian 2 K]

@[expose] noncomputable def hEquiv (H : PtwHyp P w z K) {β : MulAut P} (hβ : β ∈ autStab K) :
    Vsp K z ≃ₗ[ZMod 2] Vsp K z :=
  LinearEquiv.ofLinearMap (hInd H hβ) (hInd H (inv_mem hβ))
    (LinearMap.ext fun v => by
      induction v using vsp_induction with
      | h k =>
        rw [LinearMap.comp_apply, hInd_mk, hInd_mk, LinearMap.id_apply]
        congr 2
        exact Subtype.ext (MulAut.apply_inv_self P β k))
    (LinearMap.ext fun v => by
      induction v using vsp_induction with
      | h k =>
        rw [LinearMap.comp_apply, hInd_mk, hInd_mk, LinearMap.id_apply]
        congr 2
        exact Subtype.ext (MulAut.inv_apply_self P β k))

theorem hEquiv_toLinearMap (H : PtwHyp P w z K) {β : MulAut P} (hβ : β ∈ autStab K) :
    (hEquiv H hβ).toLinearMap = hInd H hβ :=
  rfl

end HEquiv


theorem class_two_maximal_elementary_pointwise_automorphism_module [Finite P] {w : ℕ}
    (_hw : 1 ≤ w) (hP : Nat.card P = 2 ^ (1 + 2 * w)) {z : P} (hZ : center P = zpowers z)
    (hP' : commutator P = zpowers z) (hz : orderOf z = 2) (K : Subgroup P)
    [CFSG.IsElementaryAbelian 2 K] (hK : Nat.card K = 2 ^ (w + 1)) (hzK : z ∈ K) :
    Nat.card (Vsp K z) = 2 ^ w ∧ finrank (ZMod 2) (Vsp K z) = w ∧
    K.Normal ∧ K.index = 2 ^ w ∧ (∀ r s : P, r ^ 2 ∈ K ∧ ⁅r, s⁆ ∈ K) ∧
    ∃ f : P → Dual (ZMod 2) (Vsp K z),
      (∀ (r : P) (k : K), r⁻¹ * (k : P)⁻¹ * r * k =
        z ^ (f r (Additive.ofMul (QuotientGroup.mk k))).val) ∧
      (∀ r s, f (r * s) = f r + f s) ∧ (∀ r, f r = 0 ↔ r ∈ K) ∧ Function.Surjective f ∧
      (∀ v, (∀ r, f r v = 0) → v = 0) ∧
      (∀ l : P →* Multiplicative (ZMod 2), K ≤ l.ker →
        ∃ v, ∀ r, Multiplicative.toAdd (l r) = f r v) ∧
      finrank (ZMod 2) (altHom (ZMod 2) (Vsp K z)) = w * (w - 1) / 2 ∧
      ∃ T : autFixing K →* Multiplicative (altHom (ZMod 2) (Vsp K z)),
        (∀ (α : autFixing K) (r : P), ∃ k : K, (k : P) = (α : MulAut P) r * r⁻¹ ∧
          ((Multiplicative.toAdd (T α) : altHom (ZMod 2) (Vsp K z)) :
            Dual (ZMod 2) (Vsp K z) →ₗ[ZMod 2] Vsp K z) (f r) =
              Additive.ofMul (QuotientGroup.mk k)) ∧
        innOf K ≤ autFixing K ∧ T.ker = (innOf K).subgroupOf (autFixing K) ∧
        (∃ _ : ((innOf K).subgroupOf (autFixing K)).Normal,
          ∃ φ : autFixing K ⧸ (innOf K).subgroupOf (autFixing K) →*
            Multiplicative (altHom (ZMod 2) (Vsp K z)),
            Function.Injective φ ∧ ∀ α, φ (QuotientGroup.mk α) = T α) ∧
        ∀ β ∈ autStab K, ∃ h : Vsp K z ≃ₗ[ZMod 2] Vsp K z,
          (∀ k : K, ∃ k' : K, (k' : P) = β k ∧
            h (Additive.ofMul (QuotientGroup.mk k)) = Additive.ofMul (QuotientGroup.mk k')) ∧
          (∀ U ∈ altHom (ZMod 2) (Vsp K z),
            h.toLinearMap ∘ₗ U ∘ₗ h.toLinearMap.dualMap ∈ altHom (ZMod 2) (Vsp K z)) ∧
          ∀ α γ : autFixing K, (γ : MulAut P) = β * α * β⁻¹ →
            ((Multiplicative.toAdd (T γ) : altHom (ZMod 2) (Vsp K z)) :
              Dual (ZMod 2) (Vsp K z) →ₗ[ZMod 2] Vsp K z) =
              h.toLinearMap ∘ₗ ((Multiplicative.toAdd (T α) : altHom (ZMod 2) (Vsp K z)) :
                Dual (ZMod 2) (Vsp K z) →ₗ[ZMod 2] Vsp K z) ∘ₗ h.toLinearMap.dualMap := by
  have H : PtwHyp P w z K := ⟨hP, hZ, hP', hz, hK, hzK⟩
  have hzpK : zpowers z ≤ K := by rw [zpowers_le]; exact hzK
  have hcomm : ∀ r s : P, ⁅r, s⁆ ∈ K := fun r s =>
    hzpK (hP' ▸ commutator_mem_commutator (mem_top r) (mem_top s))
  have hnormal : K.Normal := ⟨fun k hk g => by
    have : g * k * g⁻¹ = ⁅g, k⁆ * k := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem (hcomm g k) hk⟩
  have hindex : K.index = 2 ^ w := by
    have h := K.card_mul_index
    rw [hK, hP] at h
    have : 2 ^ (1 + 2 * w) = 2 ^ (w + 1) * 2 ^ w := by rw [← pow_add]; congr 1; ring
    rw [this] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  refine ⟨card_vsp H, finrank_vsp H, hnormal, hindex, fun r s => ⟨hzpK (H.sq_mem r), hcomm r s⟩,
    fr H, fun r k => H.pv_spec r k, fr_mul H, fun r => ?_, fr_surjective H, eq_zero_of_fr H,
    exists_eq_fr_apply H, ?_, tHom H, fun α r => ⟨⟨_, disp_mem H α.2 r⟩, rfl, tLin_fr H α r⟩,
    innOf_le_autFixing, tHom_ker H, ?_, fun β hβ => ?_⟩
  · rw [← mem_frHom_ker, frHom_ker H]
  · rw [finrank_altHom, finrank_vsp H]
  · exact exists_quot_injective H
  · refine ⟨hEquiv H hβ, fun k => ⟨⟨β k, apply_mem_of_mem_autStab hβ k.2⟩, rfl, hInd_mk H hβ k⟩,
      fun U hU => hInd_comp_mem_altHom H hβ hU, fun α γ hγ => ?_⟩
    have hγ' : γ = ⟨β * α * β⁻¹, conj_mem_autFixing hβ α.2⟩ := Subtype.ext hγ
    rw [hγ', hEquiv_toLinearMap, tHom_apply, tHom_apply, tLin_conj]

end CFSG.LocalAnalysis.GorensteinLyons

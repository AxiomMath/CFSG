module

public import CFSG.FeitThompson.OddOrder.ShiftedInversionIteration
import CFSG.FeitThompson.Local.CoprimeSplittingFiniteAbelian
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section ToAdditiveEnd

variable {A : Type*} [CommGroup A]

def toAdditiveEnd (σ : MulAut A) : AddMonoid.End (Additive A) :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (σ (Additive.toMul a)))
    (fun _ _ => congrArg Additive.ofMul (map_mul σ _ _))

@[simp] theorem toAdditiveEnd_apply (σ : MulAut A) (a : Additive A) :
    toAdditiveEnd σ a = Additive.ofMul (σ (Additive.toMul a)) := (rfl)

@[simp] theorem toAdditiveEnd_one : toAdditiveEnd (1 : MulAut A) = 1 := by
  ext a; rfl

theorem toAdditiveEnd_mul (σ τ : MulAut A) :
    toAdditiveEnd (σ * τ) = toAdditiveEnd σ * toAdditiveEnd τ := by
  ext a; rfl

theorem toAdditiveEnd_pow_apply (σ : MulAut A) (n : ℕ) (a : Additive A) :
    (toAdditiveEnd σ ^ n) a = Additive.ofMul ((σ ^ n) (Additive.toMul a)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change toAdditiveEnd σ ((toAdditiveEnd σ ^ n) a) = _
      rw [ih, toAdditiveEnd_apply]
      rfl

theorem toAdditiveEnd_pow_eq_one {σ : MulAut A} {n : ℕ} (hσ : σ ^ n = 1) :
    toAdditiveEnd σ ^ n = 1 := by
  ext a
  rw [toAdditiveEnd_pow_apply, hσ]
  rfl

end ToAdditiveEnd

section Core

variable {G : Type*} [Group G] {Q : Subgroup G} {p : ℕ} {s y : G}

open Subgroup
open scoped commutatorElement

theorem exists_mem_centralizer_mul_mem_commutator (hQab : IsMulCommutative ↥Q)
    (hcop : (Nat.card ↥Q).Coprime p) (hs : s ^ p = 1)
    (hsQ : s ∈ normalizer (Q : Set G)) (hy : y ∈ Q) :
    ∃ c ∈ centralizer (zpowers s : Set G), ∃ y₀ ∈ ⁅Q, zpowers s⁆, y = c * y₀ := by
  let _ : CommGroup ↥Q := @IsMulCommutative.instCommGroup ↥Q _ hQab
  set σ : MulAut ↥Q := Q.normalizerMonoidHom ⟨s, hsQ⟩ with hσ
  have hσp : σ ^ p = 1 := by
    have hsp : (⟨s, hsQ⟩ : ↥(normalizer (Q : Set G))) ^ p = 1 := Subtype.ext (by simpa using hs)
    rw [hσ, ← map_pow, hsp, map_one]
  obtain ⟨cA, hcA, bA, hbA, habc⟩ :=
    exists_add_eq_of_pow_eq_one (A := Additive ↥Q) hcop.symm (toAdditiveEnd_pow_eq_one hσp)
      (Additive.ofMul (⟨y, hy⟩ : ↥Q))
  set c : ↥Q := Additive.toMul cA with hc
  set b : ↥Q := Additive.toMul bA with hb
  have hfix : σ c = c := by
    have h := mem_ker_sub_one_iff.1 hcA
    rw [toAdditiveEnd_apply] at h
    exact Additive.ofMul.injective h
  have hcs : Commute s (c : G) := by
    have h1 : s * (c : G) * s⁻¹ = (c : G) := by
      have h := congrArg Subtype.val hfix
      rwa [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    exact mul_inv_eq_iff_eq_mul.1 h1
  refine ⟨(c : G), ?_, (b : G), ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := hh
    exact ((hcs.symm).zpow_right k).symm.eq
  · obtain ⟨d, hd⟩ := mem_range_sub_one_iff.1 hbA
    set d' : ↥Q := Additive.toMul d with hd'def
    have hdiv : σ d' / d' = b := by
      have h := congrArg Additive.toMul hd
      simpa [toAdditiveEnd_apply, hb, hd'def] using h
    have hval : s * (d' : G) * s⁻¹ / (d' : G) = (b : G) := by
      have h := congrArg Subtype.val hdiv
      rwa [Subgroup.coe_div, hσ, Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    have hbc : (b : G) = ⁅s, (d' : G)⁆ := by
      rw [← hval, commutatorElement_def, div_eq_mul_inv]
    rw [hbc, Subgroup.commutator_comm]
    exact commutator_mem_commutator (mem_zpowers s) d'.2
  · have h := congrArg Additive.toMul habc
    simpa [hc, hb, Subtype.ext_iff] using h.symm

theorem map_conj_inv_eq_of_mem_centralizer {H : Subgroup G} {c y y₀ : G}
    (hc : c ∈ centralizer (H : Set G)) (hy : y = c * y₀) :
    H.map (MulAut.conj y⁻¹).toMonoidHom = H.map (MulAut.conj y₀⁻¹).toMonoidHom := by
  have key : ∀ x ∈ H, (MulAut.conj y⁻¹) x = (MulAut.conj y₀⁻¹) x := by
    intro x hx
    have hxc : x * c = c * x := (mem_centralizer_iff.1 hc) x hx
    have hcx : c⁻¹ * x * c = x := by
      rw [mul_assoc, hxc, ← mul_assoc, inv_mul_cancel, one_mul]
    simp only [MulAut.conj_apply, inv_inv, hy, mul_inv_rev]
    calc y₀⁻¹ * c⁻¹ * x * (c * y₀) = y₀⁻¹ * (c⁻¹ * x * c) * y₀ := by group
    _ = y₀⁻¹ * x * y₀ := by rw [hcx]
  ext g
  simp only [mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (key x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, key x hx⟩

theorem exists_mem_commutator_map_conj_inv_eq (hQab : IsMulCommutative ↥Q)
    (hcop : (Nat.card ↥Q).Coprime p) (hs : s ^ p = 1)
    (hsQ : s ∈ normalizer (Q : Set G)) (hy : y ∈ Q) :
    ∃ y₀ ∈ ⁅Q, zpowers s⁆,
      (zpowers s).map (MulAut.conj y₀⁻¹).toMonoidHom
        = (zpowers s).map (MulAut.conj y⁻¹).toMonoidHom := by
  obtain ⟨c, hc, y₀, hy₀, hyc⟩ :=
    exists_mem_centralizer_mul_mem_commutator hQab hcop hs hsQ hy
  exact ⟨y₀, hy₀, (map_conj_inv_eq_of_mem_centralizer hc hyc).symm⟩

end Core

section AppendixC

variable {G : Type*} [Group G] {F : Type*} [Field F] [Fintype F] {p q m : ℕ}

open Subgroup
open scoped commutatorElement

theorem exists_mem_commutator_map_conj_inv_eq_of_appendixC
    (_hp : p.Prime) (hq : q.Prime) (_hqp : q < p) (hcard : Fintype.card F = p ^ q)
    (_hm : m = (p ^ q - 1) / (p - 1)) (_hcop : Nat.Coprime m (p - 1))
    {P U : Subgroup G} (Pe : Multiplicative F ≃* P) (Ue : normOneSubgroup F m ≃* U)
    (_hPU : P ⊓ U = ⊥)
    (_hact : ∀ (z : F) (u : normOneSubgroup F m),
      (Ue u : G)⁻¹ * (Pe (Multiplicative.ofAdd z) : G) * (Ue u : G)
        = (Pe (Multiplicative.ofAdd (z * ((u : Fˣ) : F))) : G))
    {H P₀ P₁ Q : Subgroup G} (_hH : H = P ⊔ U) {s t y : G}
    (hs : s = (Pe (Multiplicative.ofAdd (1 : F)) : G))
    (hP₀ : P₀ = (Subgroup.zpowers (Multiplicative.ofAdd (1 : F))).map
      (P.subtype.comp Pe.toMonoidHom))
    (hQab : IsMulCommutative ↥Q) (hQp : (Nat.card ↥Q).Coprime p)
    (hQnorm : P₀ ≤ normalizer (Q : Set G)) (hy : y ∈ Q)
    (hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹).toMonoidHom) (hP₁U : P₁ ≤ normalizer (U : Set G))
    (_ht : t = y⁻¹ * s * y) :
    ∃ y₀ ∈ ⁅Q, P₀⁆, P₀.map (MulAut.conj y₀⁻¹).toMonoidHom = P₁ ∧
      P₀.map (MulAut.conj y₀⁻¹).toMonoidHom ≤ normalizer (U : Set G) := by
  have hP₀s : P₀ = zpowers s := by
    rw [hP₀, MonoidHom.map_zpowers, hs]; rfl
  have hsp : s ^ p = 1 := by
    rw [hs]
    exact pow_apply_ofAdd_one_eq_one hq.ne_zero hcard (P.subtype.comp Pe.toMonoidHom)
  obtain ⟨c, hc, y₀, hy₀, hyc⟩ :=
    exists_mem_centralizer_mul_mem_commutator hQab hQp hsp (hQnorm (hP₀s ▸ mem_zpowers s)) hy
  have heq : P₀.map (MulAut.conj y₀⁻¹).toMonoidHom = P₁ := by
    rw [hP₁]
    exact (map_conj_inv_eq_of_mem_centralizer (H := P₀) (hP₀s ▸ hc) hyc).symm
  exact ⟨y₀, hP₀s ▸ hy₀, heq, heq ▸ hP₁U⟩

end AppendixC

end CFSG.FeitThompson

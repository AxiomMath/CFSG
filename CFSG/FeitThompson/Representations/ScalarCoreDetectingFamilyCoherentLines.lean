module

public import CFSG.FeitThompson.OddOrder.ChiefFactorFaithfulLinearImage
public import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ChiefLineDictionary

open Subgroup Module ChiefFactorLinearAction ChiefFactorFaithfulImage

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

variable {p : ℕ} {W : Type u} [AddCommGroup W] [Module (ZMod p) W]

def subgroupOrderIsoSubmodule (p : ℕ) {E : Type*} [Group E] {W : Type*} [AddCommGroup W]
    [Module (ZMod p) W] (e : E ≃* Multiplicative W) : Subgroup E ≃o Submodule (ZMod p) W :=
  (e.comapSubgroup.symm.trans Subgroup.toAddSubgroup').trans (AddSubgroup.toZModSubmodule p)

theorem mem_subgroupOrderIsoSubmodule {E : Type*} [Group E] (e : E ≃* Multiplicative W)
    (X : Subgroup E) (w : W) :
    w ∈ subgroupOrderIsoSubmodule p e X ↔ e.symm (Multiplicative.ofAdd w) ∈ X := by
  simp [subgroupOrderIsoSubmodule, MulEquiv.comapSubgroup]

theorem natCard_subgroupOrderIsoSubmodule {E : Type*} [Group E] (e : E ≃* Multiplicative W)
    (X : Subgroup E) : Nat.card (subgroupOrderIsoSubmodule p e X) = Nat.card X :=
  Nat.card_congr
    { toFun := fun w => ⟨e.symm (Multiplicative.ofAdd (w : W)),
        (mem_subgroupOrderIsoSubmodule e X _).1 w.2⟩
      invFun := fun x => ⟨Multiplicative.toAdd (e (x : E)), by
        rw [mem_subgroupOrderIsoSubmodule]; simp⟩
      left_inv := fun w => by ext; simp
      right_inv := fun x => by ext; simp }

theorem finrank_subgroupOrderIsoSubmodule {E : Type*} [Group E] (hp : p.Prime)
    (e : E ≃* Multiplicative W) {X : Subgroup E} (hX : Nat.card X = p) :
    finrank (ZMod p) (subgroupOrderIsoSubmodule p e X) = 1 := by
  have _hf : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (subgroupOrderIsoSubmodule p e X) = p := by
    rw [natCard_subgroupOrderIsoSubmodule, hX]
  have _hfin : Finite (subgroupOrderIsoSubmodule p e X) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.pos.ne')
  have _hft : Fintype (subgroupOrderIsoSubmodule p e X) := Fintype.ofFinite _
  have h := Module.card_eq_pow_finrank (K := ZMod p) (V := subgroupOrderIsoSubmodule p e X)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at h
  have h1 : p ^ 1 = p ^ finrank (ZMod p) (subgroupOrderIsoSubmodule p e X) := by
    rw [pow_one]; exact h
  exact ((Nat.pow_right_injective hp.two_le) h1).symm

theorem iSupIndep_subgroupOrderIsoSubmodule {E : Type*} [Group E] {ι : Type*}
    (e : E ≃* Multiplicative W) {X : ι → Subgroup E} (h : iSupIndep X) :
    iSupIndep fun i => subgroupOrderIsoSubmodule p e (X i) :=
  (iSupIndep_map_orderIso_iff (subgroupOrderIsoSubmodule p e)).mpr h

theorem iSup_subgroupOrderIsoSubmodule_eq_top {E : Type*} [Group E] {ι : Type*}
    (e : E ≃* Multiplicative W) {X : ι → Subgroup E} (h : ⨆ i, X i = ⊤) :
    ⨆ i, subgroupOrderIsoSubmodule p e (X i) = ⊤ := by
  have h2 : ⨆ i, subgroupOrderIsoSubmodule p e (X i)
      = subgroupOrderIsoSubmodule p e (⨆ i, X i) :=
    (map_iSup (subgroupOrderIsoSubmodule p e) X).symm
  rw [h2, h, TopHomClass.map_top]

section Equivariance

variable {L : Type u} [Group L] {H H0 : Subgroup L} [H.Normal] [H0.Normal]

theorem conjQuotientAut_eq_factorConjAut' (H H0 : Subgroup L) [H.Normal] [H0.Normal] :
    conjQuotientAut H H0 = factorConjAut H H0 := by
  ext g y
  induction y using QuotientGroup.induction_on with
  | _ h => rw [conjQuotientAut_apply_mk, factorConjAut_mk]

theorem map_subgroupOrderIsoSubmodule (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
    (X : Subgroup (↥H ⧸ H0.subgroupOf H)) (g : L) :
    (subgroupOrderIsoSubmodule p e X).map (factorLinearAut p H H0 e g : W →ₗ[ZMod p] W)
      = subgroupOrderIsoSubmodule p e (Subgroup.map (factorConjAut H H0 g) X) := by
  have key : ∀ w : W, (factorLinearAut p H H0 e g : W →ₗ[ZMod p] W) w
      = Multiplicative.toAdd (e (factorConjAut H H0 g (e.symm (Multiplicative.ofAdd w)))) :=
    fun w => factorLinearAut_apply' p e g w
  ext w
  simp only [Submodule.mem_map, mem_subgroupOrderIsoSubmodule, Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨e.symm (Multiplicative.ofAdd v), hv, e.injective ?_⟩
    rw [MulEquiv.apply_symm_apply, key v]
    rfl
  · rintro ⟨x, hx, hxw⟩
    refine ⟨Multiplicative.toAdd (e x), by simpa using hx, ?_⟩
    rw [key]
    have h : e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e x))) = x := by simp
    rw [h]
    have hxw' : factorConjAut H H0 g x = e.symm (Multiplicative.ofAdd w) := hxw
    rw [hxw']
    simp

theorem map_subgroupOrderIsoSubmodule_of_map_eq
    (e : (↥H ⧸ H0.subgroupOf H) ≃* Multiplicative W)
    {X : Subgroup (↥H ⧸ H0.subgroupOf H)} {g : L}
    (hg : Subgroup.map (factorConjAut H H0 g) X = X) :
    (subgroupOrderIsoSubmodule p e X).map (factorLinearAut p H H0 e g : W →ₗ[ZMod p] W)
      = subgroupOrderIsoSubmodule p e X := by
  rw [map_subgroupOrderIsoSubmodule, hg]

end Equivariance

end ChiefLineDictionary

end CFSG.FeitThompson

module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
public import CFSG.LinearAlgebra.LinearGroups.QuadraticActions
public import CFSG.Assembly.OrderReductions.ElementaryRepresentation

public section

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.ABGLocalTools

variable {H : Type*} [Group H] {p : ℕ} {N W₁ W₂ : Subgroup H}

theorem IsChiefFactorUnder.normal (h : IsChiefFactorUnder p N W₁ W₂) :
    (W₂.subgroupOf W₁).Normal :=
  ⟨fun x hx g => h.2.2.2.1 g g.2 x hx⟩

theorem IsChiefFactorUnder.isElementaryAbelian (h : IsChiefFactorUnder p N W₁ W₂)
    [(W₂.subgroupOf W₁).Normal] : IsElementaryAbelian p (W₁ ⧸ W₂.subgroupOf W₁) where
  is_comm := ⟨fun x y => by
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have : (((a * b)⁻¹ * (b * a) : W₁) : H) = ⁅(b : H)⁻¹, (a : H)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [this]
    exact h.2.2.2.2.1 _ (inv_mem b.2) _ (inv_mem a.2)⟩
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, Subgroup.coe_pow]
    exact h.2.2.2.2.2.1 _ a.2

@[expose] noncomputable def chiefConj (hN₁ : N ≤ normalizer (W₁ : Set H)) : N →* MulAut W₁ :=
  (normalizerMonoidHom W₁).comp (inclusion hN₁)

theorem chiefConj_apply_coe (hN₁ : N ≤ normalizer (W₁ : Set H)) (n : N) (w : W₁) :
    ((chiefConj hN₁ n w : W₁) : H) = n * w * (n : H)⁻¹ := by
  rw [chiefConj, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe]
  rfl

theorem chiefConj_map_eq (hN₁ : N ≤ normalizer (W₁ : Set H)) (hN₂ : N ≤ normalizer (W₂ : Set H))
    (n : N) : (W₂.subgroupOf W₁).map (chiefConj hN₁ n : W₁ →* W₁) = W₂.subgroupOf W₁ := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hy
    rw [mem_subgroupOf, MonoidHom.coe_ofClass, chiefConj_apply_coe]
    exact (mem_normalizer_iff.mp (hN₂ n.2) y).mp hy
  · intro x hx
    rw [mem_subgroupOf] at hx
    refine ⟨chiefConj hN₁ n⁻¹ x, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf, chiefConj_apply_coe]
      have := (mem_normalizer_iff.mp (hN₂ (inv_mem n.2)) x).mp hx
      simpa using this
    · apply Subtype.ext
      rw [MonoidHom.coe_ofClass, chiefConj_apply_coe, chiefConj_apply_coe]
      simp [mul_assoc]

@[expose] noncomputable def chiefAction (hN₁ : N ≤ normalizer (W₁ : Set H))
    (hN₂ : N ≤ normalizer (W₂ : Set H)) [(W₂.subgroupOf W₁).Normal] :
    N →* MulAut (W₁ ⧸ W₂.subgroupOf W₁) where
  toFun n := QuotientGroup.congr _ _ (chiefConj hN₁ n) (chiefConj_map_eq hN₁ hN₂ n)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H w =>
    rw [QuotientGroup.congr_mk, map_one]
    rfl
  map_mul' n m := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H w =>
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
      map_mul]
    rfl

theorem chiefAction_mk (hN₁ : N ≤ normalizer (W₁ : Set H)) (hN₂ : N ≤ normalizer (W₂ : Set H))
    [(W₂.subgroupOf W₁).Normal] (n : N) (w : W₁) :
    chiefAction hN₁ hN₂ n (w : W₁ ⧸ W₂.subgroupOf W₁) =
      ((chiefConj hN₁ n w : W₁) : W₁ ⧸ W₂.subgroupOf W₁) :=
  QuotientGroup.congr_mk _ _ _ (chiefConj_map_eq hN₁ hN₂ n) _

variable [Fact p.Prime]

@[expose] noncomputable def chiefRep (hN₁ : N ≤ normalizer (W₁ : Set H))
    (hN₂ : N ≤ normalizer (W₂ : Set H)) [(W₂.subgroupOf W₁).Normal]
    [IsElementaryAbelian p (W₁ ⧸ W₂.subgroupOf W₁)] :
    N →* LinearMap.GeneralLinearGroup (ZMod p) (Additive (W₁ ⧸ W₂.subgroupOf W₁)) :=
  (CFSG.OrderReductions.ElementaryRepresentation.linearRepresentation p
    (chiefAction hN₁ hN₂)).asGroupHom

theorem chiefRep_apply_mk (hN₁ : N ≤ normalizer (W₁ : Set H))
    (hN₂ : N ≤ normalizer (W₂ : Set H)) [(W₂.subgroupOf W₁).Normal]
    [IsElementaryAbelian p (W₁ ⧸ W₂.subgroupOf W₁)] (n : N) (w : W₁) :
    ((chiefRep (p := p) hN₁ hN₂ n : LinearMap.GeneralLinearGroup (ZMod p) _) :
        Additive (W₁ ⧸ W₂.subgroupOf W₁) →ₗ[ZMod p] _) (Additive.ofMul (w : W₁ ⧸ _)) =
      Additive.ofMul ((chiefConj hN₁ n w : W₁) : W₁ ⧸ W₂.subgroupOf W₁) := by
  rw [← chiefAction_mk hN₁ hN₂]
  rfl

omit [Fact p.Prime] in
theorem exists_ofMul_mk [(W₂.subgroupOf W₁).Normal] (v : Additive (W₁ ⧸ W₂.subgroupOf W₁)) :
    ∃ w : W₁, v = Additive.ofMul (w : W₁ ⧸ W₂.subgroupOf W₁) := by
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  exact ⟨w, by rw [hw]; rfl⟩

theorem chiefRep_eq_one_iff (hN₁ : N ≤ normalizer (W₁ : Set H))
    (hN₂ : N ≤ normalizer (W₂ : Set H)) [hW : (W₂.subgroupOf W₁).Normal]
    [IsElementaryAbelian p (W₁ ⧸ W₂.subgroupOf W₁)] (n : N) :
    chiefRep (p := p) hN₁ hN₂ n = 1 ↔ ∀ w ∈ W₁, ⁅w, (n : H)⁆ ∈ W₂ := by
  have key : ∀ w : W₁, ((chiefConj hN₁ n w : W₁) : W₁ ⧸ W₂.subgroupOf W₁) =
      (w : W₁ ⧸ W₂.subgroupOf W₁) ↔ ⁅(w : H), (n : H)⁆ ∈ W₂ := by
    intro w
    rw [QuotientGroup.eq, mem_subgroupOf]
    have hc : ⁅(w : H), (n : H)⁆ =
        (w : H) * (((chiefConj hN₁ n w)⁻¹ * w : W₁) : H) * (w : H)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, chiefConj_apply_coe, commutatorElement_def]
      group
    rw [hc]
    constructor
    · intro h
      have := hW.conj_mem _ ((mem_subgroupOf).mpr h) w
      rwa [mem_subgroupOf] at this
    · intro h
      have hmem : (w * ((chiefConj hN₁ n w)⁻¹ * w) * w⁻¹ : W₁) ∈ W₂.subgroupOf W₁ := by
        rw [mem_subgroupOf]
        simpa using h
      have := hW.conj_mem _ hmem w⁻¹
      rw [mem_subgroupOf] at this
      simpa [mul_assoc] using this
  constructor
  · intro h w hw
    rw [← key ⟨w, hw⟩]
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod p)
        (Additive (W₁ ⧸ W₂.subgroupOf W₁)) =>
      g.val (Additive.ofMul ((⟨w, hw⟩ : W₁) : W₁ ⧸ W₂.subgroupOf W₁))) h
    simp only [chiefRep_apply_mk, Units.val_one, Module.End.one_apply] at h1
    exact congrArg Additive.toMul h1
  · intro h
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := exists_ofMul_mk v
    rw [chiefRep_apply_mk, Units.val_one, Module.End.one_apply, (key w).mpr (h w w.2)]

theorem chiefRep_irreducible (hchief : IsChiefFactorUnder p N W₁ W₂)
    [(W₂.subgroupOf W₁).Normal] [IsElementaryAbelian p (W₁ ⧸ W₂.subgroupOf W₁)]
    (U : Submodule (ZMod p) (Additive (W₁ ⧸ W₂.subgroupOf W₁)))
    (hU : ∀ n : N, ∀ v ∈ U, (chiefRep (p := p) hchief.2.1 hchief.2.2.1 n).val v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  set Uq : Subgroup (W₁ ⧸ W₂.subgroupOf W₁) :=
    { carrier := {x | Additive.ofMul x ∈ U}
      mul_mem' := fun {x y} hx hy => by
        change Additive.ofMul x + Additive.ofMul y ∈ U
        exact U.add_mem hx hy
      one_mem' := U.zero_mem
      inv_mem' := fun {x} hx => by
        change -Additive.ofMul x ∈ U
        exact U.neg_mem hx } with hUq
  set X : Subgroup H := (Uq.comap (QuotientGroup.mk' (W₂.subgroupOf W₁))).map W₁.subtype with hX
  have hmemX : ∀ w : W₁, (w : H) ∈ X ↔ Additive.ofMul (w : W₁ ⧸ W₂.subgroupOf W₁) ∈ U := by
    intro w
    constructor
    · rintro ⟨w', hw', hww'⟩
      have : w' = w := Subtype.ext hww'
      rw [← this]
      exact hw'
    · intro hw
      exact ⟨w, hw, rfl⟩
  have hW₂X : W₂ ≤ X := by
    intro h hh
    have hhW₁ : h ∈ W₁ := hchief.1.le hh
    rw [show h = ((⟨h, hhW₁⟩ : W₁) : H) from rfl, hmemX]
    have : ((⟨h, hhW₁⟩ : W₁) : W₁ ⧸ W₂.subgroupOf W₁) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hh)
    rw [this]
    exact U.zero_mem
  have hXW₁ : X ≤ W₁ := map_subtype_le _
  have hconj : ∀ n : N, ∀ h ∈ X, (n : H) * h * (n : H)⁻¹ ∈ X := by
    rintro n _ ⟨w, hw, rfl⟩
    have h1 := hU n (Additive.ofMul (w : W₁ ⧸ W₂.subgroupOf W₁)) hw
    rw [chiefRep_apply_mk] at h1
    change (n : H) * (w : H) * (n : H)⁻¹ ∈ X
    rw [← chiefConj_apply_coe hchief.2.1 n w, hmemX]
    exact h1
  have hNX : N ≤ normalizer (X : Set H) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro h
    refine ⟨hconj ⟨n, hn⟩ h, fun hh => ?_⟩
    have := hconj ⟨n, hn⟩⁻¹ _ hh
    simpa [mul_assoc] using this
  rcases hchief.2.2.2.2.2.2 X hW₂X hXW₁ hNX with hXeq | hXeq
  · left
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨w, rfl⟩ := exists_ofMul_mk v
    have hw : (w : H) ∈ W₂ := by
      rw [← hXeq]
      exact (hmemX w).mpr hv
    have : (w : W₁ ⧸ W₂.subgroupOf W₁) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hw)
    rw [this, Submodule.mem_bot]
    rfl
  · right
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, rfl⟩ := exists_ofMul_mk v
    have hw : (w : H) ∈ X := by
      rw [hXeq]
      exact w.2
    exact (hmemX w).mp hw

omit [Fact p.Prime] in
theorem chiefConj_map_eq' (hN₁ : N ≤ normalizer (W₁ : Set H))
    (hN₂ : N ≤ normalizer (W₂ : Set H)) (n : N) :
    (W₂.subgroupOf W₁).map (chiefConj hN₁ n).toMonoidHom = W₂.subgroupOf W₁ :=
  chiefConj_map_eq hN₁ hN₂ n

theorem chiefRep_quadratic [Finite H] (hN₁ : N ≤ normalizer (W₁ : Set H))
    (hN₂ : N ≤ normalizer (W₂ : Set H)) [(W₂.subgroupOf W₁).Normal]
    [IsElementaryAbelian p (W₁ ⧸ W₂.subgroupOf W₁)] (a : N)
    (ha : ∀ u ∈ W₁, ⁅⁅u, (a : H)⁆, (a : H)⁆ = 1) :
    ((chiefRep (p := p) hN₁ hN₂ a).val - 1) ^ 2 = 0 := by
  have hval : (chiefRep (p := p) hN₁ hN₂ a).val =
      CFSG.LinearGroups.quotientLinearMap p (W₂.subgroupOf W₁) (chiefConj hN₁ a)
        (CFSG.LinearGroups.le_comap_of_map_eq _ (chiefConj_map_eq' hN₁ hN₂ a)) := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := exists_ofMul_mk v
    rw [chiefRep_apply_mk, CFSG.LinearGroups.quotientLinearMap_apply]
  rw [hval]
  refine CFSG.LinearGroups.quadratic_elementary_quotient p _ (chiefConj hN₁ a)
    (chiefConj_map_eq' hN₁ hN₂ a) fun u => ?_
  apply Subtype.ext
  have hcomm : Commute ⁅(u : H)⁻¹, (a : H)⁆ (a : H) :=
    commutatorElement_eq_one_iff_commute.mp (ha _ (inv_mem u.2))
  rw [Subgroup.coe_mul, Subgroup.coe_inv, chiefConj_apply_coe, Subgroup.coe_mul,
    Subgroup.coe_inv, chiefConj_apply_coe]
  have hc : (u : H)⁻¹ * ((a : H) * u * (a : H)⁻¹) = ⁅(u : H)⁻¹, (a : H)⁆ := by
    rw [commutatorElement_def, inv_inv]
    group
  rw [hc, ← hcomm.eq, mul_inv_cancel_right]

omit [Fact p.Prime] in
theorem pCore_range_eq_bot_of_irreducible [Fact p.Prime] {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] [Nontrivial V]
    (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hirr : ∀ U : Submodule (ZMod p) V, (∀ g : G, ∀ v ∈ U, (ρ g).val v ∈ U) → U = ⊥ ∨ U = ⊤) :
    pCore p ρ.range = ⊥ := by
  classical
  set Q := pCore p ρ.range with hQ
  let U : Submodule (ZMod p) V :=
    { carrier := {v | ∀ q ∈ Q,
        ((q : ρ.range) : LinearMap.GeneralLinearGroup (ZMod p) V).val v = v}
      add_mem' := fun {v w} hv hw q hq => by rw [map_add, hv q hq, hw q hq]
      zero_mem' := fun q _ => map_zero _
      smul_mem' := fun c v hv q hq => by rw [map_smul, hv q hq] }
  have hUinv : ∀ g : G, ∀ v ∈ U, (ρ g).val v ∈ U := by
    intro g v hv q hq
    set r : ρ.range := ⟨ρ g, g, rfl⟩
    have hq' : r⁻¹ * q * r ∈ Q := by
      have := (pCore_normal (p := p) (G := ρ.range)).conj_mem q hq r⁻¹
      simpa using this
    have h1 := hv _ hq'
    have h2 : ((r⁻¹ * q * r : ρ.range) : LinearMap.GeneralLinearGroup (ZMod p) V).val v =
        (ρ g)⁻¹.val (((q : ρ.range) : LinearMap.GeneralLinearGroup (ZMod p) V).val
          ((ρ g).val v)) := rfl
    rw [h2] at h1
    have h3 := congrArg (ρ g).val h1
    rwa [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply] at h3
  have hUne : U ≠ ⊥ := by
    let _ : MulAction Q V := MulAction.compHom V (ρ.range.subtype.comp Q.subtype)
    have hQp : IsPGroup p Q := pCore_isPGroup
    have : Fintype V := Fintype.ofFinite V
    have hcard : p ∣ Nat.card V := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
      exact dvd_pow_self p (Module.finrank_pos (R := ZMod p) (M := V)).ne'
    obtain ⟨v, hv, hv0⟩ := hQp.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard
      (a := 0) (fun q => smul_zero _)
    intro hbot
    apply hv0
    have hvU : v ∈ U := fun q hq => hv ⟨q, hq⟩
    rw [hbot, Submodule.mem_bot] at hvU
    exact hvU.symm
  rcases hirr U hUinv with h | h
  · exact absurd h hUne
  · rw [eq_bot_iff]
    intro q hq
    rw [mem_bot]
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    have hv : v ∈ U := by rw [h]; exact Submodule.mem_top
    exact hv q hq

end CFSG.ABGLocalTools

module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Algebra.Module.ZMod
public import CFSG.FeitThompson.Foundations.DerivedSubgroupCharacteristic
public import CFSG.FeitThompson.Local.NormalSubgroupCentralPrimeTorsion
public import CFSG.FeitThompson.Local.NormalSubgroupsOfEveryPrimePowerOrder

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped commutatorElement

section Derived

variable (H : Type*) [Group H]

theorem commutator_eq_closure_setOf :
    commutator H = Subgroup.closure {g : H | ∃ x y : H, x⁻¹ * y⁻¹ * x * y = g} :=
  (closure_setOf_inv_mul_inv_mul_mul_eq_commutator H).symm

end Derived

section Action

variable {H U : Type*} [Group H] [Group U]

theorem abelianization_monoidHom_ext {A : Type*} [Monoid A] {f g : Abelianization H →* A}
    (h : ∀ x : H, f (Abelianization.of x) = g (Abelianization.of x)) : f = g :=
  Abelianization.hom_ext f g (MonoidHom.ext h)

def abelianizationAut (ρ : U →* MulAut H) : U →* MulAut (Abelianization H) where
  toFun u := MulEquiv.abelianizationCongr (ρ u)
  map_one' := MulEquiv.toMonoidHom_injective (abelianization_monoidHom_ext (by simp))
  map_mul' u v := MulEquiv.toMonoidHom_injective (abelianization_monoidHom_ext (by simp))

@[simp]
theorem abelianizationAut_of (ρ : U →* MulAut H) (u : U) (x : H) :
    abelianizationAut ρ u (Abelianization.of x) = Abelianization.of (ρ u x) := by
  simp [abelianizationAut, MulEquiv.abelianizationCongr]

def zmodLinearAutOfMulAut (n : ℕ) {A : Type*} [CommGroup A] [Module (ZMod n) (Additive A)] :
    MulAut A →* (Additive A ≃ₗ[ZMod n] Additive A) where
  toFun e := { MulEquiv.toAdditive e with
    map_smul' := fun c v => ZMod.map_smul (MulEquiv.toAdditive e).toAddMonoidHom c v }
  map_one' := by ext; rfl
  map_mul' e f := by ext; rfl

def abelianizationLinearAut (p : ℕ) [Module (ZMod p) (Additive (Abelianization H))]
    (ρ : U →* MulAut H) :
    U →* (Additive (Abelianization H) ≃ₗ[ZMod p] Additive (Abelianization H)) :=
  (zmodLinearAutOfMulAut p).comp (abelianizationAut ρ)

theorem abelianizationLinearAut_apply (p : ℕ)
    [Module (ZMod p) (Additive (Abelianization H))] (ρ : U →* MulAut H) (u : U)
    (v : Additive (Abelianization H)) :
    abelianizationLinearAut p ρ u v =
      Additive.ofMul (abelianizationAut ρ u (Additive.toMul v)) := (rfl)

@[simp]
theorem abelianizationLinearAut_ofMul_of (p : ℕ)
    [Module (ZMod p) (Additive (Abelianization H))] (ρ : U →* MulAut H) (u : U) (x : H) :
    abelianizationLinearAut p ρ u (Additive.ofMul (Abelianization.of x))
      = Additive.ofMul (Abelianization.of (ρ u x)) := by
  rw [abelianizationLinearAut_apply]
  simp

end Action

section Descend

variable {p : ℕ} {H : Type*} [Group H]

theorem exists_ofMul_abelianizationOf (v : Additive (Abelianization H)) :
    ∃ x : H, Additive.ofMul (Abelianization.of x) = v := by
  obtain ⟨y, rfl⟩ := Additive.ofMul.surjective v
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective y
  exact ⟨x, rfl⟩

variable [Module (ZMod p) (Additive (Abelianization H))]

noncomputable def commFormInnerHom (c : H → H → ZMod p)
    (h2 : ∀ x y z : H, c x (y * z) = c x y + c x z) (x : H) :
    Additive (Abelianization H) →ₗ[ZMod p] ZMod p :=
  (MonoidHom.toAdditiveLeft
    (Abelianization.lift (MonoidHom.mk' (fun y => Multiplicative.ofAdd (c x y))
      (fun y z => by simp [h2 x y z])))).toZModLinearMap p

@[simp]
theorem commFormInnerHom_apply (c : H → H → ZMod p)
    (h2 : ∀ x y z : H, c x (y * z) = c x y + c x z) (x y : H) :
    commFormInnerHom c h2 x (Additive.ofMul (Abelianization.of y)) = c x y := (rfl)

noncomputable def commFormBilin (c : H → H → ZMod p)
    (h1 : ∀ x y z : H, c (x * y) z = c x z + c y z)
    (h2 : ∀ x y z : H, c x (y * z) = c x y + c x z) :
    Additive (Abelianization H) →ₗ[ZMod p]
      Additive (Abelianization H) →ₗ[ZMod p] ZMod p :=
  (MonoidHom.toAdditiveLeft
    (Abelianization.lift (MonoidHom.mk'
      (fun x => Multiplicative.ofAdd (commFormInnerHom c h2 x))
      (fun x y => by
        refine congrArg Multiplicative.ofAdd ?_
        ext v
        obtain ⟨z, rfl⟩ := exists_ofMul_abelianizationOf (H := H) v
        simp [h1 x y z])))).toZModLinearMap p

@[simp]
theorem commFormBilin_apply (c : H → H → ZMod p)
    (h1 : ∀ x y z : H, c (x * y) z = c x z + c y z)
    (h2 : ∀ x y z : H, c x (y * z) = c x y + c x z) (x y : H) :
    commFormBilin c h1 h2 (Additive.ofMul (Abelianization.of x))
      (Additive.ofMul (Abelianization.of y)) = c x y := (rfl)

end Descend

section CommForm

variable {p : ℕ} {H U : Type*} [Group H] [Group U] (Q : Subgroup H) [Q.Normal]

theorem commutatorElement_mk_mem (x y : H) :
    ⁅(QuotientGroup.mk x : H ⧸ Q), (QuotientGroup.mk y : H ⧸ Q)⁆ ∈
      (commutator H).map (QuotientGroup.mk' Q) := by
  have h : ⁅x, y⁆ ∈ commutator H := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have e1 : (QuotientGroup.mk' Q) ⁅x, y⁆
      = ⁅(QuotientGroup.mk x : H ⧸ Q), (QuotientGroup.mk y : H ⧸ Q)⁆ := by
    simp [commutatorElement_def]
  rw [← e1]
  exact Subgroup.mem_map_of_mem _ h

noncomputable def quotientCommForm
    (e : ↥((commutator H).map (QuotientGroup.mk' Q)) ≃* Multiplicative (ZMod p))
    (x y : H) : ZMod p :=
  Multiplicative.toAdd (e ⟨_, commutatorElement_mk_mem Q x y⟩)

theorem quotientCommForm_apply
    (e : ↥((commutator H).map (QuotientGroup.mk' Q)) ≃* Multiplicative (ZMod p)) (x y : H) :
    quotientCommForm Q e x y
      = Multiplicative.toAdd (e ⟨_, commutatorElement_mk_mem Q x y⟩) := (rfl)

theorem conj_eq_self_of_mem_of_le_center
    (hcent : (commutator H).map (QuotientGroup.mk' Q) ≤ Subgroup.center (H ⧸ Q))
    {t : H ⧸ Q} (ht : t ∈ (commutator H).map (QuotientGroup.mk' Q)) (g : H ⧸ Q) :
    g * t * g⁻¹ = t := by
  have h := (Subgroup.mem_center_iff.mp (hcent ht)) g
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem quotientCommForm_mul_left
    (hcent : (commutator H).map (QuotientGroup.mk' Q) ≤ Subgroup.center (H ⧸ Q))
    (e : ↥((commutator H).map (QuotientGroup.mk' Q)) ≃* Multiplicative (ZMod p)) (x y z : H) :
    quotientCommForm Q e (x * y) z = quotientCommForm Q e x z + quotientCommForm Q e y z := by
  have hmk : (QuotientGroup.mk (x * y) : H ⧸ Q)
      = QuotientGroup.mk x * QuotientGroup.mk y := rfl
  have hmul : ⁅(QuotientGroup.mk (x * y) : H ⧸ Q), (QuotientGroup.mk z : H ⧸ Q)⁆
      = ⁅(QuotientGroup.mk y : H ⧸ Q), (QuotientGroup.mk z : H ⧸ Q)⁆
        * ⁅(QuotientGroup.mk x : H ⧸ Q), (QuotientGroup.mk z : H ⧸ Q)⁆ := by
    rw [hmk, commutatorElement_mul_left_eq_conj_mul,
      conj_eq_self_of_mem_of_le_center Q hcent (commutatorElement_mk_mem Q y z)
        (QuotientGroup.mk x)]
  have hsub : (⟨_, commutatorElement_mk_mem Q (x * y) z⟩ :
        ↥((commutator H).map (QuotientGroup.mk' Q)))
      = ⟨_, commutatorElement_mk_mem Q y z⟩ * ⟨_, commutatorElement_mk_mem Q x z⟩ :=
    Subtype.ext hmul
  rw [quotientCommForm_apply, quotientCommForm_apply, quotientCommForm_apply, hsub, map_mul]
  simp [add_comm]

theorem quotientCommForm_mul_right
    (hcent : (commutator H).map (QuotientGroup.mk' Q) ≤ Subgroup.center (H ⧸ Q))
    (e : ↥((commutator H).map (QuotientGroup.mk' Q)) ≃* Multiplicative (ZMod p)) (x y z : H) :
    quotientCommForm Q e x (y * z) = quotientCommForm Q e x y + quotientCommForm Q e x z := by
  have hmk : (QuotientGroup.mk (y * z) : H ⧸ Q)
      = QuotientGroup.mk y * QuotientGroup.mk z := rfl
  have hmul : ⁅(QuotientGroup.mk x : H ⧸ Q), (QuotientGroup.mk (y * z) : H ⧸ Q)⁆
      = ⁅(QuotientGroup.mk x : H ⧸ Q), (QuotientGroup.mk y : H ⧸ Q)⁆
        * ⁅(QuotientGroup.mk x : H ⧸ Q), (QuotientGroup.mk z : H ⧸ Q)⁆ := by
    rw [hmk, commutatorElement_mul_right_eq_mul_conj,
      show ∀ A B C : H ⧸ Q, A * B * C * B⁻¹ = A * (B * C * B⁻¹) from fun A B C => by group,
      conj_eq_self_of_mem_of_le_center Q hcent (commutatorElement_mk_mem Q x z)
        (QuotientGroup.mk y)]
  have hsub : (⟨_, commutatorElement_mk_mem Q x (y * z)⟩ :
        ↥((commutator H).map (QuotientGroup.mk' Q)))
      = ⟨_, commutatorElement_mk_mem Q x y⟩ * ⟨_, commutatorElement_mk_mem Q x z⟩ :=
    Subtype.ext hmul
  rw [quotientCommForm_apply, quotientCommForm_apply, quotientCommForm_apply, hsub, map_mul]
  simp

theorem quotientCommForm_self
    (e : ↥((commutator H).map (QuotientGroup.mk' Q)) ≃* Multiplicative (ZMod p)) (x : H) :
    quotientCommForm Q e x x = 0 := by
  have hsub : (⟨_, commutatorElement_mk_mem Q x x⟩ :
      ↥((commutator H).map (QuotientGroup.mk' Q))) = 1 := Subtype.ext (by simp)
  rw [quotientCommForm_apply, hsub, map_one]
  simp

theorem quotientCommForm_aut
    (e : ↥((commutator H).map (QuotientGroup.mk' Q)) ≃* Multiplicative (ZMod p))
    (ρ : U →* MulAut H) (hfix : ∀ u : U, ∀ t ∈ commutator H, ρ u t = t) (u : U) (x y : H) :
    quotientCommForm Q e (ρ u x) (ρ u y) = quotientCommForm Q e x y := by
  have hc : ⁅x, y⁆ ∈ commutator H := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h1 : ⁅ρ u x, ρ u y⁆ = ⁅x, y⁆ := by
    have h0 : (ρ u) ⁅x, y⁆ = ⁅ρ u x, ρ u y⁆ := by simp [commutatorElement_def]
    rw [← h0, hfix u _ hc]
  have hsub : (⟨_, commutatorElement_mk_mem Q (ρ u x) (ρ u y)⟩ :
        ↥((commutator H).map (QuotientGroup.mk' Q)))
      = ⟨_, commutatorElement_mk_mem Q x y⟩ := by
    refine Subtype.ext ?_
    have h2 : ((⁅ρ u x, ρ u y⁆ : H) : H ⧸ Q)
        = ⁅(QuotientGroup.mk (ρ u x) : H ⧸ Q), (QuotientGroup.mk (ρ u y) : H ⧸ Q)⁆ := by
      simp [commutatorElement_def]
    rw [show ((⟨_, commutatorElement_mk_mem Q (ρ u x) (ρ u y)⟩ :
        ↥((commutator H).map (QuotientGroup.mk' Q))) : H ⧸ Q)
        = ⁅(QuotientGroup.mk (ρ u x) : H ⧸ Q), (QuotientGroup.mk (ρ u y) : H ⧸ Q)⁆ from rfl,
      ← h2, h1]
    simp [commutatorElement_def]
  rw [quotientCommForm_apply, quotientCommForm_apply, hsub]

end CommForm

section Main

variable {p a : ℕ} {H U : Type*} [Group H] [Group U]

theorem exists_ne_zero_isAlt_invariant_bilinForm_of_commutator_ne_bot
    [Module (ZMod p) (Additive (Abelianization H))]
    (hp : p.Prime) (_ha : 1 ≤ a) (hcard : Nat.card H = p ^ a)
    (hH' : commutator H ≠ ⊥) (ρ : U →* MulAut H)
    (hfix : ∀ u : U, ∀ t ∈ commutator H, ρ u t = t) :
    ∃ β : Additive (Abelianization H) →ₗ[ZMod p]
        Additive (Abelianization H) →ₗ[ZMod p] ZMod p,
      β ≠ 0 ∧ β.IsAlt ∧
        ∀ u : U, ∀ v w : Additive (Abelianization H),
          β (abelianizationLinearAut p ρ u v) (abelianizationLinearAut p ρ u w) = β v w := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfin : Finite H :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  have hPG : IsPGroup p H := IsPGroup.of_card hcard
  obtain ⟨n, hn⟩ := (hPG.to_subgroup (commutator H)).exists_card_eq
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp only [pow_zero] at hn
      exact absurd (Subgroup.eq_bot_of_card_eq _ hn) hH'
    · exact h
  obtain ⟨Q, hQle, hQnorm, hQcard⟩ :=
    exists_normal_le_natCard_eq_pow_of_isPGroup hp hPG (commutator H)
      (d := n - 1) (by rw [hn]; exact pow_dvd_pow _ (by omega))
  haveI := hQnorm
  haveI : Finite (H ⧸ Q) := Quotient.finite _
  haveI : ((commutator H).map (QuotientGroup.mk' Q)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Q)
  have hcs : Nat.card (Q.subgroupOf (commutator H)) = p ^ (n - 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv, hQcard]
  have hpn : p ^ n = p * p ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  have hidx : (Q.subgroupOf (commutator H)).index * p ^ (n - 1) = p * p ^ (n - 1) := by
    rw [← hcs, Subgroup.index_mul_card, hn, hpn, hcs]
  have hindex : (Q.subgroupOf (commutator H)).index = p :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (pow_ne_zero _ hp.pos.ne')) hidx
  have hRcard : Nat.card ((commutator H).map (QuotientGroup.mk' Q)) = p := by
    rw [← Subgroup.relIndex_ker (commutator H) (QuotientGroup.mk' Q), QuotientGroup.ker_mk']
    exact hindex
  have hbotcard : Nat.card ((⊥ : Subgroup (H ⧸ Q))) = 1 := by simp
  have hRne : (commutator H).map (QuotientGroup.mk' Q) ≠ ⊥ := by
    intro hb
    rw [hb, hbotcard] at hRcard
    exact hp.one_lt.ne hRcard
  obtain ⟨m, hm⟩ := (hPG.to_quotient Q).exists_card_eq
  obtain ⟨S, hSle, hScard⟩ :=
    exists_le_inf_center_natCard_eq ((commutator H).map (QuotientGroup.mk' Q)) hp hm hRne
  have hSeq : S = (commutator H).map (QuotientGroup.mk' Q) :=
    Subgroup.eq_of_le_of_card_ge (le_trans hSle inf_le_left)
      (le_of_eq (by rw [hRcard, hScard]))
  have hcent : (commutator H).map (QuotientGroup.mk' Q) ≤ Subgroup.center (H ⧸ Q) := by
    rw [← hSeq]
    exact le_trans hSle inf_le_right
  have hmc : Nat.card (Multiplicative (ZMod p)) = p := by
    haveI : NeZero p := ⟨hp.pos.ne'⟩
    rw [Nat.card_congr (Multiplicative.ofAdd (α := ZMod p)).symm, Nat.card_eq_fintype_card,
      ZMod.card]
  have e := mulEquivOfPrimeCardEq (p := p) hRcard hmc
  have hne : ∃ x y : H, quotientCommForm Q e x y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hle : commutator H ≤ Q := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      have h0 := (quotientCommForm_apply Q e x y).symm.trans (hcon x y)
      have hz : e ⟨_, commutatorElement_mk_mem Q x y⟩ = 1 :=
        Multiplicative.toAdd.injective (by simpa using h0)
      have h3 := congrArg Subtype.val (e.injective (hz.trans (map_one e).symm))
      have h1 : ⁅(QuotientGroup.mk x : H ⧸ Q), (QuotientGroup.mk y : H ⧸ Q)⁆ = 1 := by
        simpa using h3
      have h2 : (QuotientGroup.mk ⁅x, y⁆ : H ⧸ Q)
          = ⁅(QuotientGroup.mk x : H ⧸ Q), (QuotientGroup.mk y : H ⧸ Q)⁆ := by
        simp [commutatorElement_def]
      rw [← QuotientGroup.eq_one_iff, h2, h1]
    have hRb : (commutator H).map (QuotientGroup.mk' Q) ≤ ⊥ := by
      rw [Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk']
      exact hle
    rw [le_bot_iff] at hRb
    rw [hRb, hbotcard] at hRcard
    exact hp.one_lt.ne hRcard
  refine ⟨commFormBilin (quotientCommForm Q e)
      (quotientCommForm_mul_left Q hcent e) (quotientCommForm_mul_right Q hcent e), ?_, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hne
    refine fun hb => hxy ?_
    rw [← commFormBilin_apply (quotientCommForm Q e) (quotientCommForm_mul_left Q hcent e)
      (quotientCommForm_mul_right Q hcent e) x y, hb]
    simp
  · intro v
    obtain ⟨x, rfl⟩ := exists_ofMul_abelianizationOf (H := H) v
    rw [commFormBilin_apply]
    exact quotientCommForm_self Q e x
  · intro u v w
    obtain ⟨x, rfl⟩ := exists_ofMul_abelianizationOf (H := H) v
    obtain ⟨y, rfl⟩ := exists_ofMul_abelianizationOf (H := H) w
    rw [abelianizationLinearAut_ofMul_of, abelianizationLinearAut_ofMul_of,
      commFormBilin_apply, commFormBilin_apply]
    exact quotientCommForm_aut Q e ρ hfix u x y

end Main

end

end CFSG.FeitThompson

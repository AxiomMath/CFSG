module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBridge
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG

variable {G : Type} [Group G]

theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold conjugate
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g * (MulAut.conj g⁻¹).toMonoidHom y * g⁻¹ = y := by
      show g * (MulAut.conj g⁻¹ y) * g⁻¹ = y
      simp only [MulAut.conj_apply]
      group
    rw [this]; exact hy
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    show MulAut.conj g⁻¹ (g * x * g⁻¹) = x
    simp only [MulAut.conj_apply]
    group

theorem conjugate_mul' (H : Subgroup G) (a b : G) :
    conjugate H (a * b) = conjugate (conjugate H a) b := by
  ext x
  simp only [mem_conjugate_iff']
  rw [show a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group]

theorem conjugate_inf' (A B : Subgroup G) (g : G) :
    conjugate (A ⊓ B) g = conjugate A g ⊓ conjugate B g := by
  ext x
  simp only [mem_conjugate_iff', Subgroup.mem_inf]

theorem conjugate_le_conjugate' {A B : Subgroup G} (h : A ≤ B) (g : G) :
    conjugate A g ≤ conjugate B g := fun _ hx => mem_conjugate_iff'.2 (h (mem_conjugate_iff'.1 hx))

theorem conjugate_one' (H : Subgroup G) : conjugate H 1 = H := by
  ext x; simp [mem_conjugate_iff']

theorem conjugate_of_mem {M : Subgroup G} {g : G} (hg : g ∈ M) : conjugate M g = M := by
  ext x
  rw [mem_conjugate_iff']
  constructor
  · intro h
    have := M.mul_mem (M.mul_mem (M.inv_mem hg) h) hg
    simpa [mul_assoc] using this
  · intro h
    exact M.mul_mem (M.mul_mem hg h) (M.inv_mem hg)

theorem conjugate_inv_conjugate' (H : Subgroup G) (g : G) : conjugate (conjugate H g) g⁻¹ = H := by
  rw [← conjugate_mul', mul_inv_cancel, conjugate_one']

theorem conjugate_conjugate_inv' (H : Subgroup G) (g : G) : conjugate (conjugate H g⁻¹) g = H := by
  rw [← conjugate_mul', inv_mul_cancel, conjugate_one']

@[expose] noncomputable def conjugateEquiv (H : Subgroup G) (g : G) : ↥H ≃* ↥(conjugate H g) :=
  (Subgroup.equivMapOfInjective H (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective)

theorem card_conjugate' (H : Subgroup G) (g : G) : Nat.card ↥(conjugate H g) = Nat.card ↥H :=
  (Nat.card_congr (conjugateEquiv H g).toEquiv).symm

theorem isPGroup_conjugate' {p : ℕ} {H : Subgroup G} (h : IsPGroup p ↥H) (g : G) :
    IsPGroup p ↥(conjugate H g) := h.of_equiv (conjugateEquiv H g)

theorem pRank_conjugate' [Finite G] (H : Subgroup G) (g : G) :
    pRank 2 ↥(conjugate H g) = pRank 2 ↥H :=
  (CFSG.RankThree.PartOne.Quotient36.pRank_congr_mulEquiv one_lt_two (conjugateEquiv H g)).symm

theorem pRank_mono' [Finite G] {A B : Subgroup G} (h : A ≤ B) : pRank 2 ↥A ≤ pRank 2 ↥B :=
  CFSG.RankThree.PartOne.Quotient36.pRank_mono_subgroup one_lt_two h

theorem isElementaryAbelian_of_forall {U : Subgroup G} (hab : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    (hsq : ∀ u ∈ U, u * u = 1) : CFSG.IsElementaryAbelian 2 ↥U := by
  have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
  have : (a : G) * a = 1 := hsq a a.2
  apply Subtype.ext
  simp [sq, this]

theorem forall_of_isElementaryAbelian {U : Subgroup G} (h : CFSG.IsElementaryAbelian 2 ↥U) :
    (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) ∧ (∀ u ∈ U, u * u = 1) := by
  refine ⟨fun u hu v hv => ?_, fun u hu => ?_⟩
  · have hc := mul_comm' (⟨u, hu⟩ : ↥U) ⟨v, hv⟩
    exact congrArg Subtype.val hc
  · have : (u : G) ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) u hu
    rwa [sq] at this

theorem isElementaryAbelian_conjugate {U : Subgroup G} (h : CFSG.IsElementaryAbelian 2 ↥U) (g : G) :
    CFSG.IsElementaryAbelian 2 ↥(conjugate U g) := by
  obtain ⟨hab, hsq⟩ := forall_of_isElementaryAbelian h
  refine isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
  · have h1 := hab _ (mem_conjugate_iff'.1 hu) _ (mem_conjugate_iff'.1 hv)
    have e1 : g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
    have e2 : g * v * g⁻¹ * (g * u * g⁻¹) = g * (v * u) * g⁻¹ := by group
    rw [e1, e2] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  · have h1 := hsq _ (mem_conjugate_iff'.1 hu)
    have e1 : g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
    rw [e1] at h1
    have := congrArg (fun y => g⁻¹ * y * g) h1
    simpa [mul_assoc] using this

theorem card_eq_two_pow_pRank [Finite G] {U : Subgroup G} (h : CFSG.IsElementaryAbelian 2 ↥U) :
    Nat.card ↥U = 2 ^ pRank 2 ↥U := by
  have hp : IsPGroup 2 ↥U := CFSG.IsElementaryAbelian.isPGroup 2 ↥U
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  rw [hk, CFSG.pRank_eq_of_card_eq_pow one_lt_two hk]

end CFSG.GH74.GLS.C3.Layer1.Back

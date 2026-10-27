module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Alt

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem centralizes_of_actW_eq_one {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I)
    (hker : (actOn L A I hAn hI L le_sup_left).ker = ⊥) {x : ↥(L ⊔ A)}
    (hx : actW L A I hAn hI x = 1) :
    ∀ y ∈ L, (x : V ≃ₗ[ZMod 2] V) * y = y * (x : V ≃ₗ[ZMod 2] V) := by
  intro y hy
  have hxnorm : (x : V ≃ₗ[ZMod 2] V) ∈ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)) :=
    (sup_le Subgroup.le_normalizer hAn) x.2
  have hy' : (x : V ≃ₗ[ZMod 2] V) * y * (x : V ≃ₗ[ZMod 2] V)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 hxnorm y).1 hy
  have e1 : actOn L A I hAn hI L le_sup_left ⟨_, hy'⟩ =
      actOn L A I hAn hI L le_sup_left ⟨y, hy⟩ := by
    show actW L A I hAn hI ⟨_, Subgroup.mem_sup_left hy'⟩ = actW L A I hAn hI ⟨y, Subgroup.mem_sup_left hy⟩
    have : (⟨(x : V ≃ₗ[ZMod 2] V) * y * (x : V ≃ₗ[ZMod 2] V)⁻¹, Subgroup.mem_sup_left hy'⟩ : ↥(L ⊔ A)) =
        x * ⟨y, Subgroup.mem_sup_left hy⟩ * x⁻¹ := rfl
    rw [this, map_mul, map_mul, hx, map_inv, hx, one_mul, inv_one, mul_one]
  have e2 : (⟨_, hy'⟩ : ↥L) = ⟨y, hy⟩ := (MonoidHom.ker_eq_bot_iff _).1 hker e1
  have e3 : (x : V ≃ₗ[ZMod 2] V) * y * (x : V ≃ₗ[ZMod 2] V)⁻¹ = y := congrArg Subtype.val e2
  obtain ⟨X, hX⟩ : ∃ X : V ≃ₗ[ZMod 2] V, X = (x : V ≃ₗ[ZMod 2] V) := ⟨_, rfl⟩
  rw [← hX] at e3 ⊢
  calc X * y = (X * y * X⁻¹) * X := by group
    _ = y * X := by rw [e3]

theorem le_of_abar_le_lbar {H L A Mo : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I)
    (hker : (actOn L A I hAn hI L le_sup_left).ker = ⊥)
    (hAbar : (actOn L A I hAn hI A le_sup_right).range ≤
      (actOn L A I hAn hI L le_sup_left).range)
    (hLH : L ≤ H) (hAH : A ≤ H) (hMoL : ∀ y ∈ Mo, ∀ l ∈ L, l * y = y * l)
    (hMoA : ∀ y ∈ Mo, ∀ a ∈ A, y * a = a * y)
    (hcent : ∀ x ∈ H, (∀ y ∈ L, x * y = y * x) → (∀ y ∈ Mo, x * y = y * x) → x = 1) :
    A ≤ L := by
  intro a ha
  obtain ⟨l, hl⟩ : ∃ l : ↥L, actOn L A I hAn hI L le_sup_left l =
      actOn L A I hAn hI A le_sup_right ⟨a, ha⟩ := hAbar ⟨⟨a, ha⟩, rfl⟩
  let x : ↥(L ⊔ A) := ⟨(l : V ≃ₗ[ZMod 2] V)⁻¹ * a,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left l.2)) (Subgroup.mem_sup_right ha)⟩
  have hx1 : actW L A I hAn hI x = 1 := by
    have e : x = (⟨(l : V ≃ₗ[ZMod 2] V), Subgroup.mem_sup_left l.2⟩ : ↥(L ⊔ A))⁻¹ *
        ⟨a, Subgroup.mem_sup_right ha⟩ := rfl
    have h1 : actW L A I hAn hI ⟨(l : V ≃ₗ[ZMod 2] V), Subgroup.mem_sup_left l.2⟩ =
        actW L A I hAn hI ⟨a, Subgroup.mem_sup_right ha⟩ := hl
    rw [e, map_mul, map_inv, h1, inv_mul_cancel]
  have hxc := centralizes_of_actW_eq_one hAn hI hker hx1
  have hxH : (l : V ≃ₗ[ZMod 2] V)⁻¹ * a ∈ H := H.mul_mem (H.inv_mem (hLH l.2)) (hAH ha)
  have hx : (l : V ≃ₗ[ZMod 2] V)⁻¹ * a = 1 := by
    refine hcent _ hxH hxc fun y hy => ?_
    have h1 : (l : V ≃ₗ[ZMod 2] V)⁻¹ * y = y * (l : V ≃ₗ[ZMod 2] V)⁻¹ :=
      hMoL y hy _ (L.inv_mem l.2)
    have h2 : a * y = y * a := (hMoA y hy a ha).symm
    calc (l : V ≃ₗ[ZMod 2] V)⁻¹ * a * y = (l : V ≃ₗ[ZMod 2] V)⁻¹ * (a * y) := by group
      _ = (l : V ≃ₗ[ZMod 2] V)⁻¹ * (y * a) := by rw [h2]
      _ = ((l : V ≃ₗ[ZMod 2] V)⁻¹ * y) * a := by group
      _ = (y * (l : V ≃ₗ[ZMod 2] V)⁻¹) * a := by rw [h1]
      _ = y * ((l : V ≃ₗ[ZMod 2] V)⁻¹ * a) := by group
  have : a = (l : V ≃ₗ[ZMod 2] V) := by
    have := congrArg ((l : V ≃ₗ[ZMod 2] V) * ·) hx
    simpa using this
  rw [this]
  exact l.2

end Alt

end CFSG.QuasithinUnique.Setup.Lift

module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.AE (AEQ mkQ memBar Wr)
open CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL (layerX_le_centralizer conjSub_layerX_of_mem le_layerX
  mem_coreHull_of_mem_layerX layerBarHullEquiv_mk)
open scoped commutatorElement


section KerMap

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ c : G}

structure KerMap (Ω : Set (Subgroup G)) (c : G) (B : Type) [Group B] where
  f : G → B
  mul : ∀ y₁ ∈ layerX Ω c, ∀ y₂ ∈ layerX Ω c, f (y₁ * y₂) = f y₁ * f y₂
  ker : ∀ y ∈ layerX Ω c, (f y = 1 ↔ y ∈ oddCoreIn (layerX Ω c))
  surj : ∀ w : B, ∃ y ∈ layerX Ω c, f y = w

namespace KerMap

variable {B : Type} [Group B] (Kf : KerMap Ω c B)

theorem one : Kf.f 1 = 1 := by
  have h := Kf.mul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
  rw [mul_one] at h
  exact left_eq_mul.mp h

theorem inv {y : G} (hy : y ∈ layerX Ω c) : Kf.f y⁻¹ = (Kf.f y)⁻¹ := by
  have h := Kf.mul y hy y⁻¹ ((layerX Ω c).inv_mem hy)
  rw [mul_inv_cancel, Kf.one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem f_conj {n y : G} (hn : n ∈ layerX Ω c) (hy : y ∈ layerX Ω c) :
    Kf.f (n * y * n⁻¹) = Kf.f n * Kf.f y * (Kf.f n)⁻¹ := by
  rw [Kf.mul _ ((layerX Ω c).mul_mem hn hy) _ ((layerX Ω c).inv_mem hn), Kf.mul _ hn _ hy, Kf.inv hn]

theorem inj_P {P : Subgroup G} (hPX : P ≤ layerX Ω c) (hP : IsPGroup 2 ↥P) {y : G} (hy : y ∈ P)
    (h : Kf.f y = 1) : y = 1 :=
  eq_one_of_isPGroup_of_odd hP (odd_card_oddCoreIn _) hy ((Kf.ker y (hPX hy)).1 h)

theorem inj_P2 {P : Subgroup G} (hPX : P ≤ layerX Ω c) (hP : IsPGroup 2 ↥P) {y₁ y₂ : G} (h₁ : y₁ ∈ P)
    (h₂ : y₂ ∈ P) (h : Kf.f y₁ = Kf.f y₂) : y₁ = y₂ := by
  have e : Kf.f (y₁⁻¹ * y₂) = 1 := by
    rw [Kf.mul _ (hPX (P.inv_mem h₁)) _ (hPX h₂), Kf.inv (hPX h₁), h, inv_mul_cancel]
  exact inv_mul_eq_one.mp (Kf.inj_P hPX hP (P.mul_mem (P.inv_mem h₁) h₂) e)

theorem lift {P : Subgroup G} (hPX : P ≤ layerX Ω c) (hP : IsPGroup 2 ↥P) {u : B}
    (hnorm : ∀ y ∈ P, ∃ y' ∈ P, Kf.f y' = u * Kf.f y * u⁻¹) :
    ∃ n ∈ layerX Ω c, Kf.f n = u ∧ ∀ y ∈ P, n * y * n⁻¹ ∈ P := by
  obtain ⟨x₀, hx₀, hx₀u⟩ := Kf.surj u
  have hxP : ∀ y ∈ P, ∃ y' ∈ P, ∃ n ∈ oddCoreIn (layerX Ω c), x₀ * y * x₀⁻¹ = y' * n := by
    intro y hy
    obtain ⟨y', hy', hye⟩ := hnorm y hy
    refine ⟨y', hy', y'⁻¹ * (x₀ * y * x₀⁻¹), ?_, by group⟩
    have hX : x₀ * y * x₀⁻¹ ∈ layerX Ω c :=
      (layerX Ω c).mul_mem ((layerX Ω c).mul_mem hx₀ (hPX hy)) ((layerX Ω c).inv_mem hx₀)
    have hy'X := hPX hy'
    have hm : y'⁻¹ * (x₀ * y * x₀⁻¹) ∈ layerX Ω c := (layerX Ω c).mul_mem ((layerX Ω c).inv_mem hy'X) hX
    rw [← Kf.ker _ hm, Kf.mul _ ((layerX Ω c).inv_mem hy'X) _ hX, Kf.inv hy'X, Kf.f_conj hx₀ (hPX hy),
      hx₀u, hye]
    group
  obtain ⟨o, ho, hon⟩ := frattini_G (X := layerX Ω c) (N := oddCoreIn (layerX Ω c)) (P := P)
    (oddCoreIn_le _) hPX (fun x hx n hn => conj_mem_oddCoreIn hx hn) (odd_card_oddCoreIn _) hP hx₀ hxP
  have hoX := oddCoreIn_le _ ho
  have hnX : o⁻¹ * x₀ ∈ layerX Ω c := (layerX Ω c).mul_mem ((layerX Ω c).inv_mem hoX) hx₀
  refine ⟨o⁻¹ * x₀, hnX, ?_, hon⟩
  rw [Kf.mul _ ((layerX Ω c).inv_mem hoX) _ hx₀, Kf.inv hoX, (Kf.ker o hoX).2 ho, inv_one, one_mul, hx₀u]

end KerMap

namespace Lay

variable (Λ : Lay Ω K K' W S R R' z t u₁ u₂ c)
include Λ

open Classical in
@[expose] noncomputable def kerF (y : G) : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c) :=
  if hy : y ∈ layerX Ω c then Λ.lbe (QuotientGroup.mk ⟨y, hy⟩) else 1

theorem kerF_of_mem {y : G} (hy : y ∈ layerX Ω c) :
    Λ.kerF y = Λ.lbe (QuotientGroup.mk ⟨y, hy⟩) := by
  unfold kerF
  rw [dif_pos hy]

@[expose] noncomputable def kerMap :
    KerMap Ω c (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) where
  f := Λ.kerF
  mul := fun y₁ h₁ y₂ h₂ => by
    have h12 : y₁ * y₂ ∈ layerX Ω c := Subgroup.mul_mem _ h₁ h₂
    rw [Λ.kerF_of_mem h₁, Λ.kerF_of_mem h₂, Λ.kerF_of_mem h12]
    have : (QuotientGroup.mk (⟨y₁ * y₂, h12⟩ : ↥(layerX Ω c)) : layerBar Ω c) =
        QuotientGroup.mk ⟨y₁, h₁⟩ * QuotientGroup.mk ⟨y₂, h₂⟩ := rfl
    rw [this, map_mul]
  ker := fun y hy => by
    rw [Λ.kerF_of_mem hy, MulEquiv.map_eq_one_iff]
    exact mk_eq_one_iff (layerX Ω c) ⟨y, hy⟩
  surj := fun w => by
    obtain ⟨b', hb'⟩ := Λ.lbe.surjective w
    obtain ⟨⟨y, hy⟩, hy'⟩ := QuotientGroup.mk_surjective b'
    refine ⟨y, hy, ?_⟩
    rw [Λ.kerF_of_mem hy, hy', hb']

theorem kerMap_f {y : G} (hy : y ∈ layerX Ω c) (hC : y ∈ Subgroup.centralizer ({c} : Set G))
    (hY : (⟨y, hC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c) :
    Λ.kerMap.f y = QuotientGroup.mk (⟨⟨y, hC⟩, hY⟩ : ↥(coreHull Ω c)) := by
  show Λ.kerF y = _
  rw [Λ.kerF_of_mem hy]
  exact layerBarHullEquiv_mk Λ.hΩ Λ.hc2' Λ.h2 ⟨y, hy⟩

end Lay

end KerMap

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

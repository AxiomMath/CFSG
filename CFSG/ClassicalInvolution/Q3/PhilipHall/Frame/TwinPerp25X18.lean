module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25E0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X10
public import CFSG.ClassicalInvolution.Q3.Q3T7P25U02

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL
open scoped MatrixGroups


section Lift

theorem Om6mData.congr_equiv {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y']
    (e : Y ≃* Y') {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z a₀ b₀ : Y}
    (h : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Om6mData Y Φ A A' z a₀ b₀) :
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Om6mData Y' (Subgroup.map e.toMonoidHom '' Φ)
      (A.map e.toMonoidHom) (A'.map e.toMonoidHom) (e z) (e a₀) (e b₀) where
  lie := by
    obtain ⟨D, hD1, i, hi⟩ := h.lie
    exact ⟨lieSystemDataMap e D, hD1, i, hi⟩
  twin := by
    have t := h.twin
    refine ⟨⟨A, t.hA, rfl⟩, ⟨A', t.hA', rfl⟩, fun hEq => t.ne (Subgroup.map_injective e.injective hEq),
      isUniqueInvolution_map_equiv e t.hzA, isUniqueInvolution_map_equiv e t.hzA',
      ⟨a₀, t.ha₀, rfl⟩, ⟨b₀, t.hb₀, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, t.ha₀sq]
    · rw [← map_mul, t.hb₀sq]
    · rintro M ⟨M₀, hM₀, rfl⟩ hM
      rw [t.nbA M₀ hM₀ (mem_omegaNbr_of_map_equiv e hM₀ hM)]
    · rintro M ⟨M₀, hM₀, rfl⟩ hM
      rw [t.nbA' M₀ hM₀ (mem_omegaNbr_of_map_equiv e hM₀ hM)]
  conj := by
    rintro _ ⟨J, hJ, rfl⟩ y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    refine ⟨conjSub y J, h.conj J hJ y, ?_⟩
    exact (conjSub_map e.toMonoidHom y J).symm

end Lift

section TL

structure TwinLift {Y : Type} [Group Y] [Finite Y] {E E' : Type} (e : E → Y) (e' : E' → Y) (zb : Y)
    (P : Subgroup (MulAut Y)) where
  Φ : Set (Subgroup Y)
  A : Subgroup Y
  A' : Subgroup Y
  z' : Y
  a₀ : Y
  b₀ : Y
  hz : z' = zb
  om6 : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Om6mData Y Φ A A' z' a₀ b₀
  eA : ↥A ≃* SL(2, ZMod 3)
  eA' : ↥A' ≃* SL(2, ZMod 3)
  he : ∀ r, e r ∈ A
  he' : ∀ r, e' r ∈ A'
  hQ : ∀ a ∈ A, a ^ 4 = 1 → ∃ r, a = e r
  hQ' : ∀ a ∈ A', a ^ 4 = 1 → ∃ r, a = e' r
  hCA : ∀ a ∈ A, ∀ r, a * e' r = e' r * a
  hCA' : ∀ a ∈ A', ∀ r, a * e r = e r * a
  hC : ∀ c : Y, (∀ r, c * e' r = e' r * c) → (∀ a ∈ A, c * a * c⁻¹ ∈ A) ∧ (∀ a ∈ A', c * a = a * c)
  hC' : ∀ c : Y, (∀ r, c * e r = e r * c) → (∀ a ∈ A', c * a * c⁻¹ ∈ A') ∧ (∀ a ∈ A, c * a = a * c)
  hfix : ∀ β ∈ P, (∀ y ∈ A, β y = y) ∧ ∀ y ∈ A', β y = y

end TL

section Map

variable {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y'] {E E' : Type}
  {e : E → Y} {e' : E' → Y} {f : E → Y'} {f' : E' → Y'} {zb : Y} {zb' : Y'} {P : Subgroup (MulAut Y)}

noncomputable def TwinLift.map (T : TwinLift e e' zb P) (σ : Y ≃* Y') (h : ∀ r, σ (e r) = f r)
    (h' : ∀ r, σ (e' r) = f' r) (hz : σ zb = zb') {P' : Subgroup (MulAut Y')}
    (hP : P' = P.map (MulAut.congr σ).toMonoidHom) : TwinLift f f' zb' P' where
  Φ := Subgroup.map σ.toMonoidHom '' T.Φ
  A := T.A.map σ.toMonoidHom
  A' := T.A'.map σ.toMonoidHom
  z' := σ T.z'
  a₀ := σ T.a₀
  b₀ := σ T.b₀
  hz := by rw [T.hz]; exact hz
  om6 := Om6mData.congr_equiv σ T.om6
  eA := (Subgroup.equivMapOfInjective T.A σ.toMonoidHom σ.injective).symm.trans T.eA
  eA' := (Subgroup.equivMapOfInjective T.A' σ.toMonoidHom σ.injective).symm.trans T.eA'
  he := fun r => ⟨e r, T.he r, h r⟩
  he' := fun r => ⟨e' r, T.he' r, h' r⟩
  hQ := by
    rintro _ ⟨a, ha, rfl⟩ h4
    have h4' : a ^ 4 = 1 := σ.injective (by
      rw [map_pow, map_one]
      exact h4)
    obtain ⟨r, hr⟩ := T.hQ a ha h4'
    exact ⟨r, by rw [← h r, ← hr]; rfl⟩
  hQ' := by
    rintro _ ⟨a, ha, rfl⟩ h4
    have h4' : a ^ 4 = 1 := σ.injective (by
      rw [map_pow, map_one]
      exact h4)
    obtain ⟨r, hr⟩ := T.hQ' a ha h4'
    exact ⟨r, by rw [← h' r, ← hr]; rfl⟩
  hCA := by
    rintro _ ⟨a, ha, rfl⟩ r
    rw [← h' r]
    show σ a * σ (e' r) = σ (e' r) * σ a
    rw [← map_mul, ← map_mul, T.hCA a ha r]
  hCA' := by
    rintro _ ⟨a, ha, rfl⟩ r
    rw [← h r]
    show σ a * σ (e r) = σ (e r) * σ a
    rw [← map_mul, ← map_mul, T.hCA' a ha r]
  hC := by
    intro c hc
    set c₀ := σ.symm c with hc₀
    have H : ∀ r, c₀ * e' r = e' r * c₀ := by
      intro r
      apply σ.injective
      rw [map_mul, map_mul, hc₀, MulEquiv.apply_symm_apply, h' r]
      exact hc r
    obtain ⟨H1, H2⟩ := T.hC c₀ H
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨c₀ * a * c₀⁻¹, H1 a ha, ?_⟩
      show σ (c₀ * a * c₀⁻¹) = c * σ a * c⁻¹
      rw [map_mul, map_mul, map_inv, hc₀, MulEquiv.apply_symm_apply]
    · rintro _ ⟨a, ha, rfl⟩
      have := H2 a ha
      show c * σ a = σ a * c
      apply σ.symm.injective
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply, ← hc₀]
      exact this
  hC' := by
    intro c hc
    set c₀ := σ.symm c with hc₀
    have H : ∀ r, c₀ * e r = e r * c₀ := by
      intro r
      apply σ.injective
      rw [map_mul, map_mul, hc₀, MulEquiv.apply_symm_apply, h r]
      exact hc r
    obtain ⟨H1, H2⟩ := T.hC' c₀ H
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨c₀ * a * c₀⁻¹, H1 a ha, ?_⟩
      show σ (c₀ * a * c₀⁻¹) = c * σ a * c⁻¹
      rw [map_mul, map_mul, map_inv, hc₀, MulEquiv.apply_symm_apply]
    · rintro _ ⟨a, ha, rfl⟩
      have := H2 a ha
      show c * σ a = σ a * c
      apply σ.symm.injective
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply, ← hc₀]
      exact this
  hfix := by
    intro β' hβ'
    rw [hP] at hβ'
    obtain ⟨β, hβ, rfl⟩ := hβ'
    obtain ⟨H1, H2⟩ := T.hfix β hβ
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      show (MulAut.congr σ β) (σ a) = σ a
      rw [congr_apply', MulEquiv.symm_apply_apply, H1 a ha]
    · rintro _ ⟨a, ha, rfl⟩
      show (MulAut.congr σ β) (σ a) = σ a
      rw [congr_apply', MulEquiv.symm_apply_apply, H2 a ha]

end Map

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

module

public import CFSG.LargeExtraspecial.S12InspFamTools
public import CFSG.LargeExtraspecial.OutSix
public import CFSG.LargeExtraspecial.S12InspPSLPair
public import CFSG.LargeExtraspecial.S4Weak
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem psl_Lbar_apply_sub_mem_span {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar g) {u : S.Qt}
    (hu : u ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ span (ZMod 2) {S.cl (g * S.z * g⁻¹)} := by
  obtain ⟨x, hxX, hxQ, rfl⟩ := S.mem_clSub_iff.mp hu
  by_cases h0 : S.cl x = 0
  · rw [h0, map_zero, sub_zero]
    exact zero_mem _
  by_cases ha : S.cl x = S.cl (g * S.z * g⁻¹)
  · rw [ha, S.s12_Lbar_apply_cl_a haQ hℓ, sub_self]
    exact zero_mem _
  obtain ⟨y, hy, rfl⟩ := S.s12_mem_Lbar.mp hℓ
  rw [S.ρ_cl _ hxQ, mem_span_singleton_iff]
  rcases (S.conj_L0_of_mem_QG_inf_Qa haQ hne hxX ⟨h0, ha⟩).1 y hy with h | h
  · left
    change S.cl (y * x * y⁻¹) - S.cl x = 0
    rw [h, sub_self]
  · right
    change S.cl (y * x * y⁻¹) - S.cl x = _
    rw [h, S.cl_mul haQ hxQ, add_sub_cancel_right]

theorem psl_Lbar_comm_le_of_transitive {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {H : Submodule (ZMod 2) S.Qt}
    (hH : ∀ h ∈ H, polar S.q (S.cl (g * S.z * g⁻¹)) h = 0) {c : S.Qt}
    (hca : ∀ v ∈ H, v ∈ span (ZMod 2) {S.cl (g * S.z * g⁻¹)} → v ∈ span (ZMod 2) {c})
    {L₁ K : Set S.O} (hL : ∀ ℓ ∈ L₁, ℓ ∈ S.Lbar g) (hLH : ∀ ℓ ∈ L₁, ∀ h ∈ H,
      (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) h ∈ H) (hLc : ∀ ℓ ∈ L₁, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) c = c)
    (hKH : ∀ k ∈ K, ∀ h ∈ H, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) h ∈ H)
    (hKL : ∀ k ∈ K, ∀ ℓ ∈ L₁, k * ℓ * k⁻¹ ∈ L₁)
    (htr : ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ ∉ span (ZMod 2) {c} → h₂ ∉ span (ZMod 2) {c} →
      ∃ k ∈ K, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) h₁ = h₂) :
    ∀ ℓ ∈ L₁, ∀ h ∈ H, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) h - h ∈ span (ZMod 2) {c} := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ℓ₀, hℓ₀, h₀, hh₀, hu⟩ := hcon
  set u := (ℓ₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) h₀ - h₀ with hudef
  have huH : u ∈ H := H.sub_mem (hLH ℓ₀ hℓ₀ h₀ hh₀) hh₀
  have hD : ∀ h ∈ H, h ∉ span (ZMod 2) {c} → h ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    intro h hh hhc
    obtain ⟨k, hk, hku⟩ := htr u huH h hh hu hhc
    have hkh₀ : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) h₀ ∈ H := hKH k hk h₀ hh₀
    have e : h = ((k * ℓ₀ * k⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) h₀) -
        (k : S.Qt ≃ₗ[ZMod 2] S.Qt) h₀ := by
      rw [← hku, hudef, map_sub, Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply, psl_inv_apply_apply]
    rw [e]
    exact S.s12_Lbar_apply_sub_mem haQ (hL _ (hKL k hk ℓ₀ hℓ₀)) (hH _ hkh₀)
  apply hu
  rw [hudef]
  by_cases hh₀c : h₀ ∈ span (ZMod 2) {c}
  · rw [mem_span_singleton_iff] at hh₀c
    rcases hh₀c with rfl | rfl
    · rw [map_zero, sub_zero]
      exact zero_mem _
    · rw [hLc ℓ₀ hℓ₀, sub_self]
      exact zero_mem _
  · exact hca _ huH (psl_Lbar_apply_sub_mem_span haQ hne (hL ℓ₀ hℓ₀) (hD h₀ hh₀ hh₀c))

namespace PSLPair

variable {g : G} {t : S.O} (P : S.PSLPair g t)

include P in
theorem relIndex_le_two (hS : S.S12Standing g t) (hn : 3 ≤ S.width) :
    (S.Xbar12 g).relIndex S.Mbar ≤ 2 := by
  obtain ⟨e⟩ := P.model
  have e' : S.Xbar12 g ≃* Matrix.ProjectiveSpecialLinearGroup (Fin S.width) (ZMod 2) :=
    (e.trans (CFSG.QuasithinUnique.Setup.Family.projEquiv S.width)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        S.width (ZMod 2)).symm
  have hO : Nat.card (Outer (S.Xbar12 g)) ∣ 2 := by
    rw [Nat.card_congr (equivalence e').toEquiv]
    exact S14.card_outer_psl_two_dvd hn
  have h1 := card_Mbar_dvd_card_Xbar12_mul_card_outer hS
  have h2 := s12_card_mul_relIndex_of_le (Xbar12_le_Mbar (S := S) (g := g))
  have hpos : 0 < Nat.card (S.Xbar12 g) := Nat.card_pos
  rw [← h2] at h1
  have h3 : (S.Xbar12 g).relIndex S.Mbar ∣ Nat.card (Outer (S.Xbar12 g)) :=
    (Nat.mul_dvd_mul_iff_left hpos).mp h1
  exact Nat.le_of_dvd (by norm_num) (h3.trans hO)

theorem eq_of_isInv {U : Submodule (ZMod 2) S.Qt} (hU : IsInv (S.actX12 g) U) (hUW : U ≤ P.W)
    (hU0 : U ≠ ⊥) : U = P.W := by
  refine le_antisymm hUW fun w hw => ?_
  by_cases hw0 : w = 0
  · rw [hw0]
    exact zero_mem _
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  obtain ⟨x, hx, hxu⟩ := P.exists_apply_eq (hUW hu) hw hu0 hw0
  rw [← hxu]
  exact hU ⟨x, hx⟩ u hu

theorem mem_Xbar12_of_apply_mem (hS : S.S12Standing g t) (hn : 3 ≤ S.width)
    (hred : ¬ S.IsReducible12) {m : S.O} (hm : m ∈ S.Mbar) {w : S.Qt} (hw : w ∈ P.W)
    (hw0 : w ≠ 0) (hmw : (m : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ P.W) : m ∈ S.Xbar12 g := by
  obtain ⟨m₀, rfl⟩ := hm
  set U := P.W.map ((S.ρ m₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap
  have hUi : IsInv (S.actX12 g) (U ⊓ P.W) := psl_isInv_inf (psl_isInv_map_rho P.inv m₀) P.inv
  have hU0 : U ⊓ P.W ≠ ⊥ := by
    intro h
    have : (S.ρ m₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ U ⊓ P.W := ⟨⟨w, hw, rfl⟩, hmw⟩
    rw [h, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at this
    exact hw0 this
  have hWU : P.W ≤ U := (P.eq_of_isInv hUi inf_le_right hU0).symm ▸ inf_le_left
  have hUW : U = P.W := (eq_of_le_of_finrank_eq hWU
    (LinearEquiv.finrank_map_eq _ P.W).symm).symm
  let K : Subgroup S.O :=
    { carrier := {x | x ∈ S.Mbar ∧ ∀ w ∈ P.W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ P.W ∧
        ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ P.W}
      mul_mem' := by
        rintro x y ⟨hx, hxW⟩ ⟨hy, hyW⟩
        refine ⟨S.Mbar.mul_mem hx hy, fun w hw => ⟨?_, ?_⟩⟩
        · rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
          exact (hxW _ (hyW w hw).1).1
        · rw [mul_inv_rev, Subgroup.coe_mul, LinearEquiv.mul_apply]
          exact (hyW _ (hxW w hw).2).2
      one_mem' := ⟨S.Mbar.one_mem, fun w hw => ⟨hw, by rw [inv_one]; exact hw⟩⟩
      inv_mem' := by
        rintro x ⟨hx, hxW⟩
        refine ⟨S.Mbar.inv_mem hx, fun w hw => ⟨(hxW w hw).2, ?_⟩⟩
        rw [inv_inv]
        exact (hxW w hw).1 }
  have hXK : S.Xbar12 g ≤ K := fun x hx =>
    ⟨Xbar12_le_Mbar hx, fun w hw => ⟨P.apply_mem hx hw, P.apply_mem ((S.Xbar12 g).inv_mem hx) hw⟩⟩
  have hKM : K ≤ S.Mbar := fun x hx => hx.1
  have hKne : ¬ S.Mbar ≤ K := by
    intro h
    refine hred ⟨P.W, fun h0 => P.c_ne ((Submodule.mem_bot _).mp (h0 ▸ P.hc)),
      fun h1 => ?_, fun m' v hv => ((h ⟨m', rfl⟩).2 v hv).1⟩
    have := P.dim
    rw [h1, finrank_top, S.finrank_Qt_eq_two_mul_width] at this
    omega
  have hmK : S.ρ m₀ ∈ K := by
    refine ⟨⟨m₀, rfl⟩, fun v hv => ⟨?_, ?_⟩⟩
    · rw [← hUW]
      exact ⟨v, hv, rfl⟩
    · rw [← hUW] at hv
      obtain ⟨v', hv', rfl⟩ := hv
      change (((S.ρ m₀)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((S.ρ m₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v') ∈ P.W
      rw [psl_inv_apply_apply]
      exact hv'
  have hidx := P.relIndex_le_two hS hn
  have hmul : (S.Xbar12 g).relIndex K * K.relIndex S.Mbar = (S.Xbar12 g).relIndex S.Mbar :=
    Subgroup.relIndex_mul_relIndex _ _ _ hXK hKM
  have hr0 : (S.Xbar12 g).relIndex S.Mbar ≠ 0 := by
    intro h
    have h2 := s12_card_mul_relIndex_of_le (Xbar12_le_Mbar (S := S) (g := g))
    rw [h, mul_zero] at h2
    exact (Nat.card_pos (α := S.Mbar)).ne' h2.symm
  rw [← hmul] at hr0 hidx
  have hK2 : 2 ≤ K.relIndex S.Mbar := by
    have h1 : K.relIndex S.Mbar ≠ 1 := fun h => hKne (relIndex_eq_one.mp h)
    have h0 : K.relIndex S.Mbar ≠ 0 := right_ne_zero_of_mul hr0
    omega
  have hXK1 : (S.Xbar12 g).relIndex K = 1 := by
    have h0 : (S.Xbar12 g).relIndex K ≠ 0 := left_ne_zero_of_mul hr0
    have h2 : (S.Xbar12 g).relIndex K * 2 ≤ 2 :=
      le_trans (Nat.mul_le_mul_left _ hK2) hidx
    omega
  exact relIndex_eq_one.mp hXK1 hmK

theorem exists_move {H : Submodule (ZMod 2) S.Qt} (hHW : H ≤ P.W) {c : S.Qt} (hc : c ∈ H)
    {h₁ h₂ : S.Qt} (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ H) (hh₁c : h₁ ∉ span (ZMod 2) {c})
    (hh₂c : h₂ ∉ span (ZMod 2) {c}) :
    ∃ x ∈ S.Xbar12 g, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) c = c ∧
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) h₁ = h₂ ∧
      ∀ w ∈ P.W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ span (ZMod 2) {h₂ - h₁} := by
  have hnot : h₁ ∉ span (ZMod 2) {c, h₂ - h₁} := by
    rw [mem_span_pair_iff]
    rintro (h | h | h | h)
    · exact hh₁c (by rw [h]; exact zero_mem _)
    · exact hh₁c (by rw [h]; exact mem_span_singleton_self c)
    · apply hh₂c
      have : h₂ = h₁ + h₁ := by
        calc h₂ = (h₂ - h₁) + h₁ := (sub_add_cancel h₂ h₁).symm
          _ = h₁ + h₁ := by rw [← h]
      rw [this, self_add_self]
      exact zero_mem _
    · apply hh₂c
      have : h₂ = c := by
        have e : h₁ + h₁ = c + (h₂ - h₁) + h₁ := by rw [← h]
        rw [self_add_self, add_assoc, sub_add_cancel] at e
        calc h₂ = c + h₂ + c := by rw [add_comm c h₂, add_assoc, self_add_self, add_zero]
          _ = c := by rw [← e, zero_add]
      rw [this]
      exact mem_span_singleton_self c
  obtain ⟨ψ, hψ, hψ1⟩ := exists_functional hnot
  obtain ⟨x, hx, hxw⟩ := P.lift ψ (h₂ - h₁) (hHW (H.sub_mem hh₂ hh₁))
    (hψ _ (subset_span (by simp)))
  refine ⟨x, hx, ?_, ?_, fun w hw => ?_⟩
  · rw [hxw c (hHW hc), hψ c (subset_span (by simp)), zero_smul, add_zero]
  · rw [hxw h₁ (hHW hh₁), hψ1, one_smul, add_sub_cancel]
  · rw [hxw w hw, add_sub_cancel_left]
    exact smul_mem _ _ (mem_span_singleton_self _)

end PSLPair

end Setting

end CFSG.LargeExtraspecial

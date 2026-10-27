module

public import CFSG.GF2Type.Smith1979.W4C1Orth
public import CFSG.LargeExtraspecial.S12Main
public import CFSG.LargeExtraspecial.S6Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C1

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem faithful_of_card {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hX : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ (S.width + 1)) {s : S.O}
    (hs : s ∈ S.Lbar g)
    (hfix : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g), (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : s = 1 := by
  obtain ⟨y, hy, rfl⟩ := S.mem_Lbar_iff.mp hs
  have hyC : (y : G) ∈ S.CQa g :=
    S.mem_CQa_of_fix hne hy fun w hw => hfix _ (S.cl_mem_clSub hw hw.1)
  have hC := S.card_CQa_mul haQ
  rw [hX] at hC
  have hCX : Nat.card (S.CQa g) = Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := by
    rw [hX]
    refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ (S.width + 1)) ?_
    rw [hC, ← pow_add]
    congr 1
    ring
  have hle : S.QG ⊓ S.Qa g ≤ S.CQa g := by
    rw [← S.QG_inf_CQa hne]
    exact inf_le_right
  have heq : S.QG ⊓ S.Qa g = S.CQa g := eq_of_le_of_card_ge hle hCX.le
  rw [← heq] at hyC
  exact (S.ρ_eq_one_iff y).mpr hyC.1

@[expose] noncomputable def rhoM : S.Mbar →* (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  S.O.subtype.comp S.Mbar.subtype

theorem rhoM_injective : Function.Injective (rhoM S) :=
  S.O.subtype_injective.comp S.Mbar.subtype_injective

@[expose] noncomputable def Lgrp (g : G) : Subgroup S.Mbar :=
  (S.Lbar g).subgroupOf S.Mbar

theorem mem_Lgrp {g : G} {ℓ : S.Mbar} : ℓ ∈ Lgrp S g ↔ (ℓ : S.O) ∈ S.Lbar g :=
  Subgroup.mem_subgroupOf

theorem Lgrp_comm {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    ∀ a ∈ Lgrp S g, ∀ a' ∈ Lgrp S g, a * a' = a' * a := fun a ha a' ha' =>
  Subtype.ext (S.Lbar_comm haQ ((mem_Lgrp S).mp ha) ((mem_Lgrp S).mp ha'))

theorem Lgrp_sq {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) : ∀ a ∈ Lgrp S g, a * a = 1 :=
  fun a ha => Subtype.ext (by
    have h := S.sq_eq_one_of_mem_Lbar haQ ((mem_Lgrp S).mp ha)
    rw [pow_two] at h
    exact h)

theorem card_Lgrp {g : G} : Nat.card (Lgrp S g) = Nat.card (S.Lbar g) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S.Lbar_le_Mbar g)).toEquiv

theorem eight_le_card_Lgrp {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hw : S.width = 4) : 8 ≤ Nat.card (Lgrp S g) := by
  rw [card_Lgrp]
  have h1 := S.card_Lbar_ge haQ hne
  rw [hw] at h1
  exact le_of_eq_of_le (by norm_num) h1

theorem Lgrp_fix {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    ∀ ℓ ∈ Lgrp S g, rhoM S ℓ (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
  fun ℓ hℓ => S.s12_Lbar_apply_cl_a haQ ((mem_Lgrp S).mp hℓ)

theorem Lgrp_normalized {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hw : S.width = 4) : ∀ m : S.Mbar, rhoM S m (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) →
      ∀ ℓ ∈ Lgrp S g, m * ℓ * m⁻¹ ∈ Lgrp S g := by
  intro m hm ℓ hℓ
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp m.2
  have hfix : ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    rw [hh]
    exact hm
  have hnorm := (S.timmesfeld_12_4_1 haQ hne (by omega) h).mpr hfix
  rw [hh] at hnorm
  have h1 := (Subgroup.mem_normalizer_iff.mp hnorm (ℓ : S.O)).mp ((mem_Lgrp S).mp hℓ)
  exact (mem_Lgrp S).mpr h1

theorem card_Lgrp_mul {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hw : S.width = 4) :
    Nat.card (Lgrp S g) * 2 ^ (finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) + 1) = 2 ^ 8 := by
  have hE := S.card_QG_inf_Qa_eq haQ hne
  have hmul := S.card_Lbar_mul g
  have h8 : (2 : ℕ) ^ (2 * 4) = 2 ^ 8 := by norm_num
  rw [S.card_L0 haQ hne, hw, hE, h8] at hmul
  rw [card_Lgrp, pow_succ']
  exact hmul

theorem false_of_spSixSpin {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hred : ¬ S.IsReducible12)
    (hSp : S.S12SpSixSpin g) : False := by
  obtain ⟨hw, hXM, b, hb₁, hb₂, ⟨eX⟩⟩ := hSp
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hO : ∀ m : S.Mbar, rhoM S m ∈ TauCeti.QuadraticMap.orthogonalGroup S.q :=
    fun m => (m : S.O).2
  have hV : finrank (ZMod 2) S.Qt = 8 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hx0 : S.cl (g * S.z * g⁻¹) ≠ 0 := S.s12_cl_ne_zero_of_conj haQ hne
  have horb : ∃ m : S.Mbar, polar S.q (S.cl (g * S.z * g⁻¹))
      (rhoM S m (S.cl (g * S.z * g⁻¹))) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hred (S.s12_isReducible12_of_orbit hx0 fun m => hcon ⟨S.ρ m, ⟨m, rfl⟩⟩)
  have hfaith : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = 4 → ∀ ℓ ∈ Lgrp S g,
      (∀ v ∈ S.clSub (S.QG ⊓ S.Qa g), rhoM S ℓ v = v) → ℓ = 1 := by
    intro hk ℓ hℓ hfix
    have hX : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ (S.width + 1) := by
      rw [S.card_QG_inf_Qa_eq haQ hne, hk, hw]
      norm_num
    exact Subtype.ext (faithful_of_card S haQ hne hX ((mem_Lgrp S).mp hℓ) hfix)
  exact false_of_spSix_action (rhoM S) S.q_nondegenerate hV (rhoM_injective S) hO b hb₁ hb₂
    ((MulEquiv.subgroupCongr hXM.symm).trans eX) hx0
    ((S.q_cl_eq_zero_iff haQ).mpr (S.s12_conj_z_sq g)) horb (Lgrp S g) (Lgrp_comm S haQ)
    (Lgrp_sq S haQ) (eight_le_card_Lgrp S haQ hne hw) (Lgrp_fix S haQ)
    (Lgrp_normalized S haQ hne hw) (S.clSub (S.QG ⊓ S.Qa g)) (S6.cl_mem_clSub_self haQ)
    (fun v hv => S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne hv)
    (fun m hm v hv => S6.apply_mem_clSub_of_fix haQ hne m.2 hm hv)
    (fun ℓ hℓ v hv => S.s12_Lbar_apply_sub_mem haQ ((mem_Lgrp S).mp hℓ) hv)
    (card_Lgrp_mul S haQ hne hw) hfaith

theorem timmesfeld_12_16_of_C1 [IsSimpleGroup G]
    (hRI : RootInvolutionComponentsInput.{0}) (hARS : CFSG.Timmesfeld.ARSInput)
    (hTri : FischerTrialityInput) (hFischer : S12FischerStatement)
    (hInsp : Timmesfeld12_3InspectionInput) (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width)
    {t : S.O} (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.IsReducible12 ∨ S.S12OmegaPlusEight ∨ S.S12GammaLResidual g t := by
  rcases Setting.timmesfeld_12_16 (S := S) hRI hARS hTri hFischer hInsp h36 hSL haQ hne hn ht
    htA with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · by_cases hred : S.IsReducible12
    · exact Or.inl hred
    · exact (false_of_spSixSpin S haQ hne hred h).elim

end CFSG.GF2Type.Smith1979.W4C1

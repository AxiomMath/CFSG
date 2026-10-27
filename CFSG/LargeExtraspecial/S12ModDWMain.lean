module

public import CFSG.LargeExtraspecial.S12ModDW
public import CFSG.LargeExtraspecial.DW2AMain
public import CFSG.LargeExtraspecial.DW37Statement
public import CFSG.LargeExtraspecial.DWCaseII
public import CFSG.LargeExtraspecial.DWNormalFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable [IsSimpleGroup G]

theorem finrank_eq_widthN_of_nondeg
    (hARS : CFSG.Timmesfeld.ARSInput)
    (hInsp : DW2OutInspectionInputN) (hn : 2 ≤ S.width) (hP : NondegWeaklyClosed S) {g₀ : G}
    (hg₀Q : g₀ * S.z * g₀⁻¹ ∈ S.QG) (hg₀ : g₀ * S.z * g₀⁻¹ ≠ S.z)
    {W : Submodule (ZMod 2) S.Qt} (hi : IsMbarInvariant S W) (hs : ∀ v ∈ W, S.q v = 0)
    (h0 : W ≠ ⊥) : finrank (ZMod 2) W = S.width := by
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  by_cases hβ : ∀ v ∈ spanD S, S.q v = 0
  · exact finrank_eq_width_of_spanD_singular_of_nondeg hn hP hβ hg₀Q hg₀ hi hs h0
  push Not at hβ
  obtain ⟨v₀, hv₀D, hv₀q⟩ := hβ
  obtain ⟨W₁, hi₁, hs₁, hle, hmax⟩ := exists_maximal_singular hi hs
  obtain ⟨h, hhQ, hhW⟩ : ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ S.cl (h * S.z * h⁻¹) ∉ W₁ := by
    by_contra hall
    push Not at hall
    have hD : spanD S ≤ W₁ := by
      rw [spanD, Submodule.span_le]
      rintro _ ⟨k, hQ, rfl⟩
      exact hall k hQ
    exact hv₀q (hs₁ v₀ (hD hv₀D))
  have hW₁ : finrank (ZMod 2) W₁ = S.width := by
    refine le_antisymm (finrank_le_width_of_le_perp (le_perp_of_forall_q hs₁)) ?_
    by_contra hlt
    push Not at hlt
    exact Alpha.false_of_hypN_of_nondeg hARS hInsp ⟨hi₁, hs₁, fun hb => h0 (eq_bot_iff.mpr (hb ▸ hle)),
      hlt, hmax⟩ hn hP ⟨hhQ, hhW⟩
  have : CFSG.IsElementaryAbelian 2 (S.clPre W₁) :=
    isElementaryAbelian_clPre (le_perp_of_forall_q hs₁) hs₁
  have hMax : MaxEA S (S.clPre W₁) :=
    ⟨S.clPre_le_QG W₁, by rw [S.card_clPre, S.card_submodule, hW₁, pow_succ, mul_comm]⟩
  have hM₁ := M_le_normalizer_clPre hi₁
  have hsurj := (hMax.resAt_bijective_of_not_mem hM₁ hhQ fun hx => hhW hx.2).2
  have hcl := S.clSub_clPre W₁
  have hWW : W₁ ≤ W := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0]
      exact W.zero_mem
    obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have hw₀' : w₀ ∈ S.clSub (S.clPre W₁) := by rw [hcl]; exact hle hw₀
    have hw' : w ∈ S.clSub (S.clPre W₁) := by rw [hcl]; exact hw
    obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq_of_finrank rfl
      (x := (⟨w₀, hw₀'⟩ : S.clSub (S.clPre W₁))) (x' := ⟨w, hw'⟩)
      (fun h => hw₀0 (congrArg Subtype.val h)) (fun h => hw0 (congrArg Subtype.val h))
    obtain ⟨y, hy⟩ := hsurj g
    obtain ⟨m, hm⟩ := y.2
    have h1 : ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀ = w := by
      rw [← coe_resAt_apply hM₁ y ⟨w₀, hw₀'⟩, hy, hg]
    rw [← h1, ← hm]
    exact hi m w₀ hw₀
  rw [le_antisymm hle hWW]
  exact hW₁

theorem exists_maxEA_of_isReducibleN_of_nondeg
    (hARS : CFSG.Timmesfeld.ARSInput)
    (hInsp : DW2OutInspectionInputN) (hn : 2 ≤ S.width) (hP : NondegWeaklyClosed S) {g₀ : G}
    (hg₀Q : g₀ * S.z * g₀⁻¹ ∈ S.QG) (hg₀ : g₀ * S.z * g₀⁻¹ ≠ S.z) (hred : S.IsReducible) :
    ∃ A : Subgroup G, CFSG.IsElementaryAbelian 2 A ∧ MaxEA S A ∧
      S.M ≤ normalizer (A : Set G) := by
  obtain ⟨W, hW, htop, -, hc | ⟨-, hs, hEA⟩⟩ := reduction_of_simple (by omega) hred
  · exact absurd (hP W hW.2.1 hc.inf_eq_bot hW.1 htop g₀ hg₀Q) hg₀
  · refine ⟨S.clPre W, hEA, ⟨S.clPre_le_QG W, ?_⟩, M_le_normalizer_clPre hW.2.1⟩
    rw [S.card_clPre, S.card_submodule,
      finrank_eq_widthN_of_nondeg hARS hInsp hn hP hg₀Q hg₀ hW.2.1 hs hW.1, pow_succ,
      mul_comm]

theorem exists_maxEA_of_isReducibleN
    (hARS : CFSG.Timmesfeld.ARSInput)
    (hInsp : DW2OutInspectionInputN) (hn : 4 ≤ S.width) {g₀ : G}
    (hg₀Q : g₀ * S.z * g₀⁻¹ ∈ S.QG) (hg₀ : g₀ * S.z * g₀⁻¹ ≠ S.z) (hred : S.IsReducible) :
    ∃ A : Subgroup G, CFSG.IsElementaryAbelian 2 A ∧ MaxEA S A ∧
      S.M ≤ normalizer (A : Set G) :=
  exists_maxEA_of_isReducibleN_of_nondeg hARS hInsp (by omega)
    (nondegWeaklyClosed_of_four_le S hn) hg₀Q hg₀ hred

omit [IsSimpleGroup G] in
theorem dw37Statement_ofN
    (hARS : CFSG.Timmesfeld.ARSInput)
    (hInsp : DW2OutInspectionInputN) (hD : DempwolffLn2Input) : DW37Statement := by
  intro G _ _ _ S g h5 hgQ hg hred
  obtain ⟨A, hEA, hA, hM⟩ := exists_maxEA_of_isReducibleN hARS hInsp (by omega) hgQ hg hred
  have hC := hA.nonempty_centralizer_mulEquiv_of_mem_QG h5 hM hgQ hg
  exact hD.nonempty_mulEquiv_psl (by omega) G S.z (orderOf_eq_prime S.z_sq S.z_ne_one) hC

end CFSG.LargeExtraspecial.DW

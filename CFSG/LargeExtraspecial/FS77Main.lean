module

public import CFSG.LargeExtraspecial.FS77A8
public import CFSG.LargeExtraspecial.FS77Ord
public import CFSG.LargeExtraspecial.FS77PSU
public import CFSG.LargeExtraspecial.S12T36Core
public import CFSG.LargeExtraspecial.AS35Core
public import CFSG.LargeExtraspecial.S14W4LocLeaf

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.FS77

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open

section CaseA

variable {G : Type*} [Group G] [Finite G]

theorem CaseA.exists_totallySingular_four {S : Setting G} (D : CaseA S)
    {W : Submodule (ZMod 2) D.N} (hW3 : finrank (ZMod 2) W = 3) (hWq : ∀ v ∈ W, D.qN v = 0) :
    ∃ W' : Submodule (ZMod 2) S.Qt, finrank (ZMod 2) W' = 4 ∧ ∀ v ∈ W', S.q v = 0 := by
  set A : Submodule (ZMod 2) S.Qt := W.map D.N.subtype with hA
  have hAN : A ≤ D.N := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have he : D.P.e ∉ A := fun h => D.e_not_mem_N (hAN h)
  have he0 : D.P.e ≠ 0 := D.P.e_ne_zero
  refine ⟨A ⊔ (ZMod 2 ∙ D.P.e), ?_, ?_⟩
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq A (ZMod 2 ∙ D.P.e)
    have h2 : A ⊓ (ZMod 2 ∙ D.P.e) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx.2
      rcases Core.zmod2_cases c with rfl | rfl
      · rw [zero_smul]
        exact Submodule.zero_mem _
      · rw [one_smul] at hx
        exact absurd hx.1 he
    rw [h2, finrank_bot, add_zero, finrank_span_singleton he0, hA,
      Submodule.finrank_map_subtype_eq, hW3] at h1
    exact h1
  · intro v hv
    obtain ⟨y, hy, x, hx, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨w, hw, rfl⟩ := hy
    rw [QuadraticMap.map_add S.q, map_smul_eq_sq, D.P.Q_e, polar_smul_right_eq,
      Submodule.subtype_apply, D.polar_e_of_mem_N w.2, ← D.qN_apply, hWq w hw]
    ring

theorem caseA_false (S : Setting G) (hw : 4 ≤ S.width)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (htype : 5 ≤ S.width ∨ ¬ ∃ W : Submodule (ZMod 2) S.Qt,
      2 * finrank (ZMod 2) W = finrank (ZMod 2) S.Qt ∧ ∀ v ∈ W, S.q v = 0)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) : False := by
  have ha1 : g * S.z * g⁻¹ ≠ 1 := by
    intro h
    apply S.z_ne_one
    calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hq0 : S.q (S.cl (g * S.z * g⁻¹)) = 0 := by
    refine (S.q_cl_eq_zero_iff haQ).mpr ?_
    rw [pow_two]
    calc g * S.z * g⁻¹ * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ := by group
      _ = 1 := by rw [S.z_mul_z]; group
  have hcl0 : S.cl (g * S.z * g⁻¹) ≠ 0 := by
    rw [ne_eq, S.cl_eq_zero_iff haQ]
    rintro (h | h)
    exacts [ha1 h, hne h]
  obtain ⟨P, hP⟩ := exists_hypPair S.q_nondegenerate hq0 hcl0
  let D : CaseA S := ⟨g, haQ, hne, P, hP, hΩ, hw⟩
  obtain ⟨Y⟩ := D.exists_good
  have hdim : 8 ≤ finrank (ZMod 2) D.N ∨ (finrank (ZMod 2) D.N = 6 ∧
      ¬ ∃ W : Submodule (ZMod 2) D.N, finrank (ZMod 2) W = 3 ∧ ∀ v ∈ W, D.qN v = 0) := by
    rw [D.finrank_N]
    rcases htype with h5 | hminus
    · left
      omega
    · by_cases h5 : 5 ≤ S.width
      · left
        omega
      · right
        refine ⟨by omega, ?_⟩
        rintro ⟨W, hW3, hWq⟩
        obtain ⟨W', hW'4, hW'q⟩ := D.exists_totallySingular_four hW3 hWq
        exact hminus ⟨W', by rw [hW'4, S.finrank_Qt_eq_two_mul_width]; omega, hW'q⟩
  obtain ⟨e, hq, hB⟩ := exists_minus_sextuple D.qN_nondegenerate hdim
  exact Y.false_of_sextuple hq hB

end CaseA

@[expose] def FSmith1977cW4WeakInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 4 →
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
    (∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) ∨
      Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Co2)

theorem fSmith1977cW4WeakInput_of_core35 (h : S14.AschbacherSmith35Core) :
    FSmith1977cW4WeakInput := by
  intro G _ _ _ S hw _ hW
  rcases h G S (by omega) hW with h3 | ⟨-, hCo⟩
  · exact Or.inl h3
  · exact Or.inr hCo

theorem false_of_psu {G : Type*} [Group G] [Finite G] (S : Setting G) (hn : 2 ≤ S.width)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (e : G ≃* timmesfeldPSU (S.width + 2)) : False := by
  have h1 := two_pow_dvd_card_M S (by omega) hΩ
  have h2 := two_pow_le_of_mulEquiv_timmesfeldPSU (by omega) e S.M h1
  rw [show S.width + 2 - 1 = S.width + 1 by omega] at h2
  have h3 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp h2
  nlinarith

theorem false_of_co2 {G : Type*} [Group G] [Finite G]
    (S : Setting G) (hw : S.width = 4) (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (e : G ≃* CFSG.Blueprint.NativeSporadic.Co2) : False := by
  have h1 := two_pow_dvd_card_M S (by omega) hΩ
  rw [hw] at h1
  have h2 : 2 ^ 21 ∣ Nat.card G := dvd_trans h1 (Subgroup.card_subgroup_dvd_card S.M)
  rw [Nat.card_congr e.toEquiv] at h2
  have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
  rw [S14.factorization_card_Co2] at h3
  omega

theorem false_of_weaklyClosed_wide
    (h35 : S14.AschbacherThreeTranspositionCore) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (S : Setting G) (hn : 5 ≤ S.width)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) : False := by
  obtain ⟨e⟩ := psu_of_threeTransposition S (by omega) (h35 G S (by omega) (Or.inl hn) hW)
  exact false_of_psu S (by omega) hΩ e

theorem false_of_weaklyClosed_w4
    (hres : FSmith1977cW4WeakInput) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 4) (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) : False := by
  rcases hres G S hw hΩ hW with h3 | hCo
  · obtain ⟨e⟩ := psu_of_threeTransposition S (by omega) h3
    exact false_of_psu S (by omega) hΩ e
  · obtain ⟨e⟩ := hCo
    exact false_of_co2 S hw hΩ e

theorem fsmith1977cOmegaInput_of
    (h35 : S14.AschbacherThreeTranspositionCore) (hres : FSmith1977cW4WeakInput) :
    FSmith1977cOmegaInput := by
  intro G _ _ _ S hn hΩ
  by_cases hplus : S.width = 4 ∧ ∃ W : Submodule (ZMod 2) S.Qt,
      2 * finrank (ZMod 2) W = finrank (ZMod 2) S.Qt ∧ ∀ v ∈ W, S.q v = 0
  · exact hplus
  exfalso
  have htype : 5 ≤ S.width ∨ ¬ ∃ W : Submodule (ZMod 2) S.Qt,
      2 * finrank (ZMod 2) W = finrank (ZMod 2) S.Qt ∧ ∀ v ∈ W, S.q v = 0 := by
    by_cases h5 : 5 ≤ S.width
    · exact Or.inl h5
    · exact Or.inr fun h => hplus ⟨by omega, h⟩
  by_cases hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  · rcases (show 5 ≤ S.width ∨ S.width = 4 by omega) with h5 | h4
    · exact false_of_weaklyClosed_wide h35 S h5 hΩ hW
    · exact false_of_weaklyClosed_w4 hres S h4 hΩ hW
  · push Not at hW
    obtain ⟨g, hgQ, hgne⟩ := hW
    exact caseA_false S hn hΩ htype hgQ hgne

end CFSG.LargeExtraspecial.FS77

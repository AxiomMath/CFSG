module

public import CFSG.LargeExtraspecial.S12InspSplit
public import CFSG.LargeExtraspecial.S14Early
public import CFSG.LargeExtraspecial.O62Normalizer
public import CFSG.LargeExtraspecial.GLRMain
public import CFSG.LargeExtraspecial.S14W4LocMinus
public import CFSG.LargeExtraspecial.S14W4LocNoA2
public import CFSG.LargeExtraspecial.S14W4LocOrd
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S14W4LocTI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem claim_14_2_of_insp5 [IsSimpleGroup G] (hRI : RootInvolutionComponentsInput.{0})
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (hInsp : Insp5Input)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput) (hDW : DW.DW37Statement)
    (hn : 5 ≤ S.width) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    ¬ S.HasTypeAInL g ∨ Bridge.TimmesfeldConclusion G S.width S.Mbar := by
  by_cases hA : S.HasTypeAInL g
  · right
    obtain ⟨α, hαL, -, hαA⟩ := hA
    have ht : S.ρ α ∈ S.Lbar g := by
      rw [← S.map_La_eq_Lbar g]
      exact ⟨α, mem_subgroupOf.mpr hαL, rfl⟩
    rcases Setting.timmesfeld_12_16_of_insp5 hRI hARS hTri hFischer hInsp h36 hSL haQ hne hn ht
      hαA with hred | ⟨h4, -⟩ | hR | ⟨h4, -⟩
    · exact concl_of_isReducible hDW hn haQ hne hred
    · omega
    · exact (Setting.not_s12GammaLResidual haQ hne hn hR).elim
    · omega
  · exact Or.inl hA

namespace W4Loc

open CFSG.RankThree.OrthogonalInvolutions

variable {X : Type} [Group X] [Finite X] {T : Setting X} {R : Subgroup X}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {π : T.M →* (V ≃ₗ[ZMod 2] V)}

theorem card_omegaGroup_of_not_isPlus [FiniteDimensional (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (hV : finrank (ZMod 2) V = 6)
    (hq : q.polarBilin.Nondegenerate) (hm : ¬ O62.IsPlus q) :
    Nat.card (omegaGroup q hq) = 25920 := by
  obtain ⟨L, hL⟩ := O62.exists_linearEquiv_qMinus hV hq hm
  have h1 : {v | q v = 1}.ncard = 36 := by
    rw [← O62.ncard_qMinus]
    have he : {v | q v = 1} = L ⁻¹' {w | O62.qMinus w = 1} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, hL]
    rw [he, Set.ncard_preimage_of_injective_subset_range L.injective (by
      rw [L.surjective.range_eq]
      exact Set.subset_univ _)]
  rcases O62.ncard_singular_nonsingular hV hq with ⟨-, h⟩ | ⟨h0, -⟩
  · omega
  · have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    have hO := S12DW.card_orthogonalGroup_eq hq
    rcases O62.card_omegaGroup hV hq with h | h
    · exfalso
      have h2 := S12DW.card_orthogonalGroup_mul_ncard_eq hq (m := 3) (by rw [hV])
      have h3 : 2 ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1) = 1451520 := by decide
      rw [h3, hO, h] at h2
      have hS : {v | v ≠ 0 ∧ q v = 0} = {v | q v = 0} \ {0} := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
        tauto
      have : Finite V := Module.finite_of_finite (ZMod 2)
      have h0' : {v | v ≠ 0 ∧ q v = 0}.ncard + 1 = {v | q v = 0}.ncard := by
        rw [hS, Set.ncard_sdiff_singleton_add_one (by simp)]
      omega
    · exact h

theorem dvd_card_Mbar_of_minus (A : Act T R π) [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6) {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) (hR : (R.subgroupOf T.M).map π = omegaGroup q hq)
    (hm : ¬ O62.IsPlus q) : 25920 ∣ Nat.card T.Mbar := by
  have hle : omegaGroup q hq ≤ (πbar T π A.Q_le_ker).range := by
    rw [← hR]
    rintro _ ⟨r, -, rfl⟩
    exact ⟨⟨T.ρ r, ρ_mem_Mbar r⟩, πbar_ρ A.Q_le_ker r⟩
  rw [← card_omegaGroup_of_not_isPlus hV hq hm]
  exact (Subgroup.card_dvd_of_le hle).trans (Subgroup.card_range_dvd _)

theorem false_of_minus_of_insp4 (hM8 : WeaklyClosedE8Stmt)
    (hRI : RootInvolutionComponentsInput.{0}) (hARS : CFSG.Timmesfeld.ARSInput)
    (hTri : FischerTrialityInput) (hFischer : S12FischerStatement) (hInsp : Insp4Input)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput) (hTI : WeaklyClosedTITransitive.{0})
    [IsSimpleGroup X] (A : Act T R π) (hcard : Nat.card T.Qt = 2 ^ 8)
    (hirr' : ∀ W : Submodule (ZMod 2) T.Qt, W4Dict.IsInv T R W → W = ⊥ ∨ W = ⊤)
    [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V = 6)
    {q : QuadraticForm (ZMod 2) V} (hq : q.polarBilin.Nondegenerate)
    (hR : (R.subgroupOf T.M).map π = omegaGroup q hq)
    (hO : ∀ k, π k ∈ TauCeti.QuadraticMap.orthogonalGroup q) (hm : ¬ O62.IsPlus q)
    (hP : ∀ P : Subgroup T.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) (hw : T.width = 4)
    {g₀ : X} (haQ : g₀ * T.z * g₀⁻¹ ∈ T.QG) (hne : g₀ * T.z * g₀⁻¹ ≠ T.z) : False := by
  have hirr : ¬ T.IsReducible := not_isReducible_of_irr hirr'
  have hL : Lat T R := Or.inl hirr'
  by_cases hA : T.HasTypeAInL g₀
  · obtain ⟨α, hαL, -, hαA⟩ := hA
    have ht : T.ρ α ∈ T.Lbar g₀ := by
      rw [← T.map_La_eq_Lbar g₀]
      exact ⟨α, mem_subgroupOf.mpr hαL, rfl⟩
    rcases Setting.timmesfeld_12_16_of_insp4 hRI hARS hTri hFischer hInsp h36 hSL hw hP
      (dvd_card_Mbar_of_minus A hV hq hR hm) haQ hne ht hαA with hred | h8 | hΓ | hSp
    · exact hirr hred
    · exact false_of_two_pow_dvd hP (two_pow_dvd_of_omegaPlusEight T h8)
    · obtain ⟨x, hx⟩ := exists_orderOf_nine A.Q_le_ker hV hq hR hm
      exact false_of_gammaL_of_orderOf T hΓ hw x hx
    · exact false_of_two_pow_dvd hP (two_pow_dvd_of_spSixSpin T hSp)
  · exact hm (isPlus_of_cons311 hM8 A hcard hL hV hq hR hO haQ
      (cons311_of_w4 hTI (by omega) haQ hne hA hirr) hw)

end W4Loc

end CFSG.LargeExtraspecial.S14

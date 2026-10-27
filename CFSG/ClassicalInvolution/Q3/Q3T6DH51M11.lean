module

public import CFSG.ClassicalInvolution.Q3.Q3CHHyp51
public import CFSG.ClassicalInvolution.Q3.Q3NFPair
public import CFSG.ClassicalInvolution.Q3.Q3YAbs
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwE6
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3KCGen
public import CFSG.ClassicalInvolution.Q3.Q3NLFrame
public import CFSG.ClassicalInvolution.Q3.Q3TAxis
public import CFSG.ClassicalInvolution.Q3.Q3TIRed
public import CFSG.ClassicalInvolution.Q3.Q3WADict
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77


section Rows

theorem autOddFreeInner_range_of_model_ne_D4 {X : Type} [Group X] [Finite X] {c : CompData}
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (ht : IsFundTag t)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1)
    (hD4 : ¬ (t = .POmegaPlus ∧ n = 4)) (hc : c = CompData.model t n) (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) : AutOddFreeInner ↥ψ.range := by
  subst hc
  have hker' : ψ.rangeRestrict.ker ≤ Subgroup.center _ := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  by_cases hT : t = .trialityD4
  · subst hT
    have hn : n = 0 := hadm.2.2
    subst hn
    exact autOddFreeInnerTag_trialityD4 Nat.prime_three ht hadm _ ψ.rangeRestrict
      ψ.rangeRestrict_surjective hker'
  · exact autOddFreeInnerTag_of_not_D4 hD4 hT Nat.prime_three ht hadm _ ψ.rangeRestrict
      ψ.rangeRestrict_surjective hker'

end Rows

section M11

open CFSG.Blueprint

theorem m11_twin_collapse {X : Type} [Group X] {c : CompData} (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) (hc : c = CompData.m11) {R₁ R₂ : Subgroup c.G}
    (hR₁ : R₁ ∈ c.fund) (hR₂ : R₂ ∈ c.fund) {ζ : X} (h₁ : ζ ∈ R₁.map ψ) (h₂ : ζ ∈ R₂.map ψ)
    (hζ2 : ζ * ζ = 1) (hζ1 : ζ ≠ 1) (hc₁ : ∀ y ∈ R₁.map ψ, ζ * y = y * ζ)
    (hc₂ : ∀ y ∈ R₂.map ψ, ζ * y = y * ζ) : R₁ = R₂ := by
  subst hc
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_m11_eq_bot m11Facts).le
  obtain ⟨u, huR, hu⟩ := h₁
  obtain ⟨v, -, hv⟩ := h₂
  have huv : u = v := hinj (hu.trans hv.symm)
  subst huv
  have hu2 : u * u = 1 := hinj (by rw [map_mul, hu, map_one, hζ2])
  have hu1 : u ≠ 1 := fun h => hζ1 (by rw [← hu, h, map_one])
  have huc : ∀ y ∈ R₁, u * y = y * u := fun y hy =>
    hinj (by rw [map_mul, map_mul, hu]; exact hc₁ _ (Subgroup.mem_map_of_mem ψ hy))
  have hvc : ∀ y ∈ R₂, u * y = y * u := fun y hy =>
    hinj (by rw [map_mul, map_mul, hu]; exact hc₂ _ (Subgroup.mem_map_of_mem ψ hy))
  obtain ⟨w₁, hw₁⟩ := hR₁
  obtain ⟨w₂, hw₂⟩ := hR₂
  obtain ⟨φ₁, hφ₁⟩ := hw₁.exists_chart
  have hcu₁ : IsCentralInvolution R₁ u := ⟨huR, hu1, hu2, huc⟩
  have e₁ : w₁ = u := hφ₁.eq_of_central hw₁.isCentralInvolution hcu₁
  subst e₁
  have hR₂C : R₂ ≤ Subgroup.centralizer ({w₁} : Set ↥CFSG.Blueprint.NativeSporadic.M11) :=
    fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hvc y hy).symm
  exact Q3NF.m11_eq_of_le_centralizer hw₁ hw₂ hR₂C

section Glue

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {c b : G} {ι : Type}

set_option quotPrecheck false in
local notation "Yc" => centralizingLayer Φ {c}

theorem exists_fund_of_le_range3 {X : Type} [Group X] {Ψ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Ψ) {k : ι} {M : Subgroup X} (hM : M ∈ Ψ)
    (hMk : M ≤ (D.hom k).range) (hnc : ¬ M ≤ Subgroup.center X) :
    ∃ R ∈ (D.kind k).fund, M = R.map (D.hom k) := by
  obtain ⟨j, R, hR, hMR⟩ := D.fundamental M hM
  by_cases hjk : j = k
  · subst hjk
    exact ⟨R, hR, hMR⟩
  · exfalso
    apply hnc
    have h1 : M ≤ (D.hom j).range := hMR ▸ Subgroup.map_le_range _ _
    exact (le_inf hMk h1).trans (range_inf_range_le_center3 D (Ne.symm hjk))

theorem m11_twin_glue (hΦ : SecData3 c Φ)
    (D : LieSystemData3 ι (↥(Yc) ⧸
      classicalInvolutionOddCore ↥(Yc))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c}) (Yc))))
    {j : ι} (hj : D.kind j = CompData.m11) {M M' : Subgroup G} (hM : M ∈ Φ) (hM' : M' ∈ Φ)
    (hMj : modOdd c M ≤ secComp hΦ D j) (hM'j : modOdd c M' ≤ secComp hΦ D j)
    (hbU : IsUniqueInvolution M b) (hbU' : IsUniqueInvolution M' b) :
    modOdd c M = modOdd c M' := by
  have hN := normalizesLayer_of_secData3 hΦ
  have hθ : Function.Injective (sectionQuotientHom hN) := sectionQuotientHom_injective hN
  have hMc : M ∈ centMembers Φ c := ⟨hM, hΦ.le M hM⟩
  have hM'c : M' ∈ centMembers Φ c := ⟨hM', hΦ.le M' hM'⟩
  have hMY : M ≤ Yc := le_centLayer hMc
  have hM'Y : M' ≤ Yc := le_centLayer hM'c
  have hbY : b ∈ Yc := hMY hbU.mem
  have hfam : ∀ {N : Subgroup G}, N ∈ centMembers Φ c → N ≤ Yc → modOddIn (Yc) N ∈
      oddQuotientFamily (restrictFamily (centralizingMembers Φ {c}) (Yc)) :=
    fun hNc hNY => ⟨_, ⟨_, hNc, hNY, rfl⟩, rfl⟩
  have hle : ∀ {N : Subgroup G}, N ∈ centMembers Φ c → modOdd c N ≤ secComp hΦ D j →
      modOddIn (Yc) N ≤ (D.hom j).range := by
    intro N hNc hNj
    have h1 : (modOddIn (Yc) N).map (sectionQuotientHom hN) ≤ (D.hom j).range.map
        (sectionQuotientHom hN) := by
      rw [map_sectionQuotientHom_modOddIn hN hNc]
      exact hNj.trans (MonoidHom.range_comp (sectionQuotientHom hN) (D.hom j)).le
    exact (Subgroup.map_le_map_iff_of_injective hθ).mp h1
  obtain ⟨R₁, hR₁, hMR₁⟩ := exists_fund_of_le_range3 D (hfam hMc hMY) (hle hMc hMj)
    (not_le_center_of_secData3 hΦ _ (hfam hMc hMY))
  obtain ⟨R₂, hR₂, hMR₂⟩ := exists_fund_of_le_range3 D (hfam hM'c hM'Y) (hle hM'c hM'j)
    (not_le_center_of_secData3 hΦ _ (hfam hM'c hM'Y))
  have hbU_mem : ∀ {N : Subgroup G}, IsUniqueInvolution N b →
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(Yc)) ⟨b, hbY⟩ ∈ modOddIn (Yc) N :=
    fun hU => ⟨⟨b, hbY⟩, Subgroup.mem_subgroupOf.mpr hU.mem, rfl⟩
  have hcomm : ∀ {N : Subgroup G}, IsUniqueInvolution N b → ∀ y ∈ modOddIn (Yc) N,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(Yc)) ⟨b, hbY⟩ * y =
        y * QuotientGroup.mk' (classicalInvolutionOddCore ↥(Yc)) ⟨b, hbY⟩ := by
    intro N hU y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hU.commute_of_mem (Subgroup.mem_subgroupOf.mp hx))
  have hsq : QuotientGroup.mk' (classicalInvolutionOddCore ↥(Yc)) ⟨b, hbY⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(Yc)) ⟨b, hbY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨b, hbY⟩ * ⟨b, hbY⟩ : ↥(Yc)) = 1 := Subtype.ext hbU.sq
    rw [this, map_one]
  have hcoll : R₁ = R₂ := m11_twin_collapse (D.hom j) (D.ker_le_center j) hj hR₁ hR₂
    (hMR₁ ▸ hbU_mem hbU) (hMR₂ ▸ hbU_mem hbU') hsq
    (Q3Y.mk_ne_one_of_involution _ hbY hbU.sq hbU.ne_one)
    (fun y hy => hcomm hbU y (hMR₁ ▸ hy)) (fun y hy => hcomm hbU' y (hMR₂ ▸ hy))
  rw [← map_sectionQuotientHom_modOddIn hN hMc, ← map_sectionQuotientHom_modOddIn hN hM'c,
    hMR₁, hMR₂, hcoll]

end Glue

end M11

end CFSG.ClassicalInvolution.Q3.Q3T6D

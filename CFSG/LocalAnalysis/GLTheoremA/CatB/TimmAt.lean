module

public import CFSG.Milestones.CL_LIT_Timmesfeld_1978_large_extraspecial
public import CFSG.LocalAnalysis.GLTheoremA.S8.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmL2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmOmega
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.Timm

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LargeExtraspecial

@[expose] def TimmesfeldUnitaryAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → ∀ (w : ℕ), 12 ≤ w → Nonempty (G ≃* timmesfeldPSU (w + 2)) →
    ∀ M : Subgroup G, GLAIsMaxTwoLocal M → IsExtraSpec2 (pCoreOf 2 M) →
      Nat.card ↥(pCoreOf 2 M) = 2 ^ (1 + 2 * w) → (∃ g ∈ M, orderOf g = 5) →
      IsSimpleGroup ↥(oPrimeRes 5 (↥M ⧸ GLAPPrimeCore 5 ↥M))

theorem isSimpleGroup_oPrimeRes_of_pCore {C : Type} [Group C] [Finite C]
    (hcop : Nat.Coprime 5 (Nat.card (CFSG.pCore 2 C)))
    (hT : IsSimpleGroup ↥(oPrimeRes 5 (C ⧸ CFSG.pCore 2 C))) :
    IsSimpleGroup ↥(oPrimeRes 5 (C ⧸ GLAPPrimeCore 5 C)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hQL : CFSG.pCore 2 C ≤ GLAPPrimeCore 5 C := by
    show CFSG.pCore 2 C ≤ CFSG.pPrimeCore 5 C
    exact le_sSup ⟨inferInstance, hcop⟩
  let K : Subgroup (C ⧸ CFSG.pCore 2 C) := (GLAPPrimeCore 5 C).map (QuotientGroup.mk' (CFSG.pCore 2 C))
  haveI : K.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hKcop : Nat.Coprime 5 (Nat.card K) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) CFSG.pPrimeCore_coprime_card
  have hA := isSimpleGroup_oPrimeRes_quotient hKcop hT
  exact isSimpleGroup_oPrimeRes_of_mulEquiv
    (QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 C) (GLAPPrimeCore 5 C) hQL).symm hA


end CFSG.LocalAnalysis.GLTheoremA.Timm

namespace CFSG.LocalAnalysis.GLTheoremA.Timm

open Subgroup CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LargeExtraspecial

section Final


theorem timmesfeldAt_of_residual (hU : TimmesfeldUnitaryAt) : TimmesfeldAt := by
  intro G _ _ hsimple hnonab hchar M hM hext hcard hg5
  have hc : Nat.card (center ↥(pCoreOf 2 M)) = 2 := hext.2.2.2
  have hPM : pCoreOf 2 M ≤ M := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hPn : ∀ m ∈ M, ∀ x ∈ pCoreOf 2 M, m * x * m⁻¹ ∈ pCoreOf 2 M := by
    intro m hm x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨(⟨m, hm⟩ : M) * y * (⟨m, hm⟩ : M)⁻¹,
      (inferInstance : (CFSG.pCore 2 ↥M).Normal).conj_mem y hy _, ?_⟩
    simp
  obtain ⟨z, hzP, hz1, hz2, hzc⟩ := exists_central_involution hc
  have hMz : M = centralizer ({z} : Set G) :=
    eq_centralizer_of_isMaxTwoLocal hM hPM hPn hc hzP hz1 hz2 hzc
  subst hMz
  have hext' : CFSG.IsExtraspecialPGroup 2 ↥(CFSG.pCore 2 ↥(centralizer ({z} : Set G))) :=
    isExtraspecial_pCore_of_isExtraSpec2 hext
  let S := settingOf hchar hz2 hext'
  have hQ : Nat.card ↥(CFSG.pCore 2 ↥(centralizer ({z} : Set G))) = 2 ^ (1 + 2 * S.width) :=
    S.card_Q_eq
  have hcardQ : Nat.card ↥(pCoreOf 2 (centralizer ({z} : Set G))) = 2 ^ (1 + 2 * S.width) := by
    rw [← hQ]
    exact Nat.card_congr (Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥(centralizer ({z} : Set G)))
      (centralizer ({z} : Set G)).subtype (centralizer ({z} : Set G)).subtype_injective).symm.toEquiv
  have hw12 : 12 ≤ S.width := by
    have h25 : 2 ^ 25 ≤ 2 ^ (1 + 2 * S.width) := hcardQ ▸ hcard
    have : 25 ≤ 1 + 2 * S.width := (Nat.pow_le_pow_iff_right (by norm_num)).1 h25
    omega
  have hFS : timmesfeldFStar ↥(centralizer ({z} : Set G)) =
      CFSG.pCore 2 ↥(centralizer ({z} : Set G)) :=
    (CFSG.LargeExtraspecial.Bridge.Q_eq_timmesfeldFStar S).symm
  have hMbar : timmesfeldQuotientIso (timmesfeldFStar ↥(centralizer ({z} : Set G)))
      (↥(centralizer ({z} : Set G)) ⧸ CFSG.pCore 2 ↥(centralizer ({z} : Set G))) :=
    ⟨QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, by
      rw [hFS]
      exact QuotientGroup.ker_mk' _⟩
  have hconc := CFSG.Milestones.cl_lit_timmesfeld_1978_large_extraspecial G hnonab z hz2
    (CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_fstar S) S.width
    (CFSG.LargeExtraspecial.Bridge.card_fstar S) _ hMbar
  have hcopQ : Nat.Coprime 5 (Nat.card (CFSG.pCore 2 ↥(centralizer ({z} : Set G)))) := by
    rw [hQ]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hdiv : 5 ∣ Nat.card (↥(centralizer ({z} : Set G)) ⧸
      CFSG.pCore 2 ↥(centralizer ({z} : Set G))) := by
    obtain ⟨g, hgC, hg5'⟩ := hg5
    have hord : orderOf (⟨g, hgC⟩ : ↥(centralizer ({z} : Set G))) = 5 := by
      rw [← Subgroup.orderOf_coe]
      exact hg5'
    have h1 : 5 ∣ Nat.card ↥(centralizer ({z} : Set G)) := hord ▸ orderOf_dvd_natCard _
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.pCore 2 ↥(centralizer ({z} : Set G)))] at h1
    exact Nat.Coprime.dvd_of_dvd_mul_right hcopQ h1
  rcases hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · omega
  · rcases h2 with hL | hUn
    · obtain ⟨eL⟩ := hL
      exact absurd hM (L2.not_isMaxTwoLocal_centralizer_of_psl (n := S.width + 2) (by omega) eL hz2)
    · exact hU G hsimple hnonab hchar S.width hw12 hUn (centralizer ({z} : Set G)) hM hext hcardQ hg5
  · obtain ⟨-, -, q, hq, hiso⟩ := h3
    exact isSimpleGroup_oPrimeRes_of_pCore hcopQ
      (isSimpleGroup_oPrimeRes_of_alt3 hw12 hdiv hq hiso)
  · have := h4.1
    omega
  · have := h5.1
    omega
  · have := h6.1
    omega
  · haveI := h7.2.1
    exact isSimpleGroup_oPrimeRes_of_pCore hcopQ (isSimpleGroup_oPrimeRes_of_simple hdiv)
  · haveI := h8.1
    exact isSimpleGroup_oPrimeRes_of_pCore hcopQ (isSimpleGroup_oPrimeRes_of_simple hdiv)

end Final

end CFSG.LocalAnalysis.GLTheoremA.Timm

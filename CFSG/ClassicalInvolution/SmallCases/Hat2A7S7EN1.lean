module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EM00
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCollapse
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S3Aux
import CFSG.ClassicalInvolution.Q3.Q3CLBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7E.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Hat2A7S
open CFSG.ClassicalInvolution.Asc77 (omegaGen omegaGen_normal le_omegaGen oddCore_normal_eq_bot
  omegaNbr omegaStarNbr RSet USet AEmpty mem_RSet_of_isSylow2In)

section AEmpty

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaStarNbr_subset_omegaNbr_gen (hΩ : HypOmegaGen Ω)
    (hcl : ∀ L ∈ Ω, ∃ z : G, Hat2A7.IsClassical2A7 ⊤ L z) {M J : Subgroup G} (hM : M ∈ Ω)
    (hJ : J ∈ Ω) (h : J ∈ omegaStarNbr Ω M) : J ∈ omegaNbr Ω M := by
  obtain ⟨-, hJM, U, hU, hUJ, hUN⟩ := h
  obtain ⟨-, -, -, hU2, hcard⟩ := uset_data hcl hU
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  obtain ⟨hjU, huniq⟩ := involution_mem_of_card hj hUJ hcard
  obtain ⟨m, hm⟩ := hcl M hM
  obtain ⟨R, hR, hRc⟩ := exists_sylow_centralized hm hUN hU2 hjU huniq (by omega) hj.sq
    hj.ne_one
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hM hR
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ hRset).exists_not_commute
  have hnc : ∃ a ∈ R, a ∉ Subgroup.centralizer (M : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hxy₀ ((Subgroup.mem_centralizer_iff.mp (hcon x₀ hx₀)) y₀ (hR.1 hy₀)).symm
  have hN5 : ∀ v ∈ R, v ∉ Subgroup.centralizer (M : Set G) →
      v ∈ Subgroup.normalizer (J : Set G) := by
    intro v hv hvc
    refine hΩ.omega5 J hJ M hM hJM j hj v (hR.1 hv) ?_ ?_ (hRc v hv).symm
    · intro hall
      exact hvc (Subgroup.mem_centralizer_iff.mpr fun w hw => (hall w hw).symm)
    · exact hR.2.1.to_le (Subgroup.zpowers_le.mpr hv)
  have hRN : R ≤ Subgroup.normalizer (J : Set G) := by
    intro v hv
    by_cases hvc : v ∈ Subgroup.centralizer (M : Set G)
    · obtain ⟨a, ha, hac⟩ := hnc
      have haN := hN5 a ha hac
      have hva : v * a ∉ Subgroup.centralizer (M : Set G) := by
        intro hva
        apply hac
        have h1 := (Subgroup.centralizer (M : Set G)).mul_mem
          ((Subgroup.centralizer (M : Set G)).inv_mem hvc) hva
        simpa using h1
      have hvaN := hN5 (v * a) (R.mul_mem hv ha) hva
      have h2 := (Subgroup.normalizer (J : Set G)).mul_mem hvaN
        ((Subgroup.normalizer (J : Set G)).inv_mem haN)
      simpa using h2
    · exact hN5 v hv hvc
  have hMJ : M ∈ omegaNbr Ω J := ⟨hM, Ne.symm hJM, R, hRset, hR.1, hRN⟩
  exact Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ hM hMJ

theorem aEmpty_of_hm {Y : Type} [Group Y] [Finite Y]
    {Λ : Set (Subgroup Y)} (hΛ : HM Λ) : ∀ L ∈ Λ, AEmpty Λ L := by
  have hcl : ∀ L ∈ Λ, ∃ z : Y, Hat2A7.IsClassical2A7 ⊤ L z := fun L hL => by
    obtain ⟨z, hz⟩ := hΛ.classical L hL
    exact ⟨z, hz.to2A7⟩
  intro L hL J hJstar hJnot
  exact absurd (omegaStarNbr_subset_omegaNbr_gen hΛ.toGen hcl hL hJstar.1 hJstar) hJnot

end AEmpty

section Thm4

theorem thm4Below_a7 {n : ℕ} (hB : Hat2A7.CITBelow2A7 n) :
    Thm4Below n := by
  intro G _ _ hG Ω hΩ hO _ K hK J hJ hnc
  set Y : Subgroup G := omegaGen Ω with hYdef
  have : Y.Normal := omegaGen_normal hΩ.conjInvariant
  have hOY : classicalInvolutionOddCore ↥Y = ⊥ := oddCore_normal_eq_bot Y hO
  have hcl : ∀ L ∈ Ω, ∃ z : G, Hat2A7.IsClassical2A7 ⊤ L z := fun L hL => by
    obtain ⟨z, hz⟩ := hΩ.classical L hL
    exact ⟨z, hz.to2A7⟩
  have hinv : ∀ y ∈ Y, ∀ L ∈ Ω, L.map (MulAut.conj y).toMonoidHom ∈ Ω :=
    fun y _ L hL => hΩ.conjInvariant y L hL
  have hin : Hat2A7.InClass2A7 (Hat2A7.restrictTo Ω Y) :=
    Hat2A7.inClass2A7_restrictTo ⟨K, hK⟩ rfl hinv hcl
  have hcard : Nat.card ↥Y < n :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card Y)) hG
  obtain ⟨D⟩ := hB ↥Y hcard (Hat2A7.restrictTo Ω Y) hin
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  have hinj : Function.Injective π := by
    intro a b hab
    have h1 := QuotientGroup.eq.mp hab
    rw [hOY, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  have hKY : K ≤ Y := le_omegaGen hK
  have hJY : J ≤ Y := le_omegaGen hJ
  have hmemK : (K.subgroupOf Y).map π ∈ Hat2A7.oddQuotientFamily2A7 (Hat2A7.restrictTo Ω Y) :=
    ⟨K.subgroupOf Y, ⟨K, hK, rfl⟩, rfl⟩
  have hmemJ : (J.subgroupOf Y).map π ∈ Hat2A7.oddQuotientFamily2A7 (Hat2A7.restrictTo Ω Y) :=
    ⟨J.subgroupOf Y, ⟨J, hJ, rfl⟩, rfl⟩
  rw [D.members] at hmemK hmemJ
  obtain ⟨i, hi⟩ := hmemK
  obtain ⟨j, hj⟩ := hmemJ
  by_cases hij : i = j
  · exfalso
    subst hij
    have himg : (K.subgroupOf Y).map π = (J.subgroupOf Y).map π := hi.symm.trans hj
    have hle : ∀ {A B : Subgroup G} (hAY : A ≤ Y) (hBY : B ≤ Y),
        (A.subgroupOf Y).map π = (B.subgroupOf Y).map π → A ≤ B := by
      intro A B hAY hBY h a ha
      have hmem : π ⟨a, hAY ha⟩ ∈ (B.subgroupOf Y).map π :=
        h ▸ ⟨⟨a, hAY ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      obtain ⟨y, hy, hyk⟩ := hmem
      have h1 := hinj hyk
      have h2 : (y : G) ∈ B := Subgroup.mem_subgroupOf.mp hy
      rw [h1] at h2
      exact h2
    have hKJ : K = J := le_antisymm (hle hKY hJY himg) (hle hJY hKY himg.symm)
    exact hnc ⟨1, by rw [conjSub_one, hKJ]⟩
  · intro a ha b hb
    have hai : π ⟨a, hKY ha⟩ ∈ D.comp i :=
      hi ▸ ⟨⟨a, hKY ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hbj : π ⟨b, hJY hb⟩ ∈ D.comp j :=
      hj ▸ ⟨⟨b, hJY hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have h1 := D.commute i j hij _ hai _ hbj
    have h2 : (⟨a, hKY ha⟩ : ↥Y) * ⟨b, hJY hb⟩ = ⟨b, hJY hb⟩ * ⟨a, hKY ha⟩ :=
      hinj (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2

end Thm4

end CFSG.ClassicalInvolution.Hat2A7E.Asc77

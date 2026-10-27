module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

theorem isPlusExtraspecial_subgroupOf {Γ : Type*} [Group Γ] {M D : Subgroup Γ} (hDM : D ≤ M)
    {m : ℕ} (hD : IsPlusExtraspecial m D) : IsPlusExtraspecial m (D.subgroupOf M) := by
  obtain ⟨hExt, hcard, E, hED, hEel, hEcard⟩ := hD
  have hEM : E ≤ M := hED.trans hDM
  refine ⟨TwoHSData.isExtraspecial_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDM).symm hExt, ?_,
    E.subgroupOf M, fun x hx => hED hx, ⟨?_, ?_⟩, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv]
    exact hcard
  · refine ⟨⟨fun x y => ?_⟩⟩
    have hc := hEel.1.is_comm.comm
      (⟨((x : M) : Γ), Subgroup.mem_subgroupOf.mp x.2⟩ : E)
      (⟨((y : M) : Γ), Subgroup.mem_subgroupOf.mp y.2⟩ : E)
    have hc' : ((x : M) : Γ) * ((y : M) : Γ) = ((y : M) : Γ) * ((x : M) : Γ) :=
      congrArg Subtype.val hc
    exact Subtype.ext (Subtype.ext hc')
  · intro x hx
    have h1 := hEel.2 (x : Γ) (Subgroup.mem_subgroupOf.mp hx)
    exact Subtype.ext (by simpa using h1)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv]
    exact hEcard

theorem nonempty_quotient_equiv_of_eq {Γ B : Type*} [Group Γ] [Group B] {M N R : Subgroup Γ}
    (hNM : N = M) (hR : R ≤ N) [(R.subgroupOf M).Normal] {φ : ↥N →* B}
    (hφ : Function.Surjective φ) (hker : φ.ker = R.subgroupOf N) :
    Nonempty (↥M ⧸ R.subgroupOf M ≃* B) := by
  subst hNM
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)
  {φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo}

theorem isExtraspecialPlusByA5WrTwo_of_lemma_2_10 (hGold : GoldschmidtTheoremA)
    (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) (hs : Lemma27Spec h φ)
    (hF : Facts210 G t z) : IsExtraspecialPlusByA5WrTwo ↥(centralizer ({z} : Set G)) := by
  have hQnormal : ((Rgrp h).subgroupOf (Mgrp z)).Normal :=
    ⟨fun n hn m => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        Rgrp_conj_Mgrp h hGold hzt htz hs hF m.2 hn⟩
  haveI := hQnormal
  refine ⟨(Rgrp h).subgroupOf (Mgrp z), hQnormal, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact isPlusExtraspecial_subgroupOf (Rgrp_le_Mgrp h) (isPlusExtraspecial_Rgrp h)
  · intro c hc
    have hcR : (c : G) ∈ centralizer (Rgrp h : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hrQ : (⟨r, Rgrp_le_Mgrp h hr⟩ : ↥(Mgrp z)) ∈ (Rgrp h).subgroupOf (Mgrp z) :=
        Subgroup.mem_subgroupOf.mpr hr
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hc ⟨r, Rgrp_le_Mgrp h hr⟩ hrQ)
    have hcZ : (c : G) ∈ zpowers z := by
      rw [centralizer_Rgrp_eq h] at hcR
      exact hcR
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.zpowers_le.mpr (z_mem_Rgrp h) hcZ
  · exact nonempty_quotient_equiv_of_eq
      (normalizer_Rgrp_eq_Mgrp h hGold hzt htz hs hF) Subgroup.le_normalizer
      (φ := φ) hs.surj hs.ker

end CFSG.EvenSporadicStandard.HNRecog.Harada

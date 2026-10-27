module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Image
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Rank
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Hyp
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.BlockLevi
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 QuadraticMap
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.LieType.Universal.Spin
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge (Coord)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (isTypeL2_congr_of_central)

section Rho

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem isTypeL2_rhoImg_iff {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ orthDerived Q)
    (hperf : Group.IsPerfect ↥H) {r : ℕ} : IsTypeL2 r ↥(rhoImg Q H) ↔ IsTypeL2 r ↥H := by
  let f : ↥H →* ↥(rhoImg Q H) :=
    ((rho Q).comp (Subgroup.inclusion hH)).codRestrict (rhoImg Q H) (fun h =>
      mem_rhoImg.2 ⟨⟨h, hH h.2⟩, h.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨t, ht⟩
    obtain ⟨z, hz, rfl⟩ := mem_rhoImg.1 ht
    exact ⟨⟨z, hz⟩, Subtype.ext rfl⟩
  have hker : f.ker ≤ Subgroup.center ↥H := by
    intro h hh
    have h1 : rho Q ⟨h, hH h.2⟩ = 1 := congrArg Subtype.val hh
    have h2 : (⟨h, hH h.2⟩ : orthDerived Q) ∈ (scalars K V).subgroupOf (orthDerived Q) :=
      (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨c, hc⟩ := mem_scalars.1 (Subgroup.mem_subgroupOf.1 h2)
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    show (g : V ≃ₗ[K] V) ((h : V ≃ₗ[K] V) v) = (h : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) v)
    rw [hc, hc, map_smul]
  exact (isTypeL2_congr_of_central hperf f hf hker).symm

theorem fixedComponentImage_eq_rhoImg (x : V ≃ₗ[K] V) :
    fixedComponentImage Q x = rhoImg Q (supportedFixedDerived Q x) := rfl

end Rho

section BlockCase

variable (K : Type) [Field K] [Finite K]

theorem rootSL2_of_block (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (T2 : LeviSelfDual K) {y : (Coord → K) ≃ₗ[K] (Coord → K)}
    (hy : OddOrderIsometry (quadPlus 4 K) 3 y) {h : K[X]} (hh : h ∈ primaryFactors y.toLinearMap)
    (hne1 : h ≠ X - 1) (hqs : CFSG.IsQuasisimple ↥(specialBlock (quadPlus 4 K) y h)) {q : ℕ}
    (hq : 64 ≤ q) (hT : IsTypeL2 q ↥(componentImage (quadPlus 4 K) y h)) :
    ∃ c : adjointGroup Tag.D4 K, Pimg K (specialBlock (quadPlus 4 K) y h) =
      (simplePosSubgroup Tag.D4 K node0 ⊔ simpleNegSubgroup Tag.D4 K node0).map
        (MulAut.conj c).toMonoidHom := by
  have hFΩ : specialBlock (quadPlus 4 K) y h ≤ orthDerived (quadPlus 4 K) :=
    specialBlock_le_orthDerived_of_perfect hqs.1
      ((specialBlock_le_isometryCentralizer h).trans fun _ hg => (Subgroup.mem_inf.mp hg).1)
  have hT' : IsTypeL2 q ↥(specialBlock (quadPlus 4 K) y h) :=
    (isTypeL2_rhoImg_iff hFΩ hqs.1).1 hT
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hle2 : primaryMultiplicity y.toLinearMap h ≤ 2 :=
    specialBlock_multiplicity_le_two hO hy Nat.prime_three (by norm_num) hh hne1 (by omega) hT'
  have hge2 : 2 ≤ primaryMultiplicity y.toLinearMap h := by
    by_contra hlt
    have hpos := hy.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity y.toLinearMap h = 1 := by omega
    have hbot := hy.specialBlock_eq_bot_of_finrank_eq_one hh h1
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hqs
    rw [hbot] at hnt
    exact not_nontrivial_iff_subsingleton.2 inferInstance hnt
  have hm : primaryMultiplicity y.toLinearMap h = 2 := le_antisymm hle2 hge2
  by_cases hself : h = reciprocalPolynomial h
  · obtain ⟨A, B, hAB, -, hF⟩ := T2 y hy hh hne1 hself hm
    obtain ⟨c, hc⟩ := exists_Pimg_levi_eq_root K hAB
    exact ⟨c, by rw [hF]; exact hc⟩
  · obtain ⟨A, B, hAB, -, hF⟩ := specialBlock_eq_levi_paired (nondegenerate_quadPlus_four K) hy hh
      hne1 hself hm
    obtain ⟨c, hc⟩ := exists_Pimg_levi_eq_root K hAB
    exact ⟨c, by rw [hF]; exact hc⟩

end BlockCase

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

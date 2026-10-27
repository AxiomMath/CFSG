module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusClass
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYDescent
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNotLongRoot

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType CFSG.LieType.Universal
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed
  false_of_lieModel_omegaPlus_omegaMinus)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem minusFieldRow_class_four (hset : SeitzSetting G L) {f : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {G₀ : Subgroup G}
    (hG₀q : CFSG.IsQuasisimple G₀) (hZ : center G₀ = ⊥)
    (hG₀L : LieModel G₀ .POmegaPlus 4 2 (2 * f)) (hLG : L ≤ G₀)
    (htN : t ∈ normalizer (G₀ : Set G)) :
    perfectCore (G₀ ⊓ centralizer ({t} : Set G)) = L ∧
      (¬ ∃ g ∈ G₀, ∃ c ∈ centralizer (G₀ : Set G), t = g * c) ∧
      ∃ ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadMinus 4 F (by norm_num) (ι b) (ι c)),
        MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
          fieldAutT (coordinateQuadMinus 4 F (by norm_num) (ι b) (ι c)) σ
            (coordinateQuadMinus_fieldMap_of_fixed (by norm_num) ((hfix _).2 ⟨b, rfl⟩)
              ((hfix _).2 ⟨c, rfl⟩)) := by
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hf1 : 1 ≤ f := LinearPilot.one_le_of_card_eq_two_pow hKc
  have hG₀perf : ⁅G₀, G₀⁆ = G₀ := Subgroup.isPerfect_iff.mp hG₀q.1
  have hLmodel : LieModel L .POmegaMinus 4 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv e.symm
      (lieModel_coordinateMinus hf1 hKc le_rfl hirr)
  have hLq : CFSG.IsQuasisimple L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_coordinateMinus le_rfl hirr)
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_mulEquiv_minus le_rfl hf1 hKc hirr e
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl)
  have hcore : perfectCore (G₀ ⊓ centralizer ({t} : Set G)) = L := by
    apply le_antisymm
    · exact std_perfect_le hset.standardSetting hOut htC ht
        (CFSG.Quasithin.perfectCore_perfect _)
        ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right)
    · exact CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hLG hLt) hLperf
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hstated := F4Pilot.statedClassicalModel_of_lieModel_pomega (Or.inl rfl) hG₀L
  have hnot : ¬ ∃ g ∈ G₀, ∃ c ∈ centralizer (G₀ : Set G), t = g * c := by
    rintro ⟨g, hg, c, hc, htgc⟩
    have hgc : g * c = c * g := mem_centralizer_iff.1 hc g hg
    have hg2 : g * g = 1 := by
      have h1 : g * g * (c * c) = 1 := by
        calc g * g * (c * c) = g * (g * c) * c := by group
          _ = g * (c * g) * c := by rw [hgc]
          _ = (g * c) * (g * c) := by group
          _ = 1 := by rw [← htgc, htt]
      have h2 : g * g = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hmem : (⟨g * g, mul_mem hg hg⟩ : G₀) ∈ center G₀ := by
        rw [mem_center_iff]
        intro y
        apply Subtype.ext
        change (y : G) * (g * g) = g * g * y
        rw [h2]
        exact mem_centralizer_iff.1 (inv_mem (mul_mem hc hc)) y y.2
      rw [hZ, mem_bot] at hmem
      exact congrArg Subtype.val hmem
    by_cases hg1 : g = 1
    · subst hg1
      have htc : t ∈ centralizer (G₀ : Set G) := by
        rw [htgc, one_mul]
        exact hc
      have hG₀t : G₀ ≤ centralizer ({t} : Set G) := fun x hx =>
        mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htc x hx)
      have hEq : G₀ = L :=
        le_antisymm (std_perfect_le hset.standardSetting hOut htC ht hG₀perf hG₀t) hLG
      exact false_of_lieModel_omegaPlus_omegaMinus hG₀L
        (LieType.CurtisTits.lieModel_of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hLmodel)
    · have hg2' : orderOf (⟨g, hg⟩ : G₀) = 2 :=
        orderOf_eq_prime (Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact hg2))
          (fun h => hg1 (congrArg Subtype.val h))
      have hmapP : (perfectCore (centralizer ({(⟨g, hg⟩ : G₀)} : Set G₀))).map G₀.subtype =
          L := by
        rw [CFSG.Quasithin.map_perfectCore, map_centralizer_eq_inf_of_mul hg hc htgc, hcore]
      have hcompC := isComponent_perfectCore_subgroupOf hLq
        (((perfectCore (centralizer ({(⟨g, hg⟩ : G₀)} : Set G₀))).equivMapOfInjective
          G₀.subtype G₀.subtype_injective).trans (MulEquiv.subgroupCongr hmapP))
      exact CFSG.ComponentClassification.CatLeaf.involutionCentralizersComponentFree_orthogonal
        (Or.inl rfl) hstated _ hg2' _ hcompC
  refine ⟨hcore, hnot, ?_⟩
  obtain ⟨ψS⟩ := nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hG₀L F hF
  set ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F) :=
    ψS.trans (statedOmegaPlusEquiv F 4 (by omega)) with hψdef
  set τ₀ := G₀.normalizerMonoidHom ⟨t, htN⟩ with hτ₀
  have hτ : τ₀ * τ₀ = 1 := by
    rw [hτ₀, ← map_mul]
    have h1 : (⟨t, htN⟩ : normalizer (G₀ : Set G)) * ⟨t, htN⟩ = 1 := Subtype.ext htt
    rw [h1, map_one]
  set β := MulAut.congr ψ τ₀ with hβdef
  have hβ : β * β = 1 := by rw [hβdef, ← map_mul, hτ, map_one]
  have hfixmap : (fixedSubgroup τ₀).map G₀.subtype = G₀ ⊓ centralizer ({t} : Set G) := by
    rw [hτ₀, F4Pilot.fixedSubgroup_normalizerMonoidHom, subgroupOf_map_subtype, inf_comm]
  have hPfix : (perfectCore (fixedSubgroup τ₀)).map G₀.subtype = L := by
    rw [CFSG.Quasithin.map_perfectCore, hfixmap, hcore]
  let eP : perfectCore (fixedSubgroup τ₀) ≃* L :=
    ((perfectCore (fixedSubgroup τ₀)).equivMapOfInjective G₀.subtype
      G₀.subtype_injective).trans (MulEquiv.subgroupCongr hPfix)
  have hcomp0 := isComponent_perfectCore_subgroupOf hLq eP
  have hcomp0m : LieModel ((perfectCore (fixedSubgroup τ₀)).subgroupOf (fixedSubgroup τ₀))
      .POmegaMinus 4 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe (CFSG.Quasithin.perfectCore_le _)).trans eP).symm hLmodel
  have hfix' : fixedSubgroup β = (fixedSubgroup τ₀).map ψ.toMonoidHom :=
    CFSG.ComponentClassification.ExcSelector.fixedSubgroup_congr ψ τ₀
  let Φ : fixedSubgroup τ₀ ≃* fixedSubgroup β :=
    ((fixedSubgroup τ₀).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr hfix'.symm)
  have hD := CFSG.ComponentClassification.CatLeaf.isComponent_map_mulEquiv Φ hcomp0
  have hDm := LieType.CurtisTits.lieModel_of_mulEquiv
    (((perfectCore (fixedSubgroup τ₀)).subgroupOf (fixedSubgroup τ₀)).equivMapOfInjective
      Φ.toMonoidHom Φ.injective) hcomp0m
  have hb' : σ (ι b) = ι b := (hfix _).2 ⟨b, rfl⟩
  have hc' : σ (ι c) = ι c := (hfix _).2 ⟨c, rfl⟩
  have hirr' : ∀ s : F, σ s = s → s ^ 2 + ι b * s + ι c ≠ 0 := by
    intro s hs h0
    obtain ⟨s', rfl⟩ := (hfix s).1 hs
    apply hirr s'
    apply ι.injective
    rw [map_zero, ← h0, map_add, map_add, map_mul, map_pow]
  obtain ⟨Θ, hΘ⟩ := TwistedE6Pilot.exists_mulEquiv_congr_eq_fieldAutT hσ hb' hc' hirr' hβ hD hDm
  refine ⟨ψ.trans Θ, ?_⟩
  rw [mulAut_congr_trans]
  exact hΘ

end CFSG.SeitzReduction.OmegaPilot

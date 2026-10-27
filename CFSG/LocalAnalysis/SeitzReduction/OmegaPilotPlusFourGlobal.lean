module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveDescent

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType CFSG.LieType.Universal
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)

section Class

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem fieldRow_class_four (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 1 ≤ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ (2 * f))
    {G₀ : Subgroup G} (hZ : center G₀ = ⊥) (hG₀perf : ⁅G₀, G₀⁆ = G₀)
    (hG₀L : LieModel G₀ .POmegaPlus 4 2 (2 * f)) (hLG : L ≤ G₀)
    (htN : t ∈ normalizer (G₀ : Set G)) :
    perfectCore (G₀ ⊓ centralizer ({t} : Set G)) = L ∧
      (¬ ∃ g ∈ G₀, ∃ c ∈ centralizer (G₀ : Set G), t = g * c) ∧
      ∀ σ : F ≃+* F, orderOf σ = 2 →
        ∃ ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F),
          MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
            fieldAutT (coordinateQuadPlus 4 F) σ (E7Pilot.coordinateQuadPlus_fieldMap 4 σ) := by
  have hLmodel : LieModel L .POmegaPlus 4 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv e.symm (E7Pilot.lieModel_coordinatePlus hf hKc le_rfl)
  have hLq : CFSG.IsQuasisimple L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (E7Pilot.isQuasisimple_coordinatePlus (by norm_num))
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_lieModel_POmegaPlus hLmodel
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
      have hLG₀ : LieModel G₀ .POmegaPlus 4 2 f :=
        LieType.CurtisTits.lieModel_of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hLmodel
      obtain ⟨-, -, h⟩ := lieModel_POmega_two_unique_classicalOrSuzuki_of_card_eq (Or.inl rfl)
        hG₀L (Or.inl (by decide)) hLG₀ rfl
      omega
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
  refine ⟨hcore, hnot, fun σ hσ => ?_⟩
  obtain ⟨ψS⟩ := nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by norm_num) hG₀L F hF
  set ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F) :=
    ψS.trans (statedOmegaPlusEquiv F 4 (by norm_num)) with hψdef
  set τ₀ := G₀.normalizerMonoidHom ⟨t, htN⟩ with hτ₀
  have hτ : τ₀ * τ₀ = 1 := by
    rw [hτ₀, ← map_mul]
    have h1 : (⟨t, htN⟩ : normalizer (G₀ : Set G)) * ⟨t, htN⟩ = 1 := Subtype.ext htt
    rw [h1, map_one]
  have hτ1 : τ₀ ≠ 1 := by
    intro h
    apply hnot
    refine ⟨1, one_mem _, t, ?_, (one_mul t).symm⟩
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨x, hx⟩)
    rw [hτ₀, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    change t * x * t⁻¹ = x at h1
    calc x * t = t * x * t⁻¹ * t := by rw [h1]
      _ = t * x := by group
  set β := MulAut.congr ψ τ₀ with hβdef
  have hβ : β * β = 1 := by rw [hβdef, ← map_mul, hτ, map_one]
  have hβ1 : β ≠ 1 := fun h => hτ1 ((MulAut.congr ψ).injective (by rw [← hβdef, h, map_one]))
  have hfixmap : (fixedSubgroup τ₀).map G₀.subtype = G₀ ⊓ centralizer ({t} : Set G) := by
    rw [hτ₀, F4Pilot.fixedSubgroup_normalizerMonoidHom, subgroupOf_map_subtype, inf_comm]
  have hPfix : (perfectCore (fixedSubgroup τ₀)).map G₀.subtype = L := by
    rw [CFSG.Quasithin.map_perfectCore, hfixmap, hcore]
  let eP : perfectCore (fixedSubgroup τ₀) ≃* L :=
    ((perfectCore (fixedSubgroup τ₀)).equivMapOfInjective G₀.subtype
      G₀.subtype_injective).trans (MulEquiv.subgroupCongr hPfix)
  have hcomp0 := isComponent_perfectCore_subgroupOf hLq eP
  have hcomp0m : LieModel ((perfectCore (fixedSubgroup τ₀)).subgroupOf (fixedSubgroup τ₀))
      .POmegaPlus 4 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe (CFSG.Quasithin.perfectCore_le _)).trans eP).symm hLmodel
  have hfix : fixedSubgroup β = (fixedSubgroup τ₀).map ψ.toMonoidHom :=
    CFSG.ComponentClassification.ExcSelector.fixedSubgroup_congr ψ τ₀
  let Φ : fixedSubgroup τ₀ ≃* fixedSubgroup β :=
    ((fixedSubgroup τ₀).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)
  have hD := CFSG.ComponentClassification.CatLeaf.isComponent_map_mulEquiv Φ hcomp0
  have hDm := LieType.CurtisTits.lieModel_of_mulEquiv
    (((perfectCore (fixedSubgroup τ₀)).subgroupOf (fixedSubgroup τ₀)).equivMapOfInjective
      Φ.toMonoidHom Φ.injective) hcomp0m
  obtain ⟨ψ', hψ'⟩ := exists_conj_eq_fieldAutT_of_component_four hσ hβ hβ1 hD hDm
  refine ⟨ψ.trans ψ', ?_⟩
  rw [mulAut_congr_trans, mulAut_congr_self, ← hβdef, hψ']

end Class

section Global

open CFSG.Timmesfeld (edgeD)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem nonadj_four {i j : Fin (3 + 1)} (hij : i ≠ j) (h1 : ¬ edgeD (3 + 1) i j)
    (h2 : ¬ edgeD (3 + 1) j i) (hf1 : ¬ (i.val + 2 = 3 + 1 ∧ j.val + 1 = 3 + 1))
    (hf2 : ¬ (j.val + 2 = 3 + 1 ∧ i.val + 1 = 3 + 1)) :
    (i = 0 ∧ (j = 2 ∨ j = 3)) ∨ (j = 0 ∧ (i = 2 ∨ i = 3)) := by
  revert i j
  decide

theorem fieldRow_global_four (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 1) K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (hF : Nat.card F = 2 ^ (2 * f))
    {ι : K →+* F} (hC : ∀ k, PlusFieldCover e ι k)
    (horth : plusNode e 0 ≤ centralizer (plusNode e 2 : Set G) ∧
      plusNode e 0 ≤ centralizer (plusNode e 3 : Set G))
    {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, plusNode e j) :
    CFSG.IsQuasisimple G₀ ∧ center G₀ = ⊥ ∧ LieModel G₀ .POmegaPlus 4 2 (2 * f) ∧ L ≤ G₀ ∧
      perfectCore (G₀ ⊓ centralizer ({t} : Set G)) = L ∧
      (¬ ∃ g ∈ G₀, ∃ c ∈ centralizer (G₀ : Set G), t = g * c) ∧
      ∃ htN : t ∈ normalizer (G₀ : Set G), ∀ σ : F ≃+* F, orderOf σ = 2 →
        ∃ ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F),
          MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
            fieldAutT (coordinateQuadPlus 4 F) σ (E7Pilot.coordinateQuadPlus_fieldMap 4 σ) := by
  have hf1 : 1 ≤ f := LinearPilot.one_le_of_card_eq_two_pow hKc
  have hf2 : 2 ≤ f := (LinearPilot.four_le_card_iff_two_le hKc).1 hq
  have hF16 : 16 ≤ Nat.card F := by
    rw [hF]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfork := hfork_of_forall_cover (by norm_num) hC hq (by omega)
  have hcomm : ∀ i j : Fin (3 + 1), i ≠ j → ¬ edgeD (3 + 1) i j → ¬ edgeD (3 + 1) j i →
      plusNode e i ≤ centralizer (plusNode e j : Set G) := by
    intro i j hij h1 h2
    by_cases hf1 : i.val + 2 = 3 + 1 ∧ j.val + 1 = 3 + 1
    · exact hfork i j hf1.1 hf1.2
    by_cases hf2' : j.val + 2 = 3 + 1 ∧ i.val + 1 = 3 + 1
    · exact Subgroup.le_centralizer_iff.1 (hfork j i hf2'.1 hf2'.2)
    rcases nonadj_four hij h1 h2 hf1 hf2' with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
    · exact horth.1
    · exact horth.2
    · exact Subgroup.le_centralizer_iff.1 horth.1
    · exact Subgroup.le_centralizer_iff.1 horth.2
  obtain ⟨-, -, -, hG₀q, -, -⟩ := exists_weakCT_spinPlus_of_pieces (n := 3 + 1) (by norm_num)
    (by norm_num) hf1 hF (plusNode e) hG₀ hcomm
    (fun i j hij => exists_theta_plusNode (by norm_num) hC hq (by omega) hij)
  obtain ⟨Ψ, -, hcen, hmodel⟩ := exists_weakCT_spinPlus_of_pieces_two_pow (n := 3 + 1)
    (by norm_num) (by omega : 1 ≤ 2 * f) hF (by omega) (plusNode e) hG₀ hcomm
    (fun i j hij => exists_theta_plusNode (by norm_num) hC hq (by omega) hij)
  have hZ : center G₀ = ⊥ := by
    rw [hcen, center_spinGroup_quadPlus_eq_bot' (by norm_num), Subgroup.map_bot]
  have hG₀L : LieModel G₀ .POmegaPlus 4 2 (2 * f) :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel
  have hLG : L ≤ G₀ := hG₀ ▸ le_iSup_plusNode e (by norm_num) hKc hq
  have htN : t ∈ normalizer (G₀ : Set G) := by
    rw [hG₀]
    exact mem_normalizer_iSup_plusNode e htC
  obtain ⟨hcore, hnot, hcl⟩ := fieldRow_class_four hset hKc hf1 e htC ht hF hZ
    (Subgroup.isPerfect_iff.mp hG₀q.1) hG₀L hLG htN
  exact ⟨hG₀q, hZ, hG₀L, hLG, hcore, hnot, htN, hcl⟩

end Global

end CFSG.SeitzReduction.OmegaPilot

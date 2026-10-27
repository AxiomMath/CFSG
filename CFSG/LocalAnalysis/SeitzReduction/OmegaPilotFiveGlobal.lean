module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType CFSG.LieType.Universal
open CFSG.Timmesfeld (edgeD)
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_weakCT_plus_of_fieldRow_five (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (4 + 1) K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (h8 : ∀ k : Fin (4 + 1), OmegaHR8FieldAt t 4 f .POmegaPlus (modelToG e (pairTorus (K := K) k))
      (modelToG e (pairPerp (K := K) k)))
    (hrow : ∀ k : Fin (4 + 1), OmegaRowAt t (modelToG e (pairTorus (K := K) k))
      (modelToG e (pairPerp (K := K) k)) .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, plusNode e j) :
    (∀ k, Nonempty (PlusFieldCover e ι k)) ∧
      ∃ Ψ : spinGroup (Spin.quadPlus (4 + 1) F) →* G₀, Function.Surjective Ψ ∧
        Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple G₀ ∧
        CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) .POmegaPlus (4 + 1) 2 (2 * f) ∧
        (∀ j, (CurtisTits.rankOne (Spin.plusDatum (4 + 1) F (by omega)).rootGroup j).map Ψ =
          (plusNode e j).subgroupOf G₀) ∧
        t ∈ normalizer (G₀ : Set G) := by
  have hC : ∀ k, Nonempty (PlusFieldCover e ι k) := by
    intro k
    obtain ⟨-, htX, -⟩ := neighbour_data_pairTorus hKc hq (by omega : 5 ≤ 4 + 1) k e htC rfl rfl
    obtain ⟨hcomp, -, -⟩ := neighbour_standard_pairTorus_of_seitzSetting hset hKc hq
      (by omega : 5 ≤ 4 + 1) k e htC ht rfl htX rfl
    obtain ⟨htX', Kc, hKcomp, hfield, hKt⟩ := exists_fieldAlt_of_rowAt (h8 k) (hrow k) hcomp.2.2
    exact nonempty_plusFieldCover_of_field_five hset hKc hq k e htC ht rfl htX' rfl hKcomp hfield
      hKt ι hσ hfix
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  exact ⟨hC, exists_weakCT_plus_of_forall_cover (by omega) hKc hq hF (fun k => (hC k).some) hG₀
    htC⟩

theorem fieldRow_global_class_five (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (4 + 1) K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ (2 * f)) {ι : K →+* F}
    (hC : ∀ k, PlusFieldCover e ι k) {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, plusNode e j) :
    center G₀ = ⊥ ∧ LieModel G₀ .POmegaPlus (4 + 1) 2 (2 * f) ∧ L ≤ G₀ ∧
      perfectCore (G₀ ⊓ centralizer ({t} : Set G)) = L ∧
      (¬ ∃ g ∈ G₀, ∃ c ∈ centralizer (G₀ : Set G), t = g * c) ∧
      ∃ htN : t ∈ normalizer (G₀ : Set G), ∀ σ : F ≃+* F, orderOf σ = 2 →
        ∃ ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus (4 + 1) F),
          MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
            fieldAutT (coordinateQuadPlus (4 + 1) F) σ
              (E7Pilot.coordinateQuadPlus_fieldMap (4 + 1) σ) := by
  have hf2 : 2 ≤ f := by
    by_contra h
    have hf1 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hF16 : 16 ≤ Nat.card F := by
    rw [hF]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF4 : 4 ≤ Nat.card F := by omega
  have hfork := hfork_of_forall_cover (by omega) hC hq hF4
  have hcomm : ∀ i j : Fin (4 + 1), i ≠ j → ¬ edgeD (4 + 1) i j → ¬ edgeD (4 + 1) j i →
      plusNode e i ≤ centralizer (plusNode e j : Set G) := by
    intro i j hij h1 h2
    by_cases hf1 : i.val + 2 = 4 + 1 ∧ j.val + 1 = 4 + 1
    · exact hfork i j hf1.1 hf1.2
    by_cases hf2' : j.val + 2 = 4 + 1 ∧ i.val + 1 = 4 + 1
    · exact Subgroup.le_centralizer_iff.1 (hfork j i hf2'.1 hf2'.2)
    exact plusNode_le_centralizer (by omega) hC hq hF4 (disjoint_plusNodeSet hij h1 h2 hf1 hf2')
  obtain ⟨Ψ, -, hcen, hmodel⟩ := exists_weakCT_spinPlus_of_pieces_two_pow (n := 4 + 1)
    (by omega) (by omega : 1 ≤ 2 * f) hF hF4 (plusNode e) hG₀ hcomm
    (fun i j hij => exists_theta_plusNode (by omega) hC hq (by omega) hij)
  have hZ : center G₀ = ⊥ := by
    rw [hcen, center_spinGroup_quadPlus_eq_bot' (by omega), Subgroup.map_bot]
  have hG₀L : LieModel G₀ .POmegaPlus (4 + 1) 2 (2 * f) :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel
  obtain ⟨-, -, -, hG₀q, -, -, htN⟩ :=
    exists_weakCT_plus_of_forall_cover (by omega) hKc hq hF hC hG₀ htC
  have hG₀perf : ⁅G₀, G₀⁆ = G₀ := Subgroup.isPerfect_iff.mp hG₀q.1
  have hLG : L ≤ G₀ := hG₀ ▸ le_iSup_plusNode e (by omega) hKc hq
  have hLmodel : LieModel L .POmegaPlus (4 + 1) 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv e.symm
      (E7Pilot.lieModel_coordinatePlus (by omega) hKc (by omega))
  have hLq : CFSG.IsQuasisimple L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (E7Pilot.isQuasisimple_coordinatePlus (by omega))
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
      have hLG₀ : LieModel G₀ .POmegaPlus (4 + 1) 2 f :=
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
  refine ⟨hZ, hG₀L, hLG, hcore, hnot, htN, fun σ hσ => ?_⟩
  obtain ⟨ψS⟩ := nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hG₀L F hF
  set ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus (4 + 1) F) :=
    ψS.trans (statedOmegaPlusEquiv F (4 + 1) (by omega)) with hψdef
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
      .POmegaPlus (4 + 1) 2 f :=
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
  obtain ⟨ψ', hψ'⟩ := exists_conj_eq_fieldAutT_of_component hσ (by omega : 5 ≤ 4 + 1) hβ hβ1
    hD hDm
  refine ⟨ψ.trans ψ', ?_⟩
  rw [mulAut_congr_trans, mulAut_congr_self, ← hβdef, hψ']

theorem fieldRow_global_of_HR8_five (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (4 + 1) K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (h8 : ∀ k : Fin (4 + 1), OmegaHR8FieldAt t 4 f .POmegaPlus (modelToG e (pairTorus (K := K) k))
      (modelToG e (pairPerp (K := K) k)))
    (hrow : ∀ k : Fin (4 + 1), OmegaRowAt t (modelToG e (pairTorus (K := K) k))
      (modelToG e (pairPerp (K := K) k)) .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, plusNode e j) :
    (∀ k, Nonempty (PlusFieldCover e ι k)) ∧ CFSG.IsQuasisimple G₀ ∧ center G₀ = ⊥ ∧
      LieModel G₀ .POmegaPlus (4 + 1) 2 (2 * f) ∧ L ≤ G₀ ∧
      perfectCore (G₀ ⊓ centralizer ({t} : Set G)) = L ∧
      (¬ ∃ g ∈ G₀, ∃ c ∈ centralizer (G₀ : Set G), t = g * c) ∧
      ∃ htN : t ∈ normalizer (G₀ : Set G),
        ∃ ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus (4 + 1) F),
          MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
            fieldAutT (coordinateQuadPlus (4 + 1) F) σ
              (E7Pilot.coordinateQuadPlus_fieldMap (4 + 1) σ) := by
  obtain ⟨hC, -, -, -, hG₀q, -, -, -⟩ :=
    exists_weakCT_plus_of_fieldRow_five hset hKc hq e htC ht h8 hrow ι hσ hfix hG₀
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  obtain ⟨hZ, hG₀L, hLG, hcore, hnot, htN, hcl⟩ :=
    fieldRow_global_class_five hset hKc hq e htC ht hF (fun k => (hC k).some) hG₀
  exact ⟨hC, hG₀q, hZ, hG₀L, hLG, hcore, hnot, htN, hcl σ hσ⟩

end CFSG.SeitzReduction.OmegaPilot

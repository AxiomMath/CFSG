module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Fix
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Factor
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Plane
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Conj
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Basic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.Quasithin (perfectCore)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_two_ne_three (hn : 5 ≤ n) (i j k : Fin n) :
    ∃ g h : Fin n, g ≠ h ∧ i ≠ g ∧ i ≠ h ∧ j ≠ g ∧ j ≠ h ∧ k ≠ g ∧ k ≠ h := by
  classical
  have hcard : 1 < ((Finset.univ : Finset (Fin n)) \ {i, j, k}).card := by
    have h1 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin n)) {i, j, k}
    have h2 : ((Finset.univ : Finset (Fin n)) ∩ {i, j, k}).card ≤ 3 := by
      rw [Finset.univ_inter]
      exact Finset.card_le_three
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨g, hg, h, hh, hgh⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hg hh
  exact ⟨g, h, hgh, fun e => hg.1 e.symm, fun e => hh.1 e.symm, fun e => hg.2.1 e.symm,
    fun e => hh.2.1 e.symm, fun e => hg.2.2 e.symm, fun e => hh.2.2 e.symm⟩

omit [Finite K] [CharP K 2] in
theorem pairTorus_le_stabTwoBar {i j k : Fin n} (hik : i ≠ k) (hjk : j ≠ k) :
    pairTorus k ≤ stabTwoBar K i j := by
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨c, hc⟩ := mem_subgroupOf.mp ht
  refine ⟨t, mem_subgroupOf.mpr ?_, rfl⟩
  rw [← hc]
  refine ⟨⟨torusLin_eq_self_of ?_ ?_ c, torusLin_eq_self_of ?_ ?_ c⟩,
    torusLin_eq_self_of ?_ ?_ c, torusLin_eq_self_of ?_ ?_ c⟩ <;>
    simp [hik, hjk]

omit [Finite K] [CharP K 2] in
theorem pairTorusOf_le_stabPairsBar {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    {a a' b b' c c' : Fin d} (hdc₁ : PairDisjoint a a' c c') (hdc₂ : PairDisjoint b b' c c') :
    pairTorusOf Q c c' ≤ stabPairsBar Q a a' b b' := by
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨l₀, hl⟩ := mem_subgroupOf.mp ht
  refine ⟨t, mem_subgroupOf.mpr ?_, rfl⟩
  rw [← hl]
  refine ⟨⟨torusLin_eq_self_of ?_ ?_ l₀, torusLin_eq_self_of ?_ ?_ l₀⟩,
    torusLin_eq_self_of ?_ ?_ l₀, torusLin_eq_self_of ?_ ?_ l₀⟩
  · exact Pi.single_eq_of_ne hdc₁.left_ne_left _
  · exact Pi.single_eq_of_ne hdc₁.right_ne_left _
  · exact Pi.single_eq_of_ne hdc₁.left_ne_right _
  · exact Pi.single_eq_of_ne hdc₁.right_ne_right _
  · exact Pi.single_eq_of_ne hdc₂.left_ne_left _
  · exact Pi.single_eq_of_ne hdc₂.right_ne_left _
  · exact Pi.single_eq_of_ne hdc₂.left_ne_right _
  · exact Pi.single_eq_of_ne hdc₂.right_ne_right _

theorem refinedF6_pairTorusOf {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hq : 4 ≤ Nat.card K) {a a' b b' c c' : Fin d} (hi : IsHypCoord Q a a')
    (hj : IsHypCoord Q b b') (hk : IsHypCoord Q c c') (hd : PairDisjoint a a' b b')
    (hdc₁ : PairDisjoint a a' c c') (hdc₂ : PairDisjoint b b' c c')
    (hS : CFSG.IsQuasisimple (stabPairsBar Q a a' b b') ∧ center (stabPairsBar Q a a' b b') = ⊥)
    (hB4 : Nat.card K ^ 4 ≤ Nat.card (stabPairsBar Q a a' b b'))
    (hD : ⁅pairPerpOf Q c c', pairPerpOf Q c c'⁆ = pairPerpOf Q c c') :
    RefinedF6 (rootRadicalBar Q hi.hypPair hj.hypPair) (rootLeviBar Q hi.hypPair hj.hypPair)
      (pairTorusOf Q c c') (pairPerpOf Q c c') := by
  classical
  have hXB : pairTorusOf Q c c' ≤ stabPairsBar Q a a' b b' :=
    pairTorusOf_le_stabPairsBar hdc₁ hdc₂
  have hJM : pairTorusOf Q c c' ≤ rootLeviBar Q hi.hypPair hj.hypPair :=
    hXB.trans (stabPairsBar_le_rootLeviBar hi hj)
  set M := rootLeviBar Q hi.hypPair hj.hypPair with hM
  intro ι hcard
  set Y : Subgroup (matrixProjectiveDerived Q) :=
    (((pairTorusOf Q c c').subgroupOf M).map ι.toMonoidHom).map M.subtype with hYdef
  have hBfix := map_stabPairsBar_subgroupOf_eq hi hj hd hS hB4 ι
  have hYB : Y ≤ stabPairsBar Q a a' b b' := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ ((stabPairsBar Q a a' b b').subgroupOf M).map ι.toMonoidHom :=
      map_mono (fun z hz => mem_subgroupOf.mpr (hXB (mem_subgroupOf.mp hz))) hx
    rw [hBfix] at hx'
    exact mem_subgroupOf.mp hx'
  set eY : pairTorusOf Q c c' ≃* Y :=
    ((subgroupOfEquivOfLe hJM).symm.trans
      (((pairTorusOf Q c c').subgroupOf M).equivMapOfInjective _ ι.injective)).trans
      ((((pairTorusOf Q c c').subgroupOf M).map ι.toMonoidHom).equivMapOfInjective _
        M.subtype_injective) with heY
  have hYcard : Nat.card Y = Nat.card (pairTorusOf Q c c') := (Nat.card_congr eY.toEquiv).symm
  have hYcyc : IsCyclic Y := by
    have := hk.isCyclic_pairTorusOf
    exact isCyclic_of_surjective eY eY.surjective
  have hcY := card_rootRadicalBar_inf_centralizer hQ hT hi hj hd hYB
  have hcX := card_rootRadicalBar_inf_centralizer hQ hT hi hj hd hXB
  have hq0 : 0 < Nat.card K := by omega
  have hUeq : Nat.card ↥(fixSpace (Y.comap (projHom Q)) ⊓ subW K a a' b b') =
      Nat.card ↥(fixSpace ((pairTorusOf Q c c').comap (projHom Q)) ⊓ subW K a a' b b') := by
    have h := hcard
    rw [hcY, hcX] at h
    exact Nat.pow_left_injective two_ne_zero (Nat.eq_of_mul_eq_mul_left hq0 h)
  have hFY := card_fixSpace_eq hi hj hd (B := Y.comap (projHom Q))
    fun g hg => mem_stabSub_of_projHom_mem hi hYB hg
  have hFX := card_fixSpace_eq hi hj hd (B := (pairTorusOf Q c c').comap (projHom Q))
    fun g hg => mem_stabSub_of_projHom_mem hi hXB hg
  have hFX' := card_fixSpace_comap_pairTorusOf hk (by omega)
  have hFYc : Nat.card (fixSpace (Y.comap (projHom Q))) = Nat.card K ^ (d - 2) := by
    rw [hFY, hUeq, ← hFX]
    exact hFX'
  have hFYr : finrank K (fixSpace (Y.comap (projHom Q))) = d - 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K)] at hFYc
    exact Nat.pow_right_injective (by omega) hFYc
  obtain ⟨y₀, hy₀⟩ := hYcyc.exists_zpow_surjective
  obtain ⟨g₀, hg₀⟩ := projHom_surjective Q (y₀ : matrixProjectiveDerived Q)
  have hρ := projHom_injective (Q := Q) hi.exists_ne_zero
  have hord : orderOf ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      Nat.card K - 1 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective (projHom _) hρ g₀, hg₀, Subgroup.orderOf_coe,
      orderOf_eq_card_of_forall_mem_zpowers (fun x => mem_zpowers_iff.mpr (hy₀ x)), hYcard,
      card_pairTorusOf hk]
  obtain ⟨f, hf⟩ := exists_card_eq_two_pow (K := K)
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [hf, pow_zero] at hq
    omega
  have hodd : Odd (orderOf ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K))) := by
    rw [hord, hf]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, hf0⟩) odd_one
  have hyq : ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ^ Nat.card K =
      ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
    rw [show Nat.card K = (Nat.card K - 1) + 1 by omega, pow_succ, ← hord, pow_orderOf_eq_one,
      one_mul]
  have hy1 : ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hle : fixSpace (Y.comap (projHom Q)) ≤
      fixSub ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) := fun v hv =>
    hv g₀ (show projHom _ g₀ ∈ Y by rw [hg₀]; exact y₀.2)
  have hF : finrank K (Fin d → K) ≤
      finrank K (fixSub ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K))) + 2 := by
    have := Submodule.finrank_mono hle
    rw [Module.finrank_fin_fun]
    omega
  obtain ⟨u, v, hu, hv, huv, c₀, hc⟩ := exists_hypPair_of_codim_fix_le_two hQ
    (Subgroup.commutator_le_self _ g₀.2) hodd hyq hy1 hF
  have hYt : ∀ g : orthDerived Q, projHom _ g ∈ Y → ∃ c' : Kˣ,
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) u = (c' : K) • u ∧
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) v = ((c'⁻¹ : Kˣ) : K) • v ∧
      ∀ x, polar Q x u = 0 → polar Q x v = 0 → (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) x = x := by
    intro g hg
    obtain ⟨m, hm⟩ := hy₀ ⟨projHom _ g, hg⟩
    have hgm : g = g₀ ^ m := by
      apply hρ
      rw [map_zpow, hg₀]
      have := congrArg Subtype.val hm
      rw [Subgroup.coe_zpow] at this
      exact this.symm
    obtain ⟨h1, h2, h3⟩ := hc m
    refine ⟨c₀ ^ m, ?_, ?_, fun x hxu hxv => ?_⟩
    · rw [hgm, Subgroup.coe_zpow]
      exact h1
    · rw [hgm, Subgroup.coe_zpow]
      exact h2
    · rw [hgm, Subgroup.coe_zpow]
      exact h3 x hxu hxv
  exact nonempty_perfectCore_centralizer_mulEquiv_pairPerpOf hQ hk hq hD hu hv huv hYt hYcard

theorem refinedF6_pairTorus (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {i j k : Fin n} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    RefinedF6 (plusRadical K i j) (plusLevi K i j) (pairTorus k) (pairPerp (K := K) k) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n K (by omega)
  have hk := isHypCoord_coordinateQuadPlus (K := K) k
  obtain ⟨g, h, hgh, hig, hih, hjg, hjh, hkg, hkh⟩ := exists_two_ne_three hn i j k
  have hD : ⁅pairPerp (K := K) k, pairPerp (K := K) k⁆ = pairPerp (K := K) k := by
    obtain ⟨hR, hT'⟩ := regular_plusPerp (K := K) (by omega : 4 ≤ n) k
    exact Subgroup.isPerfect_iff.mp (hk.isQuasisimple_pairPerpOf hQ hR hT').1
  exact refinedF6_pairTorusOf hQ hT hq (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) hk (pairDisjoint_plus hij) (pairDisjoint_plus hik)
    (pairDisjoint_plus hjk) (isQuasisimple_stabTwoBar hn hij)
    (card_le_stabTwoBar (by omega) hik hig hih hjk hjg hjh hkg hkh hgh) hD

end CFSG.SeitzReduction.OmegaPilot

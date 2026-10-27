module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourHR7iii

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.Quasithin (perfectCore)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem refinedF6_of_le_stabPairsBar {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hq : 4 ≤ Nat.card K) {a a' b b' c c' : Fin d} (hi : IsHypCoord Q a a')
    (hj : IsHypCoord Q b b') (hk : IsHypCoord Q c c') (hd : PairDisjoint a a' b b')
    (hdc₁ : PairDisjoint a a' c c') (hdc₂ : PairDisjoint b b' c c')
    (hD : ⁅pairPerpOf Q c c', pairPerpOf Q c c'⁆ = pairPerpOf Q c c')
    (ι : rootLeviBar Q hi.hypPair hj.hypPair ≃* rootLeviBar Q hi.hypPair hj.hypPair)
    (hYB : (((pairTorusOf Q c c').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair)).map
      ι.toMonoidHom).map (rootLeviBar Q hi.hypPair hj.hypPair).subtype ≤
        stabPairsBar Q a a' b b')
    (hcard : Nat.card (rootRadicalBar Q hi.hypPair hj.hypPair ⊓ centralizer
        ((((((pairTorusOf Q c c').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair)).map
          ι.toMonoidHom).map (rootLeviBar Q hi.hypPair hj.hypPair).subtype :
            Subgroup (matrixProjectiveDerived Q))) : Set (matrixProjectiveDerived Q)) :
          Subgroup (matrixProjectiveDerived Q)) =
      Nat.card (rootRadicalBar Q hi.hypPair hj.hypPair ⊓
        centralizer (pairTorusOf Q c c' : Set (matrixProjectiveDerived Q)) :
          Subgroup (matrixProjectiveDerived Q))) :
    Nonempty (perfectCore (centralizer
      ((((((pairTorusOf Q c c').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair)).map
        ι.toMonoidHom).map (rootLeviBar Q hi.hypPair hj.hypPair).subtype :
          Subgroup (matrixProjectiveDerived Q))) : Set (matrixProjectiveDerived Q))) ≃*
      pairPerpOf Q c c') := by
  classical
  have hXB : pairTorusOf Q c c' ≤ stabPairsBar Q a a' b b' :=
    pairTorusOf_le_stabPairsBar hdc₁ hdc₂
  have hJM : pairTorusOf Q c c' ≤ rootLeviBar Q hi.hypPair hj.hypPair :=
    hXB.trans (stabPairsBar_le_rootLeviBar hi hj)
  set Y : Subgroup (matrixProjectiveDerived Q) :=
    (((pairTorusOf Q c c').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair)).map ι.toMonoidHom).map (rootLeviBar Q hi.hypPair hj.hypPair).subtype with hYdef
  set eY : pairTorusOf Q c c' ≃* Y :=
    ((subgroupOfEquivOfLe hJM).symm.trans
      (((pairTorusOf Q c c').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair)).equivMapOfInjective _ ι.injective)).trans
      ((((pairTorusOf Q c c').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair)).map ι.toMonoidHom).equivMapOfInjective _
        (rootLeviBar Q hi.hypPair hj.hypPair).subtype_injective) with heY
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

theorem refinedF6_pairTorus_four_of_le (hq : 4 ≤ Nat.card K) {i j k : Fin 4} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (ι : plusLevi K i j ≃* plusLevi K i j)
    (hYB : (((pairTorus (K := K) k).subgroupOf (plusLevi K i j)).map ι.toMonoidHom).map
      (plusLevi K i j).subtype ≤ stabTwoBar K i j)
    (hcard : Nat.card (plusRadical K i j ⊓ centralizer
        (((((pairTorus (K := K) k).subgroupOf (plusLevi K i j)).map ι.toMonoidHom).map
          (plusLevi K i j).subtype : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
            Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
          Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) =
      Nat.card (plusRadical K i j ⊓ centralizer (pairTorus (K := K) k :
          Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
        Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) :
    Nonempty (perfectCore (centralizer
      (((((pairTorus (K := K) k).subgroupOf (plusLevi K i j)).map ι.toMonoidHom).map
        (plusLevi K i j).subtype : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
          Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) ≃* pairPerp (K := K) k) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hk := isHypCoord_coordinateQuadPlus (K := K) k
  have hD : ⁅pairPerp (K := K) k, pairPerp (K := K) k⁆ = pairPerp (K := K) k := by
    obtain ⟨hR, hT'⟩ := regular_plusPerp (K := K) (by norm_num : 4 ≤ 4) k
    exact Subgroup.isPerfect_iff.mp (hk.isQuasisimple_pairPerpOf hQ hR hT').1
  exact refinedF6_of_le_stabPairsBar hQ hT hq (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) hk (pairDisjoint_plus hij) (pairDisjoint_plus hik)
    (pairDisjoint_plus hjk) hD ι hYB hcard

@[expose] def PlusFourRefinedF6OffInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ i j k : Fin 4, i ≠ j →
    i ≠ k → j ≠ k → ∀ ι : plusLevi K i j ≃* plusLevi K i j,
    ¬ ((((pairTorus (K := K) k).subgroupOf (plusLevi K i j)).map ι.toMonoidHom).map
      (plusLevi K i j).subtype ≤ stabTwoBar K i j) →
    Nat.card (plusRadical K i j ⊓ centralizer
        (((((pairTorus (K := K) k).subgroupOf (plusLevi K i j)).map ι.toMonoidHom).map
          (plusLevi K i j).subtype : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
            Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
          Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) =
      Nat.card (plusRadical K i j ⊓ centralizer (pairTorus (K := K) k :
          Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
        Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) →
    Nonempty (perfectCore (centralizer
      (((((pairTorus (K := K) k).subgroupOf (plusLevi K i j)).map ι.toMonoidHom).map
        (plusLevi K i j).subtype : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
          Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))) ≃* pairPerp (K := K) k)

@[expose] def PlusFourGLLeviF6Input : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ i j k : Fin 4, i ≠ j →
    i ≠ k → j ≠ k → ∀ Y : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
    Y ≤ plusLevi K i j → IsCyclic Y → Nat.card Y = Nat.card K - 1 → ¬ Y ≤ stabTwoBar K i j →
    Nat.card (plusRadical K i j ⊓ centralizer (Y : Set (matrixProjectiveDerived
        (coordinateQuadPlus 4 K))) : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) =
      Nat.card (plusRadical K i j ⊓ centralizer (pairTorus (K := K) k :
          Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
        Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) →
    Nonempty (perfectCore (centralizer (Y : Set (matrixProjectiveDerived
      (coordinateQuadPlus 4 K)))) ≃* pairPerp (K := K) k)

theorem plusFourRefinedF6OffInput_of_GLLevi (h : PlusFourGLLeviF6Input) :
    PlusFourRefinedF6OffInput := by
  intro K _ _ _ hq i j k hij hik hjk ι hYB hcard
  have hk := isHypCoord_coordinateQuadPlus (K := K) k
  have hJM : pairTorus (K := K) k ≤ plusLevi K i j :=
    (pairTorusOf_le_stabPairsBar (pairDisjoint_plus hik) (pairDisjoint_plus hjk)).trans
      (stabPairsBar_le_rootLeviBar (isHypCoord_coordinateQuadPlus i)
        (isHypCoord_coordinateQuadPlus j))
  set eY : pairTorus (K := K) k ≃* ((((pairTorus (K := K) k).subgroupOf (plusLevi K i j)).map
      ι.toMonoidHom).map (plusLevi K i j).subtype :
        Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :=
    ((subgroupOfEquivOfLe hJM).symm.trans
      (((pairTorus (K := K) k).subgroupOf (plusLevi K i j)).equivMapOfInjective _
        ι.injective)).trans
      ((((pairTorus (K := K) k).subgroupOf (plusLevi K i j)).map ι.toMonoidHom).equivMapOfInjective
        _ (plusLevi K i j).subtype_injective) with heY
  have hYcyc : IsCyclic ((((pairTorus (K := K) k).subgroupOf (plusLevi K i j)).map
      ι.toMonoidHom).map (plusLevi K i j).subtype :
        Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
    have : IsCyclic (pairTorus (K := K) k) := isCyclic_pairTorus k
    exact isCyclic_of_surjective eY eY.surjective
  have hYcard := (Nat.card_congr eY.toEquiv).symm.trans (card_pairTorus (K := K) k)
  exact h K hq i j k hij hik hjk _ (map_subtype_le _) hYcyc hYcard hYB hcard

theorem plusFourRefinedF6Input_of_off (h : PlusFourRefinedF6OffInput) :
    PlusFourRefinedF6Input := by
  intro K _ _ _ hq i j k hij hik hjk ι hcard
  by_cases hYB : (((pairTorus (K := K) k).subgroupOf (plusLevi K i j)).map ι.toMonoidHom).map
      (plusLevi K i j).subtype ≤ stabTwoBar K i j
  · exact refinedF6_pairTorus_four_of_le hq hij hik hjk ι hYB hcard
  · exact h K hq i j k hij hik hjk ι hYB hcard

end CFSG.SeitzReduction.OmegaPilot

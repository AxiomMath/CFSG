module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoConj
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoPlane
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoCard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)
open CFSG.Quasithin (perfectCore)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem anisoTorusOf_le_stabPairsBar {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    {a a' b b' u u' : Fin d} {β γ : K} (hne : u ≠ u') (hdu₁ : PairDisjoint a a' u u')
    (hdu₂ : PairDisjoint b b' u u') :
    anisoTorusOf Q hne β γ ≤ stabPairsBar Q a a' b b' := by
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨p, s, -, htp⟩ := mem_subgroupOf.mp ht
  refine ⟨t, mem_subgroupOf.mpr ?_, rfl⟩
  have hfix : ∀ i, u ≠ i → u' ≠ i →
      (t : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single i 1) = Pi.single i 1 := by
    intro i hiu hiu'
    rw [htp]
    exact anisoRotLin_apply_of_mem_perpSub p s
      ⟨Pi.single_eq_of_ne hiu _, Pi.single_eq_of_ne hiu' _⟩
  exact ⟨⟨hfix a hdu₁.left_ne_left hdu₁.right_ne_left,
      hfix a' hdu₁.left_ne_right hdu₁.right_ne_right⟩,
    hfix b hdu₂.left_ne_left hdu₂.right_ne_left, hfix b' hdu₂.left_ne_right hdu₂.right_ne_right⟩

theorem refinedF6_anisoTorusOf {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {a a' b b' u u' : Fin d} {β γ : K} (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hk : IsAnisoCoord Q u u' β γ) (hd : PairDisjoint a a' b b')
    (hdu₁ : PairDisjoint a a' u u') (hdu₂ : PairDisjoint b b' u u')
    (hS : CFSG.IsQuasisimple (stabPairsBar Q a a' b b') ∧ center (stabPairsBar Q a a' b b') = ⊥)
    (hB4 : Nat.card K ^ 4 ≤ Nat.card (stabPairsBar Q a a' b b'))
    (hD : ⁅pairPerpOf Q u u', pairPerpOf Q u u'⁆ = pairPerpOf Q u u') :
    RefinedF6 (rootRadicalBar Q hi.hypPair hj.hypPair) (rootLeviBar Q hi.hypPair hj.hypPair)
      (anisoTorusOf Q hk.ne β γ) (pairPerpOf Q u u') := by
  classical
  have hXB : anisoTorusOf Q hk.ne β γ ≤ stabPairsBar Q a a' b b' :=
    anisoTorusOf_le_stabPairsBar hk.ne hdu₁ hdu₂
  have hJM : anisoTorusOf Q hk.ne β γ ≤ rootLeviBar Q hi.hypPair hj.hypPair :=
    hXB.trans (stabPairsBar_le_rootLeviBar hi hj)
  set M := rootLeviBar Q hi.hypPair hj.hypPair with hM
  intro ι hcard
  set Y : Subgroup (matrixProjectiveDerived Q) :=
    (((anisoTorusOf Q hk.ne β γ).subgroupOf M).map ι.toMonoidHom).map M.subtype with hYdef
  have hBfix := map_stabPairsBar_subgroupOf_eq hi hj hd hS hB4 ι
  have hYB : Y ≤ stabPairsBar Q a a' b b' := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ ((stabPairsBar Q a a' b b').subgroupOf M).map ι.toMonoidHom :=
      map_mono (fun z hz => mem_subgroupOf.mpr (hXB (mem_subgroupOf.mp hz))) hx
    rw [hBfix] at hx'
    exact mem_subgroupOf.mp hx'
  set eY : anisoTorusOf Q hk.ne β γ ≃* Y :=
    ((subgroupOfEquivOfLe hJM).symm.trans
      (((anisoTorusOf Q hk.ne β γ).subgroupOf M).equivMapOfInjective _ ι.injective)).trans
      ((((anisoTorusOf Q hk.ne β γ).subgroupOf M).map ι.toMonoidHom).equivMapOfInjective _
        M.subtype_injective) with heY
  have hYcard : Nat.card Y = Nat.card (anisoTorusOf Q hk.ne β γ) :=
    (Nat.card_congr eY.toEquiv).symm
  have hcY := card_rootRadicalBar_inf_centralizer hQ hT hi hj hd hYB
  have hcX := card_rootRadicalBar_inf_centralizer hQ hT hi hj hd hXB
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hUeq : Nat.card ↥(fixSpace (Y.comap (projHom Q)) ⊓ subW K a a' b b') =
      Nat.card ↥(fixSpace ((anisoTorusOf Q hk.ne β γ).comap (projHom Q)) ⊓
        subW K a a' b b') := by
    have h := hcard
    rw [hcY, hcX] at h
    exact Nat.pow_left_injective two_ne_zero (Nat.eq_of_mul_eq_mul_left (by omega) h)
  have hFY := card_fixSpace_eq hi hj hd (B := Y.comap (projHom Q))
    fun g hg => mem_stabSub_of_projHom_mem hi hYB hg
  have hFX := card_fixSpace_eq hi hj hd (B := (anisoTorusOf Q hk.ne β γ).comap (projHom Q))
    fun g hg => mem_stabSub_of_projHom_mem hi hXB hg
  have hFX' := hk.card_fixSpace_comap_anisoTorusOf hQ hT
  have hFYc : Nat.card (fixSpace (Y.comap (projHom Q))) = Nat.card K ^ (d - 2) := by
    rw [hFY, hUeq, ← hFX]
    exact hFX'
  have hFYr : finrank K (fixSpace (Y.comap (projHom Q))) = d - 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K)] at hFYc
    exact Nat.pow_right_injective (by omega) hFYc
  have hYodd : Odd (Nat.card Y) := hYcard ▸ hk.odd_card_anisoTorusOf
  have hY2 : Nat.card Y = Nat.card K + 1 := hYcard.trans (hk.card_anisoTorusOf hQ hT)
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : Y, y₁ ≠ 1 := by
    have : Nontrivial Y := by
      rw [← Finite.one_lt_card_iff_nontrivial, hY2]
      omega
    exact exists_ne 1
  obtain ⟨g₀, hg₀⟩ := projHom_surjective Q (y₁ : matrixProjectiveDerived Q)
  have hρ := projHom_injective (Q := Q) hi.exists_ne_zero
  have hord : orderOf ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = orderOf y₁ := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective (projHom _) hρ g₀, hg₀, Subgroup.orderOf_coe]
  have hodd1 : Odd (orderOf y₁) := hYodd.of_dvd_nat (orderOf_dvd_natCard y₁)
  have hodd : Odd (orderOf ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K))) := by
    rw [hord]
    exact hodd1
  have hyq : ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ^ Nat.card K ≠
      ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
    intro hq'
    have hg₀q : g₀ ^ Nat.card K = g₀ := Subtype.ext (by rw [Subgroup.coe_pow]; exact hq')
    have h1 : y₁ ^ Nat.card K = y₁ := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hg₀, ← map_pow, hg₀q]
    have h3 : y₁ ^ (Nat.card K + 1) = 1 := by
      rw [← hY2]
      exact pow_card_eq_one'
    rw [pow_succ, h1] at h3
    have hd2 : orderOf y₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h4 | h4
    · exact hy₁ (orderOf_eq_one_iff.mp h4)
    · rw [h4] at hodd1
      exact absurd hodd1 (by decide)
  have hle : fixSpace (Y.comap (projHom Q)) ≤
      fixSub ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) := fun v hv =>
    hv g₀ (show projHom _ g₀ ∈ Y by rw [hg₀]; exact y₁.2)
  have hF : finrank K (Fin d → K) ≤
      finrank K (fixSub ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K))) + 2 := by
    have := Submodule.finrank_mono hle
    rw [Module.finrank_fin_fun]
    omega
  obtain ⟨hdimF, e, e', he, he', hee', hfix⟩ := exists_anisoPair_of_codim_fix_le_two hQ
    (Subgroup.commutator_le_self _ g₀.2) hodd hyq hF hk.b_ne_zero hk.irr
  have hFeq : fixSpace (Y.comap (projHom Q)) =
      fixSub ((g₀ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [Module.finrank_fin_fun] at hdimF
    omega
  have hYt : ∀ g : orthDerived Q, projHom Q g ∈ Y →
      ∀ x, polar Q x e = 0 → polar Q x e' = 0 → (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) x = x := by
    intro g hg x hxe hxe'
    have hx : x ∈ fixSpace (Y.comap (projHom Q)) := by
      rw [hFeq]
      exact hfix x hxe hxe'
    exact hx g hg
  exact hk.nonempty_perfectCore_centralizer_mulEquiv_pairPerpOf hQ hT hD he he' hee' hYt hYcard

section Minus

variable {n : ℕ}

theorem refinedF6_anisoTorus (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin (n - 1)} (hij : i ≠ j) :
    RefinedF6 (minusRadical (K := K) (by omega) b c i j) (minusLevi (by omega) b c i j)
      (anisoTorus (K := K) (n := n) (by omega) b c)
      (anisoPerp (K := K) (n := n) (by omega) b c) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  obtain ⟨k, hik, hjk, -⟩ := exists_ne_three_fin (by omega : 4 ≤ n - 1) i j i
  have hD : ⁅anisoPerp (K := K) hn1 b c, anisoPerp (K := K) hn1 b c⁆ =
      anisoPerp (K := K) hn1 b c :=
    Subgroup.isPerfect_iff.mp (isQuasisimple_anisoPerp (by omega) hirr).1
  exact refinedF6_anisoTorusOf hQ hT (isHypCoord_coordinateQuadMinus hn1 b c i)
    (isHypCoord_coordinateQuadMinus hn1 b c j) (isAnisoCoord_coordinateQuadMinus hn1 hirr)
    (pairDisjoint_minus hn1 hij) (pairDisjoint_aniso hn1 i).symm (pairDisjoint_aniso hn1 j).symm
    (isQuasisimple_minusStabPairsBar_of_five_le hn hirr hij)
    (card_le_minusStabPairsBar hn hirr hik hjk) hD

theorem rootPairElt_mem_anisoPerp (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j k : Fin (n - 1)} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    rootPairElt (regular_coordinateQuadMinus n K b c hn hirr).1
      ((isHypCoord_coordinateQuadMinus (K := K) (by omega) b c i).orth
        (isHypCoord_coordinateQuadMinus (by omega) b c j) (pairDisjoint_minus (by omega) hij))
      ((isHypCoord_coordinateQuadMinus (K := K) (by omega) b c i).orth
        (isHypCoord_coordinateQuadMinus (by omega) b c k) (pairDisjoint_minus (by omega) hik))
      ((isHypCoord_coordinateQuadMinus (K := K) (by omega) b c j).orth
        (isHypCoord_coordinateQuadMinus (by omega) b c k) (pairDisjoint_minus (by omega) hjk)) ∈
      anisoPerp (by omega) b c := by
  have hn1 : 1 ≤ n := by omega
  have hu := isAnisoCoord_coordinateQuadMinus (K := K) hn1 hirr
  have di := pairDisjoint_aniso hn1 i
  have dj := pairDisjoint_aniso hn1 j
  refine ⟨_, mem_subgroupOf.mpr ⟨eichler_apply_of_polar_eq_zero ?_ ?_,
    eichler_apply_of_polar_eq_zero ?_ ?_⟩, rfl⟩
  · change polar _ (Pi.single (anisoCoordLeft hn1) 1)
      (Pi.single (minusIndexEquiv n hn1 (.inl i)) 1) = 0
    rw [hu.polar_left, Pi.single_eq_of_ne di.left_ne_right.symm, mul_zero]
  · change polar _ (Pi.single (anisoCoordLeft hn1) 1)
      (Pi.single (minusIndexEquiv n hn1 (.inl j)) 1) = 0
    rw [hu.polar_left, Pi.single_eq_of_ne dj.left_ne_right.symm, mul_zero]
  · change polar _ (Pi.single (anisoCoordRight hn1) 1)
      (Pi.single (minusIndexEquiv n hn1 (.inl i)) 1) = 0
    rw [hu.polar_right, Pi.single_eq_of_ne di.left_ne_left.symm, mul_zero]
  · change polar _ (Pi.single (anisoCoordRight hn1) 1)
      (Pi.single (minusIndexEquiv n hn1 (.inl j)) 1) = 0
    rw [hu.polar_right, Pi.single_eq_of_ne dj.left_ne_left.symm, mul_zero]

theorem minusRootElt_decomp_aniso (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j k : Fin (n - 1)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ∃ z : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c),
      z ∈ anisoPerp (by omega) b c ∧ IsLongRoot _ z ∧ z ≠ 1 ∧
      perfectCore (centralizer ({z} : Set (matrixProjectiveDerived
        (coordinateQuadMinus n K (by omega) b c)))) =
        minusRadical (by omega) b c i j ⊔ minusLevi (by omega) b c i j ∧
      IsPGroup 2 (minusRadical (K := K) (by omega) b c i j) ∧
      minusLevi (by omega) b c i j ≤ normalizer (minusRadical (by omega) b c i j :
        Set (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))) ∧
      Disjoint (minusRadical (K := K) (by omega) b c i j) (minusLevi (by omega) b c i j) ∧
      (∀ N : Subgroup (minusLevi (K := K) (by omega) b c i j), N.Normal → IsPGroup 2 N →
        N = ⊥) ∧
      anisoTorus (by omega) b c ≤ minusLevi (by omega) b c i j := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hi := isHypCoord_coordinateQuadMinus (K := K) hn1 b c i
  have hj := isHypCoord_coordinateQuadMinus (K := K) hn1 b c j
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hd := pairDisjoint_minus hn1 hij
  have h₁₂ := hi.orth hj hd
  have h₁₃ := hi.orth hk (pairDisjoint_minus hn1 hik)
  have h₂₃ := hj.orth hk (pairDisjoint_minus hn1 hjk)
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  have hS := isQuasisimple_minusStabPairsBar_of_five_le (K := K) hn hirr hij
  refine ⟨rootPairElt hQ h₁₂ h₁₃ h₂₃, rootPairElt_mem_anisoPerp (by omega) hirr hij hik hjk,
    isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃, rootPairElt_ne_one hQ h₁₂ h₁₃ h₂₃, ?_,
    isPGroup_rootRadicalBar _ _, rootLeviBar_le_normalizer h₁₂,
    disjoint_rootRadicalBar_rootLeviBar h₁₂,
    fun N hN h2 => rootLeviBar_normal_isPGroup_eq_bot_of hi hj hd hQ hT hS N hN h2, ?_⟩
  · rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (commutator_centralizer_rootPairElt_of hi hj hd hQ h₁₃ h₂₃ hl0 hl1
        (Subgroup.isPerfect_iff.mp hS.1.1))]
    exact centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃
  · exact (anisoTorusOf_le_stabPairsBar (anisoCoord_ne hn1) (pairDisjoint_aniso hn1 i).symm
      (pairDisjoint_aniso hn1 j).symm).trans (stabPairsBar_le_rootLeviBar hi hj)

end Minus

end CFSG.SeitzReduction.OmegaPilot

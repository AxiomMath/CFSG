module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PosCore
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoF6

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.Quasithin (perfectCore)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem refinedF6_anisoTorusOf_stabPairsBar {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {a a' b b' u u' : Fin d} {β γ : K} (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hk : IsAnisoCoord Q u u' β γ) (hd : PairDisjoint a a' b b')
    (hdu₁ : PairDisjoint a a' u u') (hdu₂ : PairDisjoint b b' u u')
    (hD : ⁅pairPerpOf Q u u', pairPerpOf Q u u'⁆ = pairPerpOf Q u u') :
    RefinedF6 (rootRadicalBar Q hi.hypPair hj.hypPair) (stabPairsBar Q a a' b b')
      (anisoTorusOf Q hk.ne β γ) (pairPerpOf Q u u') := by
  classical
  have hXB : anisoTorusOf Q hk.ne β γ ≤ stabPairsBar Q a a' b b' :=
    anisoTorusOf_le_stabPairsBar hk.ne hdu₁ hdu₂
  set M := stabPairsBar Q a a' b b' with hM
  intro ι hcard
  set Y : Subgroup (matrixProjectiveDerived Q) :=
    (((anisoTorusOf Q hk.ne β γ).subgroupOf M).map ι.toMonoidHom).map M.subtype with hYdef
  have hYB : Y ≤ stabPairsBar Q a a' b b' := map_subtype_le _
  set eY : anisoTorusOf Q hk.ne β γ ≃* Y :=
    ((subgroupOfEquivOfLe hXB).symm.trans
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

theorem perfectCore_centralizer_rootPairElt_two_of_aniso {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    {a a' b b' c c' u u' : Fin d} {β γ : K} (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hk : IsHypCoord Q c c') (hu : IsAnisoCoord Q u u' β γ) (hij : PairDisjoint a a' b b')
    (hik : PairDisjoint a a' c c') (hjk : PairDisjoint b b' c c')
    (hiu : PairDisjoint a a' u u') (hju : PairDisjoint b b' u u') (hku : PairDisjoint c c' u u')
    (hS : ⁅stabPairsBar Q a a' b b', stabPairsBar Q a a' b b'⁆ = stabPairsBar Q a a' b b') :
    perfectCore (centralizer
        {rootPairElt hQ (hi.orth hj hij) (hi.orth hk hik) (hj.orth hk hjk)}) =
      rootRadicalBar Q hi.hypPair hj.hypPair ⊔ stabPairsBar Q a a' b b' := by
  have hβ := hu.b_ne_zero
  have hxW : (Pi.single u 1 : Fin d → K) ∈ subW K a a' b b' :=
    ⟨⟨Pi.single_eq_of_ne hiu.left_ne_left.symm _, Pi.single_eq_of_ne hiu.left_ne_right.symm _⟩,
      Pi.single_eq_of_ne hju.left_ne_left.symm _, Pi.single_eq_of_ne hju.left_ne_right.symm _⟩
  have hyW : (Pi.single u' 1 : Fin d → K) ∈ subW K a a' b b' :=
    ⟨⟨Pi.single_eq_of_ne hiu.right_ne_left.symm _, Pi.single_eq_of_ne hiu.right_ne_right.symm _⟩,
      Pi.single_eq_of_ne hju.right_ne_left.symm _, Pi.single_eq_of_ne hju.right_ne_right.symm _⟩
  refine perfectCore_centralizer_rootPairElt_two hK hQ hi hj hk hij hik hjk hS hxW
    (Submodule.smul_mem _ β⁻¹ hyW) (Pi.single_eq_of_ne hku.left_ne_left.symm _)
    (Pi.single_eq_of_ne hku.left_ne_right.symm _) ?_ ?_ ?_
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hku.right_ne_left.symm, mul_zero]
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hku.right_ne_right.symm, mul_zero]
  · rw [polar_smul_left_eq, hu.polar_right, Pi.single_eq_same, mul_one, inv_mul_cancel₀ hβ]

end CFSG.SeitzReduction.OmegaPilot

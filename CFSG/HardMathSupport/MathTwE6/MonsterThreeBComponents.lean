module

public import CFSG.HardMathSupport.MathTwE6.MonsterThreeBIrr
public import CFSG.HardMathSupport.MathTwE6.ExtraspecialComponentsApply
public import Certificates.Certificate136201
public import Certificates.Certificate136207

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.MathTwE6.M3BIrr

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (QQ tbL tbL_conj QQ_le_tbL tbb₁_mem
  tbb₂_mem card_QQ not_three_pow_21_dvd factorization_tbL le_zpowers_of_le_CQ isAct_b₁ isAct_b₂)


theorem conj_mem_zpowers {G : Type*} [Group G] {b w : G} (h : b⁻¹ * w * b ∈ Subgroup.zpowers w) :
    ∀ g ∈ Subgroup.zpowers w, b⁻¹ * g * b ∈ Subgroup.zpowers w := by
  rintro _ ⟨k, rfl⟩
  have e : b⁻¹ * w ^ k * b = (b⁻¹ * w * b) ^ k := by
    have := conj_zpow (a := b⁻¹) (b := w) (i := k)
    rw [inv_inv] at this
    exact this.symm
  simp only
  rw [e]
  exact zpow_mem h k

theorem tbL_le_normalizer_zpowers :
    tbL ≤ Subgroup.normalizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  intro b hb
  refine mem_normalizer_of_conj ?_
  refine conj_mem_of_mem_closure (S := {tbb₁, tbb₂} ∪ Set.range tbq) ?_ hb
  rintro b' ((rfl | rfl) | ⟨j, rfl⟩)
  · refine conj_mem_zpowers ?_
    have h2 : tbb₁⁻¹ * tbw * tbb₁ = tbw ^ 2 := isAct_b₁.2
    rw [h2]
    exact pow_mem (Subgroup.mem_zpowers _) _
  · refine conj_mem_zpowers ?_
    have h2 : tbb₂⁻¹ * tbw * tbb₂ = tbw ^ 1 := isAct_b₂.2
    rw [h2]
    exact pow_mem (Subgroup.mem_zpowers _) _
  · refine conj_mem_zpowers ?_
    have hc := tbCommData.commute_of_mem (Subgroup.subset_closure ⟨j, rfl⟩)
      (Subgroup.mem_zpowers tbw)
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact Subgroup.mem_zpowers _

theorem components_dvd_card_mulAut (hirr : irrCheck () = true)
    (hsyl : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.SylFact) :
    ∀ J : Subgroup Gmat,
      CFSG.Open.IsComponentOf J
        (Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat)) →
      9 ∣ (Subgroup.center J).index → 3 ^ 12 ∣ Nat.card (MulAut J) := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  have hcardG : Nat.card Gmat = CFSG.Open.monsterOrder := CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  have hLQ : tbL ≤ Subgroup.normalizer (QQ : Set Gmat) := fun b hb =>
    mem_normalizer_of_conj (tbL_conj b hb)
  have hLX : tbL ≤ Subgroup.normalizer
      (Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) : Set Gmat) :=
    fun b hb => CFSG.HardMathSupport.MathTwE6.mem_normalizer_centralizer
      (tbL_le_normalizer_zpowers hb)
  have hL3 : (Nat.card Gmat).factorization 3 ≤ (Nat.card tbL).factorization 3 := by
    rw [factorization_tbL hsyl]
    by_contra h
    exact not_three_pow_21_dvd (hcardG ▸ (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      Nat.card_pos.ne').2 (by omega))
  have hCQ := CFSG.HardMathSupport.MathTwE6.card_le_three_of_le_centralizer tbw tbw_pow_three QQ
    tbL hLQ hL3 (le_zpowers_of_le_CQ hsyl)
  have hrel : (Subgroup.zpowers tbw).relIndex QQ = 3 ^ 12 := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers tbw) (K := QQ)
    rw [inf_of_le_left (Subgroup.zpowers_le.2 tbCommData.mem_z), Nat.card_zpowers,
      tbCommData.orderOf_z, card_QQ] at h
    omega
  have hidx : ¬ (Subgroup.zpowers tbw).relIndex QQ ∣ (10 : ℕ).factorial := by
    rw [hrel]; decide
  have hG : ¬ 9 ^ (10 + 1) ∣ Nat.card Gmat := fun h =>
    not_three_pow_21_dvd (hcardG ▸ (pow_dvd_pow 3 (by norm_num : 21 ≤ 22)).trans
      (by simpa [show (9 : ℕ) ^ 11 = 3 ^ 22 by norm_num] using h))
  intro J hJ hJ9
  have := CFSG.HardMathSupport.MathTwE6.component_relIndex_dvd_card_mulAut tbw _ QQ tbL 10
    QQ_le_tbL hLQ hLX hCQ (fun N hN hnorm => tbL_dichotomy hirr N hN hnorm) hidx hG J hJ hJ9
  rwa [hrel] at this

theorem components_dvd_card_mulAut_of_certificates :
    ∀ J : Subgroup Gmat,
      CFSG.Open.IsComponentOf J
        (Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat)) →
      9 ∣ (Subgroup.center J).index → 3 ^ 12 ∣ Nat.card (MulAut J) :=
  components_dvd_card_mulAut Certificates.certificate136207
    Certificates.certificate136201

end CFSG.HardMathSupport.MathTwE6.M3BIrr

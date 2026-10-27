module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.MonsterThreeBAllComp
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ThreeCentralLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ThreeOutRank
public import Certificates.Certificate136207

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.MonsterThreeBRank

open CFSG.Open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (QQ tbL card_QQ)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (SylFact)
open CFSG.HardMathSupport.MathTwE6.M3BIrr (irrCheck)
open CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialAll
open CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialOut
open CFSG.HardMathSupport.Dickson.I271.ThreeCentralLeaf (three_central_leaf)
open CFSG.HardMathSupport.Dickson.I271.ThreeOutRank
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo LieOuterRank)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge SporadicOrdersTable)

theorem multiplicative_pow_eq_one {n p : ℕ} (x : Multiplicative (Fin n → ZMod p)) : x ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp

section Glue


theorem card_dvd_monsterOrder_gmat (J : Subgroup Gmat) : Nat.card J ∣ monsterOrder := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  have hG : Nat.card Gmat = monsterOrder := CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  exact hG ▸ Subgroup.card_subgroup_dvd_card J

theorem commutator_mem_zpowers {g h : Gmat} (hg : g ∈ QQ) (hh : h ∈ QQ) :
    g⁻¹ * h⁻¹ * g * h ∈ Subgroup.zpowers tbw :=
  tbCommData.bcomm_mem hg hh

theorem pow_three_mem_zpowers {g : Gmat} (hg : g ∈ QQ) : g ^ 3 ∈ Subgroup.zpowers tbw := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  have h1 : (⟨g, hg⟩ : QQ) ^ 3 ∈ tbCommData.coordHom.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact multiplicative_pow_eq_one _
  rw [tbCommData.ker_coordHom] at h1
  exact Subgroup.mem_subgroupOf.1 h1

theorem not_beta1 (hOut : SporadicOuterLeTwo) (hRank : LieOuterRank)
    (hKG : CFSG.Open.IsKGroup Gmat) (hsyl : SylFact) (hirr : irrCheck () = true)
    {J : Subgroup Gmat} (hJ : M3Beta1 J) : False := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  have S := m3Setup hsyl hirr
  obtain ⟨hJc, -, hQN, hker, -⟩ := hJ
  have hQc : Nat.card QQ = 3 ^ (12 + 1) := by
    rw [card_eq_pow_mul_of_relIndex S.order_w S.hwQ S.hrel]
    ring
  obtain ⟨D, hD, hDc, hDin⟩ := exists_elemAbelian_inner_trivial (p := 3) (k := 12) (m := 3)
    (by norm_num) S.order_w S.hQX hJc.1 S.hwX hJc.2.2.1 hQN hQc hker
    (fun a ha b hb => commutator_mem_zpowers ha hb) (fun a ha => pow_three_mem_zpowers ha)
  exact no_elemAbelian_three_cube hOut hRank hJc.2.2 (hKG.subgroup J) hD hDc hDin

theorem not_beta2a (hGA : GriessAllModelsStatement) (hb : LieOrderBridge)
    (hOut : SporadicOuterLeTwo) (hOrd : SporadicOrdersTable) (hKG : CFSG.Open.IsKGroup Gmat)
    (hsyl : SylFact) (hirr : irrCheck () = true) {J : Subgroup Gmat}
    (hJ : M3Beta2a J) : False := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  have S := m3Setup hsyl hirr
  obtain ⟨hJc, hQJ, -, hXN, hCeq, hZ, h20, -⟩ := hJ
  have hperf : commutator ↥J = ⊤ := hJc.2.2.1
  have hQc : Nat.card QQ = 3 ^ (12 + 1) := by
    rw [card_eq_pow_mul_of_relIndex S.order_w S.hwQ S.hrel]
    ring
  have h13 : 3 ^ (12 + 1) ∣ Nat.card J := hQc ▸ Subgroup.card_dvd_of_le hQJ
  have h12 : 3 ^ 12 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    pow_dvd_card_quot (by norm_num) hZ h13
  have h19 : 3 ^ 19 ∣ Nat.card (MulAut (↥J ⧸ Subgroup.center ↥J)) :=
    pow_dvd_card_mulAut (by norm_num) S.order_w hperf hXN hCeq h20
  exact three_central_leaf hGA hb hOut hOrd hJc.2.2 (hKG.subgroup J) (card_dvd_monsterOrder_gmat J)
    (dvd_of_eq hZ.symm) h12 h19

theorem not_m3Residual (hGA : GriessAllModelsStatement) (hb : LieOrderBridge)
    (hOut : SporadicOuterLeTwo) (hOrd : SporadicOrdersTable) (hRank : LieOuterRank)
    (hKG : CFSG.Open.IsKGroup Gmat) (hsyl : SylFact) (hirr : irrCheck () = true) :
    ¬ ((∃ J, M3Beta1 J) ∨ (∃ J, M3Beta2a J)) := by
  rintro (⟨J, hJ⟩ | ⟨J, hJ⟩)
  · exact not_beta1 hOut hRank hKG hsyl hirr hJ
  · exact not_beta2a hGA hb hOut hOrd hKG hsyl hirr hJ

theorem m3ResBNoComp_of_rank (hGA : GriessAllModelsStatement) (hb : LieOrderBridge)
    (hOut : SporadicOuterLeTwo) (hOrd : SporadicOrdersTable) (hRank : LieOuterRank)
    (hKG : CFSG.Open.IsKGroup Gmat) (hsyl : SylFact) (hirr : irrCheck () = true)
    (hM3 : OPrimeCoreTrivialAt 3 Gmat) : M3ResBNoComp :=
  m3ResBNoComp_of_not_residual hsyl hirr hM3
    (not_m3Residual hGA hb hOut hOrd hRank hKG hsyl hirr)

theorem m3ResBNoComp_of_rank_of_certificates
    (hGA : GriessAllModelsStatement) (hb : LieOrderBridge)
    (hOut : SporadicOuterLeTwo) (hOrd : SporadicOrdersTable) (hRank : LieOuterRank)
    (hKG : CFSG.Open.IsKGroup Gmat) (hM3 : OPrimeCoreTrivialAt 3 Gmat) : M3ResBNoComp :=
  m3ResBNoComp_of_rank hGA hb hOut hOrd hRank hKG Certificates.certificate136201
    Certificates.certificate136207 hM3

end Glue

end CFSG.HardMathSupport.Dickson.I271.MonsterThreeBRank

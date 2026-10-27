module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwoLocalLevi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperShared
public import CFSG.RankThree.PartOne.S15K.FamilyBlock
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLevi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2U5Fam
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly

@[expose] def Rk2E8LeviRankInput (p : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], p ∣ Nat.card F + 1 →
    ∀ (i : Fin Tag.E8.rank), ∀ E : Subgroup (ModGL Tag.E8 F),
      E ≤ subsystemGroup Tag.E8 F {j | j ≠ i} → IsElemAbelian p E → Nat.card E ≤ p ^ 7

theorem levi_card_le_seven {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1) (hLev : Rk2E8LeviRankInput p)
    {J : Set (Fin Tag.E8.rank)} (hJ : J ≠ Set.univ)
    {E : Subgroup (ModGL Tag.E8 K)} (hE : E ≤ subsystemGroup Tag.E8 K J)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra hall
    push Not at hall
    exact hJ (Set.eq_univ_of_forall hall)
  exact hLev K hd i E
    (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono
      (fun j hj hji => hi (hji ▸ hj)))) hEel

theorem twoLocal_card_le_seven_adjointGroup_E8 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    (hLev : Rk2E8LeviRankInput p) :
    ∀ R E : Subgroup (adjointGroup Tag.E8 K), R ≠ ⊥ → IsPGroup 2 R →
      E ≤ Subgroup.normalizer (R : Set (adjointGroup Tag.E8 K)) → IsElemAbelian p E →
      Nat.card E ≤ p ^ 7 := by
  haveI : Fintype K := Fintype.ofFinite K
  exact fun R E hR hR2 hER hE =>
  twoLocal_card_le_of_levi' hp hp2
    (CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd)
    (fun J hJ E hE hEel => levi_card_le_seven hp hp2 hd hLev hJ hE hEel) hR hR2 hER hE

theorem twoLocalRank_le_seven_adjointGroup_E8 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    (hLev : Rk2E8LeviRankInput p) :
    GLATwoLocalRank p (adjointGroup Tag.E8 K) ≤ 7 :=
  CFSG.LocalAnalysis.GLTheoremA.glaTwoLocalRank_le_of_card_le hp
    (twoLocal_card_le_seven_adjointGroup_E8 hp hp2 hd hLev)

theorem rk2_up_e8_of_levi {K : Type} [Group K] [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab)
    (ht : lab.tag = .E8) (hn : 2 ≤ lab.n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ lab.n + 1) (hLev : Rk2E8LeviRankInput p) :
    GLATwoLocalRank p K < rk2LieRank lab := by
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E8 0 2 lab.n :=
    lieModel_of_markedModel_E8 ht hM
  obtain ⟨-, F, hF, hFin, hFcard, ⟨φ⟩⟩ := hM'.chevalleyExceptionalModel
    (by decide : StatedLieTag.E8 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  letI : Field F := hF
  letI : Finite F := hFin
  have hn1 : 1 ≤ lab.n := by omega
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := lab.n) hn1 hFcard
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hZ : Subgroup.center K = ⊥ :=
    rk2_center_eq_bot_of_large hK (Or.inr (Or.inr (Or.inr (Or.inr ht)))) hn
  let χ : AdjointQuotient .E8 F ≃* adjointGroup Tag.E8 F :=
    (QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := Tag.E8) (K := F))).trans QuotientGroup.quotientBot
  let eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq (by rw [hZ]))
  let e : K ≃* adjointGroup Tag.E8 F := (eK.trans φ).trans χ
  have hGL : GLATwoLocalRank p K = GLATwoLocalRank p (adjointGroup Tag.E8 F) :=
    le_antisymm (rk2_twoLocal_equiv_le hp e) (rk2_twoLocal_equiv_le hp e.symm)
  have hdF : p ∣ Nat.card F + 1 := by rw [hFcard]; exact hd
  have hbound := twoLocalRank_le_seven_adjointGroup_E8 (K := F) hp hp2 hdF hLev
  have h8 : rk2LieRank lab = 8 := by rw [rk2LieRank, ht]
  rw [hGL, h8]
  exact lt_of_le_of_lt hbound (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA

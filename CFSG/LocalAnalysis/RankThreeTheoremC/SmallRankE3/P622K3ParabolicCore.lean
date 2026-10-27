module

public import CFSG.LieType.SteinbergBRLinearSmallParabolic
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3SectionTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Parab
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

theorem projSL3_parabolic_section {F : Type} [Field F] [Finite F] [CharP F 2]
    (h8 : 8 ≤ Nat.card F) (h3 : ¬ 3 ∣ Nat.card F - 1) {d : ℕ} (hd1 : 1 ≤ d) (hd3 : d < 3)
    {z : projectiveSL 3 F} (hz : orderOf z = 3)
    (hzP : z ∈ (stabilizer (flagSpace 3 F d)).map (proj 3 F)) :
    ∃ H N : Subgroup (projectiveSL 3 F),
      H ≤ (stabilizer (flagSpace 3 F d)).map (proj 3 F) ∧ S622IsSimpleSection H N ∧ z ∈ H ∧
        z ∉ N ∧ 3 ∣ N.relIndex H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hev : Even (Nat.card F) := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.mpr (FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2))
  have hfin : Module.finrank F (flagSpace 3 F d) = d := finrank_flagSpace (by omega)
  set W := flagSpace 3 F d with hW
  set P : Subgroup (projectiveSL 3 F) := (stabilizer W).map (proj 3 F) with hP
  set B : Subgroup (projectiveSL 3 F) := (CFSG.perfectResidual P).map P.subtype with hB
  obtain ⟨-, -, hNB, -, hrad, ⟨e1⟩, ⟨e2⟩, hcardN, -, -, -, -⟩ :=
    CFSG.LieType.linear_small_parabolic_perfect_residual_structure
      hev hd1 hd3 (Or.inl ⟨rfl, by omega⟩) W hfin hP hB
  set Nr : Subgroup (projectiveSL 3 F) :=
    (CFSG.LieType.SteinbergBR.BlockPar.radU F W).map (proj 3 F) with hNr
  have hm : max d (3 - d) = 2 := by interval_cases d <;> rfl
  rw [hm] at e1 e2
  have hsl2 : IsSimpleGroup SL(2, F) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136.isSimpleGroup_SL2 F
      (by omega)
  have hnc : ∃ a b : SL(2, F), a * b ≠ b * a :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136.SL2_nonabelian F
  haveI hDn : (Nr.subgroupOf B).Normal := by rw [← hrad]; infer_instance
  let e : ↥B ⧸ Nr.subgroupOf B ≃* SL(2, F) :=
    (QuotientGroup.quotientMulEquivOfEq hrad).symm.trans (e1.trans e2)
  have hsec : S622IsSimpleSection B Nr := isSimpleSection_of_quotient_equiv hNB e hsl2 hnc
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card F = 2 ^ k := by
    have := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hq3 : ¬ 3 ∣ Nat.card F := by
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hq2 : Nat.card F % 3 = 2 := by omega
  have hcardSL2 : Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F
  have hdexp : d * (3 - d) = 2 := by interval_cases d <;> rfl
  have hcardNr : Nat.card Nr = Nat.card F ^ 2 := by rw [hcardN, hdexp]
  have hcardB : Nat.card B = Nat.card F ^ 2 * (Nat.card F * (Nat.card F ^ 2 - 1)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Nr.subgroupOf B)
    have h2 : Nat.card (↥B ⧸ Nr.subgroupOf B) = Nat.card SL(2, F) := Nat.card_congr e.toEquiv
    have h3' : Nat.card (Nr.subgroupOf B) = Nat.card Nr :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv
    rw [h1, h2, h3', hcardSL2, hcardNr, mul_comm]
  have hscal : Nat.card (scalars 3 F) = 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.card_scalars_eq_gcd F (by norm_num : 1 ≤ 3)]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hcardSL3 : Nat.card SL(3, F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
    rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv]
    exact CFSG.Open.StatedAPI.card_statedSL_three F
  have hcardG : Nat.card (projectiveSL 3 F) = Nat.card SL(3, F) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars 3 F)
    rw [hscal, mul_one] at h
    exact h.symm
  have hBindex : B.index = Nat.card F ^ 3 - 1 := by
    have h1 := Subgroup.card_mul_index B
    rw [hcardB, hcardG, hcardSL3] at h1
    have ha : 0 < Nat.card F ^ 2 - 1 := by
      have : 8 * 8 ≤ Nat.card F ^ 2 := by
        rw [sq]; exact Nat.mul_le_mul h8 h8
      omega
    have hpos : 0 < Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) :=
      Nat.mul_pos (pow_pos (by omega) 3) ha
    have h2 : Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * B.index =
        Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by
      calc Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * B.index
          = Nat.card F ^ 2 * (Nat.card F * (Nat.card F ^ 2 - 1)) * B.index := by ring
        _ = Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := h1
        _ = Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hBP : B ≤ P := Subgroup.map_subtype_le _
  have hrel : B.relIndex P ∣ Nat.card F ^ 3 - 1 := by
    have h1 := Subgroup.relIndex_mul_index hBP
    rw [← hBindex, ← h1]
    exact Dvd.intro _ rfl
  have hq3m : ¬ 3 ∣ Nat.card F ^ 3 - 1 := by
    have hpow : Nat.card F ^ 3 % 3 = 2 := by
      rw [Nat.pow_mod, hq2]
    omega
  have hzB : z ∈ B := by
    haveI hBn : (B.subgroupOf P).Normal := by
      have hBP' : B.subgroupOf P = CFSG.perfectResidual P := by
        rw [hB]
        exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
      rw [hBP']
      unfold CFSG.perfectResidual
      exact Subgroup.normal_iInf_normal fun n => derivedSeries_normal _ n
    have hz3' : z ^ 3 = 1 := by
      have h := pow_orderOf_eq_one z
      rwa [hz] at h
    have hzP3 : (⟨z, hzP⟩ : ↥P) ^ 3 = 1 := Subtype.ext hz3'
    have hmk : (QuotientGroup.mk (⟨z, hzP⟩ : ↥P) : ↥P ⧸ B.subgroupOf P) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hzP3]
      rfl
    have hord : orderOf (QuotientGroup.mk (⟨z, hzP⟩ : ↥P) : ↥P ⧸ B.subgroupOf P) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one hmk
    have hcardQ : Nat.card (↥P ⧸ B.subgroupOf P) = B.relIndex P :=
      (Subgroup.index_eq_card (B.subgroupOf P)).symm
    have hord2 : orderOf (QuotientGroup.mk (⟨z, hzP⟩ : ↥P) : ↥P ⧸ B.subgroupOf P) ∣
        B.relIndex P := hcardQ ▸ orderOf_dvd_natCard _
    have hcop : Nat.Coprime 3 (B.relIndex P) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h => hq3m (h.trans hrel)
    have hone : orderOf (QuotientGroup.mk (⟨z, hzP⟩ : ↥P) : ↥P ⧸ B.subgroupOf P) = 1 :=
      Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hord hord2)
    have hmk1 : (QuotientGroup.mk (⟨z, hzP⟩ : ↥P) : ↥P ⧸ B.subgroupOf P) = 1 :=
      orderOf_eq_one_iff.mp hone
    have hmem : (⟨z, hzP⟩ : ↥P) ∈ B.subgroupOf P := (QuotientGroup.eq_one_iff _).mp hmk1
    exact (Subgroup.mem_subgroupOf).mp hmem
  have hzNr : z ∉ Nr := by
    intro hmem
    have h1 : orderOf (⟨z, hmem⟩ : Nr) ∣ Nat.card Nr := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hz, hcardNr, hk, ← pow_mul] at h1
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have h3rel : 3 ∣ Nr.relIndex B := by
    have h1 : Nr.relIndex B = Nat.card (↥B ⧸ Nr.subgroupOf B) := Subgroup.index_eq_card _
    rw [h1, Nat.card_congr e.toEquiv, hcardSL2]
    have hsq : Nat.card F ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod, hq2]
    have : 3 ∣ Nat.card F ^ 2 - 1 := by omega
    exact Dvd.dvd.mul_left this _
  exact ⟨B, Nr, hBP, hsec, hzB, hzNr, h3rel⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

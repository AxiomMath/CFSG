module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviGeneric
public import CFSG.LieType.SteinbergBRLinearSmallParabolic
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Parab
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherExtremalParabolics

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open scoped MatrixGroups
open Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

section Numerics

variable {F : Type} [Field F] [Finite F]

theorem card_projStab_mul {d : ℕ} (hd1 : 1 ≤ d) (hd3 : d < 3) :
    Nat.card ((stabilizer (flagSpace 3 F d)).map (proj 3 F)) * Nat.card (scalars 3 F) *
        (Nat.card F ^ 2 + Nat.card F + 1) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hqQ : (2 : ℚ) ≤ (Nat.card F : ℚ) := by exact_mod_cast hq
  have hne : (Nat.card F : ℚ) - 1 ≠ 0 := by
    have : (0 : ℚ) < (Nat.card F : ℚ) - 1 := by linarith
    exact this.ne'
  have hfin : Module.finrank F (flagSpace 3 F d) = d :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.finrank_flagSpace (by omega)
  have hidxQ : ((projStabilizer (flagSpace 3 F d)).index : ℚ) =
      (Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.index_projStabilizer, hfin]
    obtain rfl | rfl : d = 1 ∨ d = 2 := by omega
    · rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.gaussianCoeff_one, div_eq_iff hne]
      ring
    · rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.gaussianCoeff_symm hq
          (by norm_num : (2 : ℕ) ≤ 3),
        show (3 : ℕ) - 2 = 1 from rfl,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.gaussianCoeff_one, div_eq_iff hne]
      ring
  have hidx : (projStabilizer (flagSpace 3 F d)).index = Nat.card F ^ 2 + Nat.card F + 1 := by
    exact_mod_cast hidxQ
  have h1 : Nat.card (projStabilizer (flagSpace 3 F d)) *
      (projStabilizer (flagSpace 3 F d)).index = Nat.card (projectiveSL 3 F) :=
    Subgroup.card_mul_index (projStabilizer (flagSpace 3 F d))
  have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card (projectiveSL 3 F) * Nat.card (scalars 3 F) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars 3 F)
  have hprod : ∏ j ∈ Finset.Icc 2 3, (Nat.card F ^ j - 1) =
      (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by
    rw [Finset.prod_Icc_succ_top (show 2 ≤ 2 + 1 by norm_num), Finset.Icc_self,
      Finset.prod_singleton]
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num : 1 ≤ 3),
      show 3 * (3 - 1) / 2 = 3 from rfl, hprod]
  show Nat.card (projStabilizer (flagSpace 3 F d)) * Nat.card (scalars 3 F) *
      (Nat.card F ^ 2 + Nat.card F + 1) =
    Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1))
  calc Nat.card (projStabilizer (flagSpace 3 F d)) * Nat.card (scalars 3 F) *
        (Nat.card F ^ 2 + Nat.card F + 1)
      = Nat.card (projStabilizer (flagSpace 3 F d)) *
          (projStabilizer (flagSpace 3 F d)).index * Nat.card (scalars 3 F) := by
        rw [hidx]; ring
    _ = Nat.card (projectiveSL 3 F) * Nat.card (scalars 3 F) := by rw [h1]
    _ = Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) := h2.symm
    _ = Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := hSL

theorem card_projStab_mul' {d : ℕ} (hd1 : 1 ≤ d) (hd3 : d < 3) :
    Nat.card ((stabilizer (flagSpace 3 F d)).map (proj 3 F)) * Nat.card (scalars 3 F) =
      Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F - 1) := by
  have h := card_projStab_mul (F := F) hd1 hd3
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 1 := ⟨Nat.card F - 1, by omega⟩
  have h3 : Nat.card F ^ 3 - 1 = (Nat.card F - 1) * (Nat.card F ^ 2 + Nat.card F + 1) := by
    rw [hr]
    have : (r + 1) ^ 3 = r * ((r + 1) ^ 2 + (r + 1) + 1) + 1 := by ring
    simp only [Nat.add_sub_cancel]
    omega
  rw [h3] at h
  have hpos : 0 < Nat.card F ^ 2 + Nat.card F + 1 := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h]
  ring

end Numerics

theorem projSL3_dvd_card_succ {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card F - 1) {d : ℕ} (hd1 : 1 ≤ d) (hd3 : d < 3)
    {z : projectiveSL 3 F} (hz : orderOf z = p)
    (hzP : z ∈ (stabilizer (flagSpace 3 F d)).map (proj 3 F)) :
    p ∣ Nat.card F + 1 ∧ 4 ≤ Nat.card F := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hev : Even (Nat.card F) := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.mpr (FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card F = 2 ^ k := by
    have := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  set W := flagSpace 3 F d with hW
  set P : Subgroup (projectiveSL 3 F) := (stabilizer W).map (proj 3 F) with hP
  have hpP : p ∣ Nat.card P := by
    have h1 : orderOf (⟨z, hzP⟩ : ↥P) ∣ Nat.card P := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hz] at h1
  have hPg := card_projStab_mul' (F := F) hd1 hd3
  have hpq0 : ¬ p ∣ Nat.card F := by
    rw [hk]
    intro h
    have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 1 := ⟨Nat.card F - 1, by omega⟩
  have hsq : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    rw [hr]
    have : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
    simp only [Nat.add_sub_cancel]
    omega
  have hpq1 : p ∣ Nat.card F + 1 := by
    have h1 : p ∣ Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F - 1) := by
      rw [← hPg]
      exact Dvd.dvd.mul_right hpP _
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · exact absurd (hp.dvd_of_dvd_pow h3) hpq0
      · rw [hsq] at h3
        rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
        · exact absurd h4 hpq
        · exact h4
    · exact absurd h2 hpq
  have hq4 : 4 ≤ Nat.card F := by
    have := Nat.le_of_dvd (by omega) hpq1
    omega
  exact ⟨hpq1, hq4⟩

theorem projSL3_levi {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card F - 1) {d : ℕ} (hd1 : 1 ≤ d) (hd3 : d < 3)
    {z : projectiveSL 3 F} (hz : orderOf z = p)
    (hzP : z ∈ (stabilizer (flagSpace 3 F d)).map (proj 3 F)) :
    LeviSec p ((stabilizer (flagSpace 3 F d)).map (proj 3 F)) z ∧
      LeviHom ((stabilizer (flagSpace 3 F d)).map (proj 3 F))
        (Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hev : Even (Nat.card F) := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.mpr (FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card F = 2 ^ k := by
    have := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  set W := flagSpace 3 F d with hW
  set P : Subgroup (projectiveSL 3 F) := (stabilizer W).map (proj 3 F) with hP
  have hPg := card_projStab_mul' (F := F) hd1 hd3
  obtain ⟨hpq1, hq4⟩ := projSL3_dvd_card_succ hp hp5 hpq hd1 hd3 hz hzP
  obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 1 := ⟨Nat.card F - 1, by omega⟩
  have hsq : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    rw [hr]
    have : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
    simp only [Nat.add_sub_cancel]
    omega
  have hfin : Module.finrank F W = d := finrank_flagSpace (by omega)
  have hBdef : leviY P = (CFSG.perfectResidual ↥P).map P.subtype := leviY_eq_map_perfectResidual P
  set B : Subgroup (projectiveSL 3 F) := leviY P with hBset
  obtain ⟨-, -, hNB, hpc, hrad, ⟨e1⟩, ⟨e2⟩, hcardN, -, -, -, -⟩ :=
    CFSG.LieType.linear_small_parabolic_perfect_residual_structure hev hd1 hd3
      (Or.inl ⟨rfl, hq4⟩) W hfin hP hBdef
  set Nr : Subgroup (projectiveSL 3 F) :=
    (CFSG.LieType.SteinbergBR.BlockPar.radU F W).map (proj 3 F) with hNr
  have hm : max d (3 - d) = 2 := by interval_cases d <;> rfl
  rw [hm] at e1 e2
  have hsl2 : IsSimpleGroup SL(2, F) := Parrott.P614.P614K136.isSimpleGroup_SL2 F (by omega)
  have hnc : ∃ a b : SL(2, F), a * b ≠ b * a := Parrott.P614.P614K136.SL2_nonabelian F
  haveI hDn : (Nr.subgroupOf B).Normal := by rw [← hrad]; infer_instance
  let e : ↥B ⧸ Nr.subgroupOf B ≃* SL(2, F) :=
    (QuotientGroup.quotientMulEquivOfEq hrad).symm.trans (e1.trans e2)
  have hsec : S622IsSimpleSection B Nr := isSimpleSection_of_quotient_equiv hNB e hsl2 hnc
  have hWeq : leviW P = Nr := by
    unfold leviW CFSG.Open.pCoreOf
    rw [← hBset, hpc, hrad]
    exact Subgroup.map_subgroupOf_eq_of_le hNB
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
  have hBP : B ≤ P := leviY_le P
  have hrelBP : B.relIndex P * Nat.card (scalars 3 F) = Nat.card F - 1 := by
    have h1 := Subgroup.relIndex_mul_card (H := B) (K := P)
    rw [inf_of_le_left hBP, hcardB] at h1
    have hpos : 0 < Nat.card F ^ 2 * (Nat.card F * (Nat.card F ^ 2 - 1)) := by
      have : 1 < Nat.card F ^ 2 := by nlinarith
      exact Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc Nat.card F ^ 2 * (Nat.card F * (Nat.card F ^ 2 - 1)) *
          (B.relIndex P * Nat.card (scalars 3 F))
        = (B.relIndex P * (Nat.card F ^ 2 * (Nat.card F * (Nat.card F ^ 2 - 1)))) *
          Nat.card (scalars 3 F) := by ring
      _ = Nat.card P * Nat.card (scalars 3 F) := by rw [h1]
      _ = Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F - 1) := hPg
      _ = Nat.card F ^ 2 * (Nat.card F * (Nat.card F ^ 2 - 1)) * (Nat.card F - 1) := by ring
  have hrelq : ¬ p ∣ B.relIndex P := fun h =>
    hpq (h.trans (Dvd.intro _ hrelBP))
  have hBn : (B.subgroupOf P).Normal := CFSG.Quasithin.perfectCore_normal P
  have hzB : z ∈ B := mem_of_orderOf_prime_of_coprime_relIndex hBP hBn hp hrelq hzP hz
  have hrel : Nr.relIndex B = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_congr e.toEquiv, hcardSL2]
  have hprel : p ∣ Nr.relIndex B := by
    rw [hrel]
    refine Dvd.dvd.mul_left ?_ _
    rw [hsq]
    exact Dvd.dvd.mul_left hpq1 _
  have hpNr : ¬ p ∣ Nat.card Nr := by
    rw [hcardNr, hk, ← pow_mul]
    intro h
    have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  unfold LeviSec LeviHom
  rw [hWeq]
  refine ⟨⟨hzB, hsec, hprel, hpNr⟩, ?_⟩
  refine ⟨(e : _ →* _).comp (QuotientGroup.mk' (Nr.subgroupOf B)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  rw [MonoidHom.ker_mulEquiv_comp, QuotientGroup.ker_mk']

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

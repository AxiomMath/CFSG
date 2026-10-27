module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Split

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open

section Certificate

private theorem one_le_of_two_le_rk2Ord {p n : ℕ} (h : 2 ≤ rk2Ord p n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · exfalso
    rw [h0] at h
    simp [rk2Ord] at h
  · exact h0

theorem i165On_famA_of_engine (hE : SL165EngineFamA) : I165On i165FamA := by
  refine i165On_of_cover ?_
  intro K _ _ lab p q hK hP hp hp2 hq hq2 hqp hns he hm4
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hm0, hd⟩ := hP
  subst ht
  have hm0' : 2 ≤ rk2Ord p n := hm0
  have hd' : 3 * rk2Ord p n ≤ l + 1 := hd
  have hn1 : 1 ≤ n := one_le_of_two_le_rk2Ord hm0'
  obtain ⟨hQ, hlam, hMo⟩ := rk2_model_of_isLabel hK
  obtain ⟨F, hField, hFinite, hcard, ⟨e⟩⟩ :=
    exists_model_psl_of_isLabel (n := n) (d := l + 1) hMo rfl rfl rfl rfl
  letI : Field F := hField
  letI : Fintype F := Fintype.ofFinite F
  have hFcard : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3 := by
    have h3 : 3 ≤ GLATwoLocalRank q K := by omega
    obtain ⟨lab', hlab', hs⟩ :=
      rk2_split16_of_tables_holds hq hq2 (hasLabel_mono (fun _ _ => trivial) hK) h3 he.symm
    exact dvd_two_pow_sub_one_or_eq_three_of_hasLabel_of_exists_split16 hm4 hK
      ⟨lab', hlab', hs⟩ (by trivial)
  have hsmall : 2 ≤ n ∨ 3 ≤ rk2Ord p n := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · right
      have hn : n = 1 := by omega
      have hne : rk2Ord p n ≠ 2 := by
        intro h2
        have hp3 : p = 3 := (rk2Ord_one_eq_two_iff hp hp2).1 (by rwa [hn] at h2)
        subst hp3
        exact hns ⟨.A, l, 1⟩ (by rw [← hn]; exact hK)
          (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
      omega
    · exact Or.inl hge
  have hd3 : 3 ≤ l + 1 := by omega
  have hd5 : 5 ≤ l + 1 := by omega
  have hmult : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedSL (l + 1) F))) =
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin (l + 1)) F)) := by
    rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv,
      card_hopfMultiplier_statedProj_of_five_le (F := F) (d := l + 1) hd5,
      card_center_specialLinearGroup_eq_gcd (d := l + 1) (by omega)]
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open K).2 hQ)
  obtain ⟨φ, hφ, hφker⟩ := exists_surjective_statedSL_of_model hQ' e hd3 hmult
  have hpF : ¬ p ∣ Fintype.card F - 1 := by
    rw [hFcard]
    intro h
    have h1 : rk2Ord p n = 1 := rk2Ord_eq_one_iff.2 h
    omega
  have hScalCard : Nat.card ((StatedScalars (Fin (l + 1)) F).subgroupOf
      (StatedSL (l + 1) F)) ∣ Fintype.card F - 1 := by
    rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars (l + 1) F,
      Subgroup.card_map_of_injective
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (l + 1) F).injective,
      card_center_specialLinearGroup_eq_gcd (d := l + 1) (by omega)]
    exact Nat.gcd_dvd_right _ _
  have hpk : ¬ p ∣ Nat.card φ.ker := fun h =>
    hpF ((h.trans (Subgroup.card_dvd_of_le hφker)).trans hScalCard)
  have hsc_center : (StatedScalars (Fin (l + 1)) F).subgroupOf (StatedSL (l + 1) F) ≤
      Subgroup.center ↥(StatedSL (l + 1) F) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxS : ((x : ↥(StatedSL (l + 1) F)) : GL (Fin (l + 1)) F) ∈
        StatedScalars (Fin (l + 1)) F := hx
    obtain ⟨c, hc⟩ := hxS
    have hx' : ((x : ↥(StatedSL (l + 1) F)) : GL (Fin (l + 1)) F) =
        Matrix.GeneralLinearGroup.scalar (Fin (l + 1)) c := hc.symm
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx']
    exact (Matrix.GeneralLinearGroup.scalar_commute c (y : GL (Fin (l + 1)) F)).symm
  refine ⟨↥(StatedSL (l + 1) F), inferInstance, inferInstance, φ, hφ,
    hφker.trans hsc_center, hpk, ?_⟩
  intro Ã hÃe hÃmax hÃ3
  obtain ⟨D, E, F', J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3, hFZ⟩ :=
    hE F n (l + 1) p q hFcard hp hp2 hq hq2 hqp hm0' hd' hsmall hqdiv Ã hÃe hÃmax hÃ3
  exact ⟨D, E, F', J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3,
    le_bot_iff.mp ((inf_le_inf_left F' hφker).trans (le_of_eq hFZ))⟩

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F

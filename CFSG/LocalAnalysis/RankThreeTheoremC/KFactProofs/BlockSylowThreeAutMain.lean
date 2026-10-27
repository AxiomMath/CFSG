module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockSylowThreeAutQuasi
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockSylowThreeAutAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsGlue
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Reduce
public import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique CFSG.HardMathSupport.Curtis.NaturalModuleCensus

@[expose] def OrderNineWitnessStatement : Prop :=
  (∀ {X : Type} [Group X] {n : ℕ}, StatedClassicalModel X .PSL n 2 1 → 6 ≤ n →
    ∃ x : X, orderOf x = 9) ∧
  (∀ {X : Type} [Group X] {n : ℕ}, StatedClassicalModel X .PSp n 2 1 → ∃ x : X, orderOf x = 9) ∧
  (∀ {X : Type} [Group X] {n : ℕ}, StatedClassicalModel X .POmegaPlus n 2 1 →
    ∃ x : X, orderOf x = 9) ∧
  (∀ {X : Type} [Group X] {n : ℕ}, StatedClassicalModel X .POmegaMinus n 2 1 →
    ∃ x : X, orderOf x = 9) ∧
  (∀ {X : Type} [Group X] {n : ℕ}, StatedClassicalModel X .PSU n 2 1 → 4 ≤ n →
    ∃ x : X, orderOf x = 9)

theorem coprime_three_card_of_perfect_of_solvable {W : Type*} [Group W] {J : Subgroup W}
    (hJ : Group.IsSolvable J) {U : Subgroup W} (hUJ : U ≤ J) (hU : ⁅U, U⁆ = U) :
    Nat.Coprime 3 (Nat.card U) := by
  have hUs : Group.IsSolvable U := solvable_of_solvable_injective (Subgroup.inclusion_injective hUJ)
  by_cases hbot : U = ⊥
  · subst hbot
    simp
  · exfalso
    haveI : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hbot
    haveI : Group.IsPerfect U := Subgroup.isPerfect_iff.mpr hU
    exact Group.IsPerfect.not_isSolvable U hUs

theorem not_27_dvd_card_mulAut_of_parab
    (hGA : CFSG.Open.GriessAllModelsStatement) (hExc : SuOddThreeDvdStatement hGA)
    (hWit : OrderNineWitnessStatement) {W : Type} [Group W] [Finite W]
    (hW : CFSG.Open.IsQuasisimple W) (hcl : IsClassicalTwoOrG2 (W ⧸ Subgroup.center W))
    {T J : Subgroup W} (hT : IsSylowTwoOf T ⊤) (hNJ : Subgroup.normalizer (T : Set W) ≤ J)
    (hJ : J ≠ Subgroup.normalizer (T : Set W))
    (hperf : ∀ U : Subgroup W, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    (hidx : ¬ 3 ∣ J.index) : ¬ 27 ∣ Nat.card (MulAut W) := by
  intro h27
  have : Group.IsPerfect W := ⟨hW.1⟩
  have hX0 := center_centerQuotient_eq_bot hW
  have h27X : 27 ∣ Nat.card (MulAut (W ⧸ Subgroup.center W)) :=
    h27.trans (card_mulAut_dvd_of_perfect W)
  obtain ⟨S, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  have hψ : Function.Surjective (QuotientGroup.mk' (Subgroup.center W)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center W)).ker ≤ Subgroup.center W :=
    (QuotientGroup.ker_mk' _).le
  obtain ⟨hTb, hNb, hJb, hperfb⟩ := map_overgroup_of_central hψ hker S hNJ hJ hperf
  rcases kFactParabolicThreeCensus _ hcl _ _ hTb hNb hJb hperfb with ⟨d, hd, ⟨e⟩⟩ | hsmall
  ·
    obtain ⟨t, n, ht, hc⟩ := exists_model_of_indexTwo d hd e
    by_cases hsm : t = .PSL ∧ n ≤ 5
    · obtain ⟨rfl, hn⟩ := hsm
      exact not_27_dvd_card_mulAut_of_model_psl_two hX0 hc hn h27X
    · rcases threeSubgroups_of_quasisimple hGA hExc hW hc ht
        (fun htu => (CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.1 htu) S J hNJ hJ hperf
        with hE | h3
      · have hwit : ∃ x : W ⧸ Subgroup.center W, orderOf x = 9 := by
          rcases ht with rfl | rfl | rfl | rfl | rfl
          · exact hWit.1 hc (by
              by_contra h6
              exact hsm ⟨rfl, by omega⟩)
          · exact hWit.2.1 hc
          · exact hWit.2.2.1 hc
          · exact hWit.2.2.2.1 hc
          · obtain ⟨-, -, hn3, hne⟩ := hc.1
            exact hWit.2.2.2.2 hc (by
              by_contra h4
              exact hne (by rw [show n = 3 by omega]; rfl))
        obtain ⟨x, hx⟩ := hwit
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
        exact false_of_elemAbelian_of_nine_dvd_orderOf hidx hE
          (hx ▸ orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center W)) y)
      · exact hidx h3
  ·
    rcases hsmall with ⟨m, hm, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
    · exact not_27_dvd_card_mulAut_of_equiv_alt hX0 hm e h27X
    · rcases hd with ⟨q, hq, hd'⟩ | ⟨q, hq, hd'⟩
      ·
        obtain ⟨dd, hv⟩ := d
        simp only at hd'
        subst hd'
        obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
        have hc := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
        rw [hp, hf] at hc
        exact not_27_dvd_card_mulAut_of_model_psl_seven hX0 hc h27X
      ·
        obtain ⟨dd, hv⟩ := d
        simp only at hd'
        subst hd'
        obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
        have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
        rw [hp, hf] at hc
        have hNF := nineFreeOver_catalog_psu_three_three hq rfl e
        have hXp : ⁅(⊤ : Subgroup (W ⧸ Subgroup.center W)),
            (⊤ : Subgroup (W ⧸ Subgroup.center W))⁆ = ⊤ := by
          have : Group.IsPerfect (W ⧸ Subgroup.center W) := Group.IsPerfect.ofSurjective hψ
          exact this.commutator_eq_top
        have hnine : ¬ 9 ∣ Nat.card (J.map (QuotientGroup.mk' (Subgroup.center W))) := fun h9 => by
          have htop := hNF _ _ hTb (Subgroup.le_normalizer.trans hNb) h9
          have hc' := hperfb ⊤ htop.ge hXp
          rw [← htop] at hc'
          exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc' ((dvd_mul_right 3 3).trans h9)
        have h6048 : Nat.card (W ⧸ Subgroup.center W) = 6048 :=
          CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hc
        have hmul := Subgroup.card_mul_index (J.map (QuotientGroup.mk' (Subgroup.center W)))
        rw [Subgroup.index_map_eq J hψ (hker.trans ((Subgroup.center_le_normalizer _).trans hNJ)),
          h6048] at hmul
        have h27' : 27 ∣ Nat.card (J.map (QuotientGroup.mk' (Subgroup.center W))) * J.index :=
          hmul ▸ (by norm_num : 27 ∣ 6048)
        have hcop : Nat.Coprime 27 J.index := by
          have : Nat.Coprime (3 ^ 3) J.index := Nat.Coprime.pow_left 3
            ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hidx)
          simpa using this
        exact hnine ((by norm_num : 9 ∣ 27).trans (hcop.dvd_of_dvd_mul_right h27'))

theorem kFactCompParabSylowThreeAut_of_inputs
    (hGA : CFSG.Open.GriessAllModelsStatement) (hExc : SuOddThreeDvdStatement hGA)
    (hWit : OrderNineWitnessStatement) : KFactCompParabSylowThreeAut := by
  intro Y _ _ L P hcp hsolv hidx
  obtain ⟨T, hT, hNJ, hJ⟩ := exists_sylow_normalizer_subgroupOf_of_compParabE (CompParab.toE hcp)
  have hJsolv : Group.IsSolvable ↥(P.subgroupOf L) :=
    solvable_of_solvable_injective (f := (Subgroup.subgroupOfEquivOfLe hcp.parab.1).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hcp.parab.1).injective
  exact not_27_dvd_card_mulAut_of_parab hGA hExc hWit hcp.comp.2.2 hcp.type hT hNJ hJ
    (fun U hUJ hU => coprime_three_card_of_perfect_of_solvable hJsolv hUJ hU) hidx

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

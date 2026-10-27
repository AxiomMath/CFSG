module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInnerAut
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.LocalAnalysis.GLTheoremB

section Recog

theorem exists_elemAbelian_nine_barOf {H : Type*} [Group H] [Finite H] {E : Subgroup H}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 9) :
    ∃ E' : Subgroup (H ⧸ CFSG.Open.GLAPPrimeCore 3 H),
      CFSG.Open.IsElemAbelian 3 E' ∧ Nat.card E' = 9 := by
  set O := CFSG.Open.GLAPPrimeCore 3 H with hO
  set ρ : ↥E →* H ⧸ O := (QuotientGroup.mk' O).comp E.subtype with hρ
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : (x : H) ∈ O := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx)
    have h2 : orderOf (x : H) ∣ 3 := orderOf_dvd_of_pow_eq_one (hE.2 x x.2)
    have h3 : orderOf (x : H) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O h1
    have h4 : orderOf (x : H) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h3
        (coprime_card_gLAPPrimeCore_aux 3 H).symm) h2
    exact Subgroup.mem_bot.2 (Subtype.ext (orderOf_eq_one_iff.1 h4))
  have hrange : ρ.range = E.map (QuotientGroup.mk' O) := by
    rw [hρ, MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨E.map (QuotientGroup.mk' O), isElemAbelian_map _ hE, ?_⟩
  rw [← hrange, ← hc]
  exact (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm

end Recog

theorem inputFieldRecog_holds : UniquenessMaximal.InputFieldRecog := by
  intro G _ _ Ky K₀ g hT hg hg3 hK₀ hE
  refine ⟨hg, ?_⟩
  obtain ⟨J₁, hJ₁, rfl⟩ := exists_comp_subgroupOf
    (inf_le_left : Ky ⊓ Subgroup.centralizer ({g} : Set G) ≤ Ky) hK₀
  have hJ := comp_map_fixSub hg hg3 hJ₁
  have hQ := isQuasisimple_quotient_of_glaPComponent hJ
  have hα3 := barAut_pow_three hg hg3
  have hJα : ∀ j ∈ J₁.map (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 3 ↥Ky)),
      (barAut 3 Ky ⟨g, hg⟩) j = j := fun j hj => hJ.1 hj
  obtain ⟨E, hEJ, hEa, hEc⟩ := hE
  have hE9 : ∃ E' : Subgroup (barOf 3 (J₁.map (QuotientGroup.mk'
      (CFSG.Open.GLAPPrimeCore 3 ↥Ky)))), CFSG.Open.IsElemAbelian 3 E' ∧ Nat.card E' = 9 := by
    have hEa' : CFSG.Open.IsElemAbelian 3 (E.subgroupOf (J₁.map Ky.subtype)) :=
      isElemAbelian_comap (J₁.map Ky.subtype).subtype_injective hEa
    have hEc' : Nat.card (E.subgroupOf (J₁.map Ky.subtype)) = 9 := by
      rw [← hEc]
      exact card_comap_of_le_range (J₁.map Ky.subtype).subtype_injective (by
        rw [Subgroup.range_subtype]; exact hEJ)
    exact exists_elemAbelian_nine_of_mulEquiv (liftEquiv J₁).symm
      (exists_elemAbelian_nine_barOf hEa' hEc')
  rcases hT with ⟨K, hKf, hFin, hc, ⟨e⟩⟩ | ⟨K, hKf, hFin, q, hcard, hq3, ⟨e⟩⟩
  · obtain ⟨p, f, hK, hmod, h2⟩ := exists_true_data K hc
    exact inner_proj hK hmod h2
      (e.trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm) hα3 hJα hQ hE9
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    have hK : PiField false p f K :=
      ⟨hF.prime, hF.one_le, by rw [piCard, Bool.cond_false]; exact hcard⟩
    have hmod : ModThree false (p ^ f) := hq3
    have e' := e.trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm
    by_cases h2 : 2 < p ^ f
    · exact inner_proj hK hmod h2 e' hα3 hJα hQ hE9
    · exfalso
      have hs := (isSolvable_slPi_false_two hK (pow_eq_two_of_not_two_lt hF h2)).2
      have hY : Group.IsSolvable (barOf 3 Ky) :=
        Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
      have hJs : Group.IsSolvable ↥(J₁.map (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 3 ↥Ky))) :=
        Group.isSolvable_of_isSolvable_injective (f := (J₁.map (QuotientGroup.mk'
          (CFSG.Open.GLAPPrimeCore 3 ↥Ky))).subtype) Subtype.val_injective
      exact false_of_isSolvable_quotient hQ hJs

end CFSG.HardMathSupport.Solomon.Coordinator

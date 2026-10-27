module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArmsHolds
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.CatFS412
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.Arith
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCatClass
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GrSLit.L34Sec5S


theorem g2FixedCatalog_of_outer (hOut : G2EvenOuterFixedCatalog) : G2FixedCatalog := by
  intro n hn S _ _ hs hna hcat σ hσ P hPF hD hPne hL
  have : IsSimpleGroup S := hs
  have hP2 : IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have h : CatLeaf.ProperFixedComponent σ P := ⟨hσ, hPF, hP2, hPne⟩
  have hσ2 : orderOf σ = 2 :=
    orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => hσ y) h.ne_one
  have hR : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → LieModel X .G2 0 2 n →
      LieModel Y .G2 0 2 n := fun _ _ _ _ e hX => LieType.CurtisTits.lieModel_of_mulEquiv e hX
  have hsmall : ∀ M : ℕ, ¬ 2 ^ 12 ∣ M →
      ∀ (X : Type) [Group X] [Finite X], LieModel X .G2 0 2 n → ¬ Nat.card X ∣ M := by
    intro M h12 X _ _ hX hd
    rw [card_of_lieModel_g_two_two_pow hX] at hd
    exact h12 (((Nat.pow_dvd_pow 2 (by omega : 12 ≤ 6 * n)).trans
      (two_pow_six_mul_dvd_ordG2 (by omega))).trans hd)
  have hRalt : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
      ¬ LieModel (alternatingGroup Ω) .G2 0 2 n := by
    intro Ω _ _ hΩ hA
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have h1 := card_of_lieModel_g_two_two_pow hA
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card] at h1
    exact ordG2_two_pow_ne_factorial_div_two hn hΩ h1.symm
  have hRodd : ∀ (X : Type) [Group X] (t : StatedLieTag) (n' p f : ℕ), p.Prime → p ≠ 2 →
      StatedLieAdmissible t n' p f → LieModel X t n' p f → ¬ LieModel X .G2 0 2 n :=
    fun X _ t n' p f hp hp2 hadm hm hX =>
      SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two_of_ne_Tits hX (by decide)
        (fun h1 => absurd h1.1 (by decide)) (fun h1 => absurd h1.1 (by decide))
        (fun h1 => absurd h1.1 (by decide)) ⟨t, n', p, f, hp, hp2, hadm, hm⟩
  have h360 := hsmall 360 (by decide)
  have h504 := hsmall 504 (by decide)
  have h20160 := hsmall 20160 (by decide)
  have hHe := hsmall 4030387200 (by decide)
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨k, hk, ⟨θ⟩⟩ | ho | he | hsp
  · exact (not_of_properFixedComponent_alternating (R := fun X _ => LieModel X .G2 0 2 n) hR
      hRalt h360 hk θ h hL).elim
  · exact (not_of_properFixedComponent_oddLie (R := fun X _ => LieModel X .G2 0 2 n)
      SeitzReduction.gls3OddLieAutComponentsInput CatLeafProof.lieOrderFormulasInput
      hR hRodd h504 hna ho h hL).elim
  · rcases CatLeaf.exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
    · exact (not_of_properFixedComponent_evenLie_inner (R := fun X _ => LieModel X .G2 0 2 n)
        SeitzReduction.gls3OddLieAutComponentsInput CatLeafProof.lieOrderFormulasInput hR hRalt
        h360 hRodd h504 h20160 hHe hna he h ht hL).elim
    · obtain ⟨-, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hD.1
      exact Or.inl (hOut n hn S hs he σ hσ2 hout (P.subgroupOf (fixedSubgroup σ)) hD
        (LieType.CurtisTits.lieModel_of_mulEquiv eZ hL))
  · obtain ⟨s, ⟨e⟩⟩ := hsp
    obtain ⟨-, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hD.1
    have hLD := LieType.CurtisTits.lieModel_of_mulEquiv eZ hL
    have hc := card_of_lieModel_g_two_two_pow hLD
    obtain ⟨hdvd, hin, hout⟩ := CatFC.armInputs_holds.table hs hna e hσ2 hD
    rw [hc] at hdvd hin hout
    by_cases hinn : σ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨rfl, rfl⟩ := g2_inner_row hn hdvd (hin hinn)
      exact Or.inr ⟨rfl, ⟨e⟩⟩
    · exact (g2_outer_row hn hdvd (hout hinn)).elim

end CFSG.EvenSporadicStandard.Induction

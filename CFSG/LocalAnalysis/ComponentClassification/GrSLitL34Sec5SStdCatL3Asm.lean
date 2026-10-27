module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatL3Out
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatL3Spor
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem l3TwoPowProperFixedCatalog_of_inputs
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hO : CatLeaf.LieOrderFormulasInput)
    (hMinn : CatLeaf.MonsterInnerInput) (hMcomp : CatLeaf.MonsterLocalComponentsInput) :
    L3TwoPowProperFixedCatalog := by
  intro n hn hev S _ _ hs hna hcat σ hσ P hPF hP hPne hL
  have : IsSimpleGroup S := hs
  have h : CatLeaf.ProperFixedComponent σ P := ⟨hσ, hPF, hP, hPne⟩
  have hR : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → LieModel X .PSL 3 2 n →
      LieModel Y .PSL 3 2 n := fun _ _ _ _ e hX => LieType.CurtisTits.lieModel_of_mulEquiv e hX
  have hsmall : ∀ M : ℕ, 0 < M → ¬ 2 ^ 12 ∣ M → ∀ (X : Type) [Group X] [Finite X],
      LieModel X .PSL 3 2 n → ¬ Nat.card X ∣ M := fun M _ h12 X _ _ hX hd =>
    h12 (((Nat.pow_dvd_pow 2 (by omega : 12 ≤ 3 * n)).trans
      (pow_dvd_card_of_lieModel_psl_three (by omega) hX)).trans hd)
  have hRalt : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
      ¬ LieModel (alternatingGroup Ω) .PSL 3 2 n := by
    intro Ω _ _ hΩ hA
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have h1 := SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hA
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card] at h1
    rcases SeitzReduction.LinearPilot.ordA_two_pow_eq_factorial_div_two (n := 3 - 1)
      (by norm_num) (by omega) h1.symm with h2 | h2 <;> omega
  have hRodd : ∀ (X : Type) [Group X] (t : StatedLieTag) (n' p f : ℕ), p.Prime → p ≠ 2 →
      StatedLieAdmissible t n' p f → LieModel X t n' p f → ¬ LieModel X .PSL 3 2 n :=
    fun X _ t n' p f hp hp2 hadm hm hX => SeitzReduction.CrossChar.sLmNotOddLieInputAt
      (m := 3) (by norm_num) X n (fun h3 => by rw [Prod.mk.injEq] at h3; omega) hX
      ⟨t, n', p, f, hp, hp2, hadm, hm⟩
  have h360 := hsmall 360 (by norm_num) (by decide)
  have h504 := hsmall 504 (by norm_num) (by decide)
  have h20160 := hsmall 20160 (by norm_num) (by decide)
  have hHe := hsmall 4030387200 (by norm_num) (by decide)
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨k, hk, ⟨θ⟩⟩ | ho | he | hsp
  · exact (not_of_properFixedComponent_alternating (R := fun X _ => LieModel X .PSL 3 2 n) hR
      hRalt h360 hk θ h hL).elim
  · exact (not_of_properFixedComponent_oddLie (R := fun X _ => LieModel X .PSL 3 2 n) hGLS hO
      hR hRodd h504 hna ho h hL).elim
  · rcases CatLeaf.exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
    · exact (not_of_properFixedComponent_evenLie_inner (R := fun X _ => LieModel X .PSL 3 2 n)
        hGLS hO hR hRalt h360 hRodd h504 h20160 hHe hna he h ht hL).elim
    · exact lieModel_two_mul_of_evenLie_outer he h hout hn hev hL
  · exact (false_of_properFixedComponent_sporadic_psl_three hMinn hMcomp hna hsp h (by omega)
      hL).elim

end CFSG.ComponentClassification.GrSLit.L34Sec5S

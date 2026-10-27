module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatSuz
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatONan
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_card_of_properFixedComponent_nonsporadic
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hO : CatLeaf.LieOrderFormulasInput)
    (hEO : CatLeaf.EvenLieOuterTwoComponentsInput) {N : ℕ}
    (h14 : (14 : ℕ).factorial / 2 < N) (h15 : N < (15 : ℕ).factorial / 2)
    (hLie : ∀ (X : Type) [Group X] {t : StatedLieTag} {n p f : ℕ}, StatedLieAdmissible t n p f →
      LieModel X t n p f → Nat.card X ≠ N)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hS : (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨ OddLieType S ∨
      EvenLieType S)
    {σ : MulAut S} {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P) :
    Nat.card (P ⧸ Open.fusionZStar P) ≠ N := by
  have hHe : 4030387200 < N := lt_of_le_of_lt (by norm_num [Nat.factorial]) h14
  have hR : ∀ (X Y : Type) [Group X] [Group Y], (X ≃* Y) → Nat.card X = N → Nat.card Y = N :=
    fun _ _ _ _ e hX => (Nat.card_congr e.toEquiv).symm.trans hX
  have hsmall : ∀ M : ℕ, 0 < M → M < N → ∀ (X : Type) [Group X] [Finite X], Nat.card X = N →
      ¬ Nat.card X ∣ M := fun M hM hMN X _ _ hX hd => by
    have := Nat.le_of_dvd hM hd
    omega
  have hRalt : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
      ¬ Nat.card (alternatingGroup Ω) = N := by
    intro Ω _ _ hΩ hA
    have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card] at hA
    exact factorial_div_two_ne_of_bounds h14 h15 _ hA
  have hRodd : ∀ (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ), p.Prime → p ≠ 2 →
      StatedLieAdmissible t n p f → LieModel X t n p f → ¬ Nat.card X = N :=
    fun X _ _ _ _ _ _ _ hadm hm => hLie X hadm hm
  have h360 := hsmall 360 (by norm_num) (by omega)
  have h504 := hsmall 504 (by norm_num) (by omega)
  have h20160 := hsmall 20160 (by norm_num) (by omega)
  have hHe' := hsmall 4030387200 (by norm_num) hHe
  rcases hS with ⟨n, hn, ⟨θ⟩⟩ | ho | he
  · exact not_of_properFixedComponent_alternating (R := fun X _ => Nat.card X = N) hR hRalt h360
      hn θ h
  · exact not_of_properFixedComponent_oddLie (R := fun X _ => Nat.card X = N) hGLS hO hR hRodd
      h504 hna ho h
  rcases CatLeaf.exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  · exact not_of_properFixedComponent_evenLie_inner (R := fun X _ => Nat.card X = N) hGLS hO hR
      hRalt h360 hRodd h504 h20160 hHe' hna he h ht
  intro hP
  obtain ⟨τ, n, f, hadm, hm⟩ := he
  obtain ⟨eL⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1)
  have hcard : Nat.card ((P.subgroupOf (fixedSubgroup σ)) ⧸
      Open.fusionZStar (P.subgroupOf (fixedSubgroup σ))) = N := by
    rw [Nat.card_congr eL.toEquiv, hP]
  rcases hEO S τ n f hadm hm σ (orderOf_eq_two_of_properFixedComponent h) hout _ h.2.2.1 with
    ⟨τ', n', f', hadm', hm'⟩ | hA | hU
  · exact hLie _ hadm' hm' hcard
  · obtain ⟨eA⟩ := hA
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hcard
    norm_num [Nat.factorial] at hcard
    omega
  · have hadm3 : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
    exact hLie _ hadm3 hU hcard

theorem suzONanNotProperFixedCatalog_of_inputs
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hO : CatLeaf.LieOrderFormulasInput)
    (hEO : CatLeaf.EvenLieOuterTwoComponentsInput) (hMinn : CatLeaf.MonsterInnerInput)
    (hMcomp : CatLeaf.MonsterLocalComponentsInput) : SuzONanNotProperFixedCatalog := by
  intro S _ _ hs hna hcat σ hσ P hPF hP hPne
  have : IsSimpleGroup S := hs
  have h : CatLeaf.ProperFixedComponent σ P := ⟨hσ, hPF, hP, hPne⟩
  have key : ∀ {N : ℕ}, (14 : ℕ).factorial / 2 < N → N < (15 : ℕ).factorial / 2 →
      (∀ (X : Type) [Group X] {t : StatedLieTag} {n p f : ℕ}, StatedLieAdmissible t n p f →
        LieModel X t n p f → Nat.card X ≠ N) →
      (NativeSporadic.SporadicRep S → Nat.card (P ⧸ Open.fusionZStar P) ≠ N) →
      Nat.card (P ⧸ Open.fusionZStar P) ≠ N := by
    intro N h14 h15 hLie hspor
    rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
      hA | ho | he | hsp
    · exact not_card_of_properFixedComponent_nonsporadic hGLS hO hEO h14 h15 hLie hna (.inl hA) h
    · exact not_card_of_properFixedComponent_nonsporadic hGLS hO hEO h14 h15 hLie hna
        (.inr (.inl ho)) h
    · exact not_card_of_properFixedComponent_nonsporadic hGLS hO hEO h14 h15 hLie hna
        (.inr (.inr he)) h
    · exact hspor hsp
  refine ⟨fun hS => ?_, fun hS => ?_⟩
  · obtain ⟨f⟩ := hS
    exact key (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (fun X _ _ _ _ _ hadm hm => lieModel_card_ne_suz hO hadm hm)
      (fun hsp => not_card_suz_of_properFixedComponent_sporadic hMinn hMcomp hna hsp h)
      ((Nat.card_congr f.toEquiv).trans Sporadic.Suz.card_Suz)
  · obtain ⟨f⟩ := hS
    exact key (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (fun X _ _ _ _ _ hadm hm => lieModel_card_ne_onan hO hadm hm)
      (fun hsp => not_card_onan_of_properFixedComponent_sporadic hMinn hMcomp hna hsp h)
      ((Nat.card_congr f.toEquiv).trans Sporadic.ON.card_ON)

end CFSG.ComponentClassification.GrSLit.L34Sec5S

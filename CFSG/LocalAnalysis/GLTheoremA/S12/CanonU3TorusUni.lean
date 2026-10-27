module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Uni
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusCore
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3UniTorusDiag
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3UniTorusEnd
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAKit
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open CFSG.Assembly
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived
  exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived mem_innAutDerived_congr)

open CFSG.LocalAnalysis.GLTheoremA.I141F.Tri (mem_innAutDerived_of_innDiagKind_of_not_derived)

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (primeFormP primeFormConjHom primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram isPrimeFormGram_idGram)

open CFSG.StandardType (MarkedModel markTag markRank markChar markDeg)

open CFSG.SignalizerFunctorTheorem.TransportA (isComponentOf_map)

open Polynomial
open scoped Classical

section Aux

theorem eq_of_isComponentOf_map_of_unique {S P : Type} [Group S] [Group P]
    {θ : S ≃* P} {β : MulAut S} {J : Subgroup S}
    (huniq : ∀ J' : Subgroup S, CFSG.Open.IsComponentOf J' (fixSubgroup β) → J' = J) :
    ∀ T' : Subgroup P, CFSG.Open.IsComponentOf T'
      (fixSubgroup (θ.symm.trans (β.trans θ))) → T' = J.map θ.toMonoidHom := by
  intro T' hT'
  have hfix : (fixSubgroup (θ.symm.trans (β.trans θ))).map θ.symm.toMonoidHom =
      fixSubgroup β := by
    rw [CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup θ.symm (θ.symm.trans (β.trans θ))]
    congr 1
    ext x
    simp [MulEquiv.trans_apply]
  have hJ : T'.map θ.symm.toMonoidHom = J := by
    apply huniq
    have h1 := isComponentOf_map θ.symm hT'
    convert h1 using 2
    · rfl
    · exact hfix.symm
  calc T' = (T'.map θ.symm.toMonoidHom).map θ.toMonoidHom := by
        rw [Subgroup.map_map]
        have hcomp : θ.toMonoidHom.comp θ.symm.toMonoidHom = MonoidHom.id P := by
          ext x
          simp
        rw [hcomp, Subgroup.map_id]
    _ = J.map θ.toMonoidHom := by rw [hJ]

theorem exists_moved_of_map_fixSubgroup {S P : Type} [Group S] [Group P]
    {θ : S ≃* P} {β₁ β₂ : MulAut S} {J : Subgroup S} {T : Subgroup P}
    (hT : T = J.map θ.toMonoidHom)
    (hmoves : ∀ k : ℕ, ∃ j ∈ J, (β₂ * β₁ ^ k) j ≠ j) :
    ∀ k : ℕ, ∃ t ∈ T,
      ((θ.symm.trans (β₂.trans θ)) * (θ.symm.trans (β₁.trans θ)) ^ k) t ≠ t := by
  intro k
  obtain ⟨j, hjJ, hj⟩ := hmoves k
  refine ⟨θ j, ?_, ?_⟩
  · rw [hT]
    exact Subgroup.mem_map_of_mem _ hjJ
  · intro hfix
    have hev : ((θ.symm.trans (β₂.trans θ)) * (θ.symm.trans (β₁.trans θ)) ^ k) (θ j)
        = θ ((β₂ * β₁ ^ k) j) := by
      rw [← MulAut.congr_apply θ β₂, ← MulAut.congr_apply θ β₁]
      rw [← map_pow, ← map_mul]
      simp [MulAut.congr_apply]
    rw [hev] at hfix
    exact hj (θ.injective hfix)

theorem isSolvable_inf_fixSubgroup_map_iff {S P : Type} [Group S] [Group P]
    {θ : S ≃* P} {β : MulAut S} {A : MulAut P} {J : Subgroup S}
    (hβ : θ.symm.trans (β.trans θ) = A) :
    (IsSolvable ↥(J ⊓ fixSubgroup β) ↔
      IsSolvable ↥(J.map θ.toMonoidHom ⊓ fixSubgroup A)) := by
  have hmap : (J ⊓ fixSubgroup β).map θ.toMonoidHom =
      J.map θ.toMonoidHom ⊓ fixSubgroup A := by
    rw [Subgroup.map_inf J (fixSubgroup β) θ.toMonoidHom θ.injective,
      CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup θ β, hβ]
  let e : ↥(J ⊓ fixSubgroup β) ≃* ↥((J ⊓ fixSubgroup β).map θ.toMonoidHom) :=
    Subgroup.equivMapOfInjective (J ⊓ fixSubgroup β) θ.toMonoidHom θ.injective
  constructor
  · intro hs
    haveI : Group.IsSolvable ↥(J ⊓ fixSubgroup β) := hs
    rw [← hmap]
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · intro hs
    rw [← hmap] at hs
    haveI : Group.IsSolvable ↥((J ⊓ fixSubgroup β).map θ.toMonoidHom) := hs
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem not_isSolvable_and_of_model_uni_aux {S : Type} [Group S] [Finite S]
    {labL : GLALabel} {β β₁ β₂ : MulAut S} {n : ℕ} {J : Subgroup S}
    (hT : U3TorusHyp S labL β β₁ β₂ n J) {d : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData 2 labL.n K) (hd3 : 3 ≤ d) (hd6 : d ≤ 6)
    (hne : ¬(d = 3 ∧ 2 ^ labL.n = 2)) (θ : S ≃* primeFormP hU (idGram K d))
    (hβmem : β ∈ innAutDerived S) (hβ₁mem : β₁ ∈ innAutDerived S)
    (hβ₂mem : β₂ ∈ innAutDerived S)
    (hcardT : Nat.card (↥(J.map θ.toMonoidHom) ⧸
      Subgroup.center ↥(J.map θ.toMonoidHom)) = ordTwistedA 2 (2 ^ n)) :
    ¬ (IsSolvable ↥(J ⊓ fixSubgroup β₁) ∧ IsSolvable ↥(J ⊓ fixSubgroup β₂)) := by
  classical
  let β' : MulAut (primeFormP hU (idGram K d)) := θ.symm.trans (β.trans θ)
  let β₁' : MulAut (primeFormP hU (idGram K d)) := θ.symm.trans (β₁.trans θ)
  let β₂' : MulAut (primeFormP hU (idGram K d)) := θ.symm.trans (β₂.trans θ)
  have hβ'mem : β' ∈ innAutDerived (primeFormP hU (idGram K d)) :=
    (mem_innAutDerived_congr θ).2 hβmem
  have hβ₁'mem : β₁' ∈ innAutDerived (primeFormP hU (idGram K d)) :=
    (mem_innAutDerived_congr θ).2 hβ₁mem
  have hβ₂'mem : β₂' ∈ innAutDerived (primeFormP hU (idGram K d)) :=
    (mem_innAutDerived_congr θ).2 hβ₂mem
  have hβ'3 : β' ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr θ) β 3
    rw [hT.core.pow_three, map_one] at h3
    exact h3.symm
  have hβ₁'3 : β₁' ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr θ) β₁ 3
    rw [hT.pow_three₁, map_one] at h3
    exact h3.symm
  have hβ₂'3 : β₂' ^ 3 = 1 := by
    have h3 := map_pow (MulAut.congr θ) β₂ 3
    rw [hT.pow_three₂, map_one] at h3
    exact h3.symm
  obtain ⟨A, c, -, hA, hβeq⟩ :=
    exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived hU
      (isPrimeFormGram_idGram (n := d)) hd3 hne hβ'mem hβ'3
  obtain ⟨A₁, c₁, -, hA₁, hβ₁eq⟩ :=
    exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived hU
      (isPrimeFormGram_idGram (n := d)) hd3 hne hβ₁'mem hβ₁'3
  obtain ⟨A₂, c₂, -, hA₂, hβ₂eq⟩ :=
    exists_primeFormConjHom_pow_scalar_of_mem_innAutDerived hU
      (isPrimeFormGram_idGram (n := d)) hd3 hne hβ₂'mem hβ₂'3
  have hβeq' : θ.symm.trans (β.trans θ) = primeFormConjHom hU (idGram K d) A := hβeq
  have hβ₁eq' : θ.symm.trans (β₁.trans θ) = primeFormConjHom hU (idGram K d) A₁ := hβ₁eq
  have hβ₂eq' : θ.symm.trans (β₂.trans θ) = primeFormConjHom hU (idGram K d) A₂ := hβ₂eq
  have hβne : primeFormConjHom hU (idGram K d) A ≠ 1 := by
    rw [← hβeq]
    intro h1
    apply hT.core.ne_one
    have h2 : (MulAut.congr θ) β = 1 := h1
    exact (MulEquiv.map_eq_one_iff (MulAut.congr θ)).1 h2
  have hfix : (fixSubgroup β).map θ.toMonoidHom =
      fixSubgroup (primeFormConjHom hU (idGram K d) A) := by
    rw [CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup θ β, ← hβeq]
  have hTcomp : CFSG.Open.IsComponentOf (J.map θ.toMonoidHom)
      (fixSubgroup (primeFormConjHom hU (idGram K d) A)) := by
    have h1 := isComponentOf_map θ hT.core.isComponentOf
    exact hfix ▸ h1
  obtain ⟨hfn, μ, hμ, ha, hm, htop, hTblock⟩ :=
    exists_block_of_component_primeForm hU hd6 hT.core.odd A hA hβne hTcomp hcardT
  have h3n : 3 ≤ n := hT.core.three_le
  have hf2 : 2 ≤ labL.n := by
    rw [hfn]
    omega
  have h3dvd : 3 ∣ 2 ^ labL.n + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
      CFSG.two_pow_mod_three_of_odd hT.core.odd_labL_n]
  have hunique : ∀ T' : Subgroup (primeFormP hU (idGram K d)),
      CFSG.Open.IsComponentOf T' (fixSubgroup (primeFormConjHom hU (idGram K d) A)) →
      T' = blockImage hU (Matrix.GeneralLinearGroup.toLin (A : GL (Fin d) K)) (X - C μ) := by
    intro T' hT'
    refine (eq_of_isComponentOf_map_of_unique hT.unique T' ?_).trans hTblock
    rw [← hβeq] at hT'
    exact hT'
  have hc₁ : Commute (primeFormConjHom hU (idGram K d) A)
      (primeFormConjHom hU (idGram K d) A₁) := by
    rw [← hβeq, ← hβ₁eq]
    exact hT.commute₁.map (MulAut.congr θ).toMonoidHom
  have hc₂ : Commute (primeFormConjHom hU (idGram K d) A)
      (primeFormConjHom hU (idGram K d) A₂) := by
    rw [← hβeq, ← hβ₂eq]
    exact hT.commute₂.map (MulAut.congr θ).toMonoidHom
  have hc₁₂ : Commute (primeFormConjHom hU (idGram K d) A₁)
      (primeFormConjHom hU (idGram K d) A₂) := by
    rw [← hβ₁eq, ← hβ₂eq]
    exact hT.commute₁₂.map (MulAut.congr θ).toMonoidHom
  obtain ⟨P, d', e₁, e₂, hPd, hP₁, hP₂, hI⟩ :=
    exists_diagonal_of_unique hU hf2 h3dvd A A₁ A₂ hA hA₁ hA₂ hc₁ hc₂ hc₁₂ hμ ha hm htop
      hunique
  have hmoves : ∀ k : ℕ, ∃ t ∈ blockImage hU
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin d) K)) (X - C μ),
      (primeFormConjHom hU (idGram K d) A₂ *
        primeFormConjHom hU (idGram K d) A₁ ^ k) t ≠ t := by
    have h := exists_moved_of_map_fixSubgroup (T := J.map θ.toMonoidHom) rfl hT.moves₂
    rw [hβ₂eq', hβ₁eq'] at h
    rw [hTblock] at h
    exact h
  have hnot := not_isSolvable_and_of_diagonal hU hf2 A A₁ A₂ P hA₁ hA₂ hPd hP₁ hP₂ hμ ha hI
    hmoves
  intro hsol
  have hsol₁ : IsSolvable ↥(J.map θ.toMonoidHom ⊓
      fixSubgroup (primeFormConjHom hU (idGram K d) A₁)) :=
    (isSolvable_inf_fixSubgroup_map_iff (β := β₁)
      (A := primeFormConjHom hU (idGram K d) A₁) (J := J) hβ₁eq').1 hsol.1
  have hsol₂ : IsSolvable ↥(J.map θ.toMonoidHom ⊓
      fixSubgroup (primeFormConjHom hU (idGram K d) A₂)) :=
    (isSolvable_inf_fixSubgroup_map_iff (β := β₂)
      (A := primeFormConjHom hU (idGram K d) A₂) (J := J) hβ₂eq').1 hsol.2
  have hsolT₁ : IsSolvable ↥(blockImage hU
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin d) K)) (X - C μ) ⊓
      fixSubgroup (primeFormConjHom hU (idGram K d) A₁)) := by
    rw [← hTblock]
    exact hsol₁
  have hsolT₂ : IsSolvable ↥(blockImage hU
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin d) K)) (X - C μ) ⊓
      fixSubgroup (primeFormConjHom hU (idGram K d) A₂)) := by
    rw [← hTblock]
    exact hsol₂
  exact hnot ⟨hsolT₁, hsolT₂⟩

end Aux

section MainCerts


theorem not_isSolvable_and_of_model_uni {S : Type} [Group S] [Finite S]
    {labL : GLALabel} {β β₁ β₂ : MulAut S} {n : ℕ} {J : Subgroup S}
    (hT : U3TorusHyp S labL β β₁ β₂ n J) (hF : FamUni labL) {d : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData 2 labL.n K) (hd3 : 3 ≤ d) (hd6 : d ≤ 6)
    (hne : ¬(d = 3 ∧ 2 ^ labL.n = 2))
    (θ : S ≃* primeFormP hU (idGram K d)) :
    ¬ (IsSolvable ↥(J ⊓ fixSubgroup β₁) ∧ IsSolvable ↥(J ⊓ fixSubgroup β₂)) := by
  classical
  have hnd : labL.tag ≠ .B2der ∧ labL.tag ≠ .G2der ∧ labL.tag ≠ .twF4der := by
    rcases hF with htag | ⟨htag, -⟩ <;> rw [htag] <;> decide
  have hβmem : β ∈ innAutDerived S :=
    mem_innAutDerived_of_innDiagKind_of_not_derived hT.core.center_eq_bot hnd hT.core.innDiagKind
  have hβ₁mem : β₁ ∈ innAutDerived S :=
    mem_innAutDerived_of_innDiagKind_of_not_derived hT.core.center_eq_bot hnd hT.innDiagKind₁
  have hβ₂mem : β₂ ∈ innAutDerived S :=
    mem_innAutDerived_of_innDiagKind_of_not_derived hT.core.center_eq_bot hnd hT.innDiagKind₂
  have eJK : ↥J ≃* ↥(J.map θ.toMonoidHom) :=
    J.equivMapOfInjective θ.toMonoidHom θ.injective
  have hcardT : Nat.card (↥(J.map θ.toMonoidHom) ⧸
      Subgroup.center ↥(J.map θ.toMonoidHom)) = ordTwistedA 2 (2 ^ n) := by
    rw [← hT.core.card_centerQuot_uni]
    exact (Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥J)
      (Subgroup.center ↥(J.map θ.toMonoidHom)) eJK
      (Subgroup.map_center_eq eJK)).toEquiv).symm
  exact not_isSolvable_and_of_model_uni_aux hT hU hd3 hd6 hne θ hβmem hβ₁mem hβ₂mem hcardT

theorem u3TorusCoreOn_uni : U3TorusCoreOn FamUni := by
  intro S _ _ labL β β₁ β₂ n J hF hT
  classical
  have h3dvd : 3 ∣ 2 ^ labL.n + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod,
      CFSG.two_pow_mod_three_of_odd hT.core.odd_labL_n]
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel
    hT.core.hasLabel_of_innDiag
  rcases hF with htag | ⟨htag, hrank⟩
  · have hd6 : labL.rank + 1 ≤ 6 := by
      have hlab2 := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.lambda2_of_hasLabel
        hT.core.hasLabel_of_innDiag
      have hl := CFSG.StandardType.largeEvenLabelAll_torusLift_twA (p := 3)
        hlab2 htag (by norm_num) h3dvd
      have hTlift := ggTorusLift_of_labelAll hT.core.center_eq_bot hT.core.innDiagKind hl
      have hr := hT.core.rank_le _ hTlift
      simp only [CFSG.StandardType.ggUnitaryTorusRank] at hr
      split_ifs at hr <;> omega
    have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .PSU
        (labL.rank + 1) 2 labL.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, htag] using hM
    have hSCM : StatedClassicalModel (S ⧸ Subgroup.center S) .PSU
        (labL.rank + 1) 2 labL.n := hLM.statedClassicalModel (by decide)
    have hSCM' : StatedClassicalModel S .PSU (labL.rank + 1) 2 labL.n :=
      CFSG.StandardType.statedClassicalModel_of_mulEquiv'
        (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hT.core.center_eq_bot) hSCM
    obtain ⟨K, hKf, hU, -, ⟨eP⟩⟩ := exists_primeFormP_mulEquiv_of_statedModel_uni hSCM'
    exact not_isSolvable_and_of_model_uni hT (Or.inl htag) hU
      hSCM'.1.2.2.1 hd6
      (by rintro ⟨h1, h2⟩; exact hSCM'.1.2.2.2 (by rw [h1, h2])) eP
  · have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .PSU 4 2 labL.n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg, htag, hrank] using hM
    have hSCM : StatedClassicalModel (S ⧸ Subgroup.center S) .PSU 4 2 labL.n :=
      hLM.statedClassicalModel (by decide)
    have hSCM' : StatedClassicalModel S .PSU 4 2 labL.n :=
      CFSG.StandardType.statedClassicalModel_of_mulEquiv'
        (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hT.core.center_eq_bot) hSCM
    obtain ⟨K, hKf, hU, -, ⟨eP⟩⟩ := exists_primeFormP_mulEquiv_of_statedModel_uni hSCM'
    exact not_isSolvable_and_of_model_uni hT (Or.inr ⟨htag, hrank⟩) hU (by norm_num)
      (by norm_num) (by rintro ⟨h1, -⟩; omega) eP

end MainCerts

end CFSG.LocalAnalysis.GLTheoremA.CanonU3

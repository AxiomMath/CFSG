module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUBase
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Orth2

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial

section Models

theorem psu_lieModel_psl_of_equiv_sl {Y : Type} [Group Y] {F : Type} [Field F] [Finite F] {m e : ℕ}
    (hadm : StatedLieAdmissible .PSL (m + 1) 3 e) (hF : Nat.card F = 3 ^ e)
    (E : Y ≃* Matrix.SpecialLinearGroup (Fin (m + 1)) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :
    LieModel Y .PSL (m + 1) 3 e :=
  LieModel.of_mulEquiv E.symm (Or.inl ⟨by decide,
    LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient m F hadm hF⟩)

end Models

section Orthogonal

variable {k W : Type} [Field k] [Finite k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  {e : ℕ}

theorem psu_three_pow_facts (he : 1 ≤ e) : 3 ≤ 3 ^ e ∧ (2 ≤ e → 9 ≤ 3 ^ e) := by
  refine ⟨OddInner.three_le_pow Nat.prime_three (by norm_num) he, fun h2 => ?_⟩
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) h2

theorem psu_orth_three_has27 (hO : LieOrderFormulasInput) (he : 3 ≤ e) (hk : Nat.card k = 3 ^ e)
    (Q : QuadraticForm k W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank k W = 3) :
    PSUHas27Sub (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left
      (by norm_num)).pow
  have h27 : 27 ≤ 3 ^ e := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hK2 : Nat.card k ≠ 2 := by rw [hk]; omega
  have hK3 : Nat.card k ≠ 3 := by rw [hk]; omega
  obtain ⟨d, ψ, e', -, -, hcomm, hq, -⟩ := orthogonal_three_derived
    hodd hK3 Q hQ hdim
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 k le_rfl (Or.inr hK2) (Or.inr hK3))
    (CatalogueBOrthogonal.traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) k →* _))
    (traceZeroSpecialImage_quasisimple hK2 hK3) hcomm
  have hadm : StatedLieAdmissible .PSL 2 3 e :=
    OddInner.admissible_PSL Nat.prime_three (by omega) le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  exact PSUHas27Sub.of_lieModel hO _ hq.1 hadm (psu_lieModel_psl_of_equiv_sl (m := 1) hadm hk E)
    (by simp [lieSylowExponent]; omega)

open CatalogueBOrthogonalFive in
theorem psu_orth_five_has27 (hO : LieOrderFormulasInput) (he : 1 ≤ e) (hk : Nat.card k = 3 ^ e)
    (Q : QuadraticForm k W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank k W = 5) :
    PSUHas27Sub (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left
      (by norm_num)).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨d, ψ, e', -, -, hcomm, hq, -⟩ := orthogonal_five_derived hodd Q hQ hdim
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' (symplecticKernel_quasisimple hodd)
    (selfAdjointSymplecticAction h2) (selfAdjointSymplecticImage_quasisimple hodd) hcomm
  have hadm : StatedLieAdmissible .PSp 2 3 e := by
    refine ⟨Nat.prime_three, he, le_rfl, fun h => ?_⟩
    have h1 : 3 ^ e = 2 := (Prod.mk.inj h).2
    have := (psu_three_pow_facts he).1
    omega
  let eSp := symplecticKernelEquivFin.trans (LieType.Universal.Symplectic.equivStatedSp 2 k)
  let eTot := E.trans (QuotientGroup.congr _ _ eSp (Subgroup.map_center_eq eSp))
  have hmod : LieModel (commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ⧸
      Subgroup.center (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))) .PSp 2 3 e :=
    LieModel.of_mulEquiv eTot.symm (Or.inl ⟨by decide,
      LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 k hadm hk⟩)
  exact PSUHas27Sub.of_lieModel hO _ hq.1 hadm hmod (by simp [lieSylowExponent]; omega)

theorem psu_orth_big_has27 (hO : LieOrderFormulasInput) (he : 1 ≤ e) (hk : Nat.card k = 3 ^ e)
    (Q : QuadraticForm k W) (hQ : Q.polarBilin.Nondegenerate) (hdim : 7 ≤ Module.finrank k W) :
    PSUHas27Sub (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  obtain ⟨n, hn⟩ : ∃ n, (Module.finrank k W = 2 * n + 1 ∧ 3 ≤ n) ∨
      (Module.finrank k W = 2 * n ∧ 4 ≤ n) := by
    rcases Nat.even_or_odd (Module.finrank k W) with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨r, Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨r, Or.inl ⟨by omega, by omega⟩⟩
  obtain ⟨hq, τ', n', hne, hadm, hlie⟩ := orthogonal_derived_lieModel_ne Nat.prime_three
    (by norm_num) he hk Q hQ hn
  have hSE : 3 ≤ lieSylowExponent τ' n' := by
    rcases lieSylowExponent_ge_three hadm (by norm_num) with ⟨h1, -⟩ | h3
    · exact absurd h1 hne
    · exact h3
  exact PSUHas27Sub.of_lieModel hO _ hq.1 hadm hlie
    (le_trans hSE (Nat.le_mul_of_pos_right _ (by omega)))

open CatalogueBOrthogonalFourNonsplit in
theorem psu_orth_nonsplit_four_has27 (hO : LieOrderFormulasInput) (he : 2 ≤ e)
    (hk : Nat.card k = 3 ^ e) (Q : QuadraticForm k W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 4)
    (hno : ¬ ∃ S : Submodule k W, Module.finrank k S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    PSUHas27Sub (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left
      (by norm_num)).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hns, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_four_derived hodd Q hQ hdim hno
  have : Fact (¬ IsSquare (δ : k)) := ⟨hns⟩
  have : Finite (extension (δ : k)) :=
    Finite.of_equiv (k × k) (QuadraticAlgebra.equivProd (δ : k) 0).symm
  have hcard := extension_card (δ : k)
  have h9 := (psu_three_pow_facts (by omega : 1 ≤ e)).2 he
  have h1 : 1 < Nat.card k := Finite.one_lt_card
  have hE2 : Nat.card (extension (δ : k)) ≠ 2 := by
    rw [hcard]
    nlinarith
  have hE3 : Nat.card (extension (δ : k)) ≠ 3 := by
    rw [hcard]
    nlinarith
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 (extension (δ : k)) le_rfl (Or.inr hE2)
      (Or.inr hE3)) (specialRho (δ : k) h2) (hermitianSpecialImage_quasisimple (δ : k) h2) hcomm
  have hE : Nat.card (extension (δ : k)) = 3 ^ (2 * e) := by
    rw [hcard, hk, ← pow_mul, mul_comm]
  have hadm : StatedLieAdmissible .PSL 2 3 (2 * e) :=
    OddInner.admissible_PSL Nat.prime_three (by omega) le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  exact PSUHas27Sub.of_lieModel hO _ hq.1 hadm (psu_lieModel_psl_of_equiv_sl (m := 1) hadm hE E)
    (by simp [lieSylowExponent]; omega)

open CatalogueBOrthogonalFourSplit in
theorem psu_orth_split_four (hO : LieOrderFormulasInput) (he : 2 ≤ e) (hk : Nat.card k = 3 ^ e)
    (Q : QuadraticForm k W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank k W = 4)
    (hS : ∃ S : Submodule k W, Module.finrank k S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    (3 ≤ e → PSUHas27Sub (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      (e = 2 → PSUHasPair360 (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have h9 := (psu_three_pow_facts (by omega : 1 ≤ e)).2 he
  have hK2 : Nat.card k ≠ 2 := by rw [hk]; omega
  have hK3 : Nat.card k ≠ 3 := by rw [hk]; omega
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, hcomm12, hperf, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hdim hS
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 k le_rfl (Or.inr hK2)
    (Or.inr hK3)
  have hadm : StatedLieAdmissible .PSL 2 3 e :=
    OddInner.admissible_PSL Nat.prime_three (by omega) le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  obtain ⟨E₁⟩ := nonempty_centerQuotient_equiv_of_eq_map e' hSL
    ((specialRho (K := k)).comp (MonoidHom.inl _ _)) (determinantLeftFactor_quasisimple hK2 hK3)
    (M := (determinantLeftFactor k).map e'.symm.toMonoidHom) rfl
  obtain ⟨E₂⟩ := nonempty_centerQuotient_equiv_of_eq_map e' hSL
    ((specialRho (K := k)).comp (MonoidHom.inr _ _)) (determinantRightFactor_quasisimple hK2 hK3)
    (M := (determinantRightFactor k).map e'.symm.toMonoidHom) rfl
  have hm₁ := psu_lieModel_psl_of_equiv_sl (m := 1) hadm hk E₁
  have hm₂ := psu_lieModel_psl_of_equiv_sl (m := 1) hadm hk E₂
  refine ⟨fun h3 => PSUHas27Sub.of_lieModel hO _ hq₁.1 hadm hm₁ (by simp [lieSylowExponent]; omega),
    fun h2 => ?_⟩
  subst h2
  refine ⟨↥((determinantLeftFactor k).map e'.symm.toMonoidHom),
    ↥((determinantRightFactor k).map e'.symm.toMonoidHom), inferInstance, inferInstance,
    Subgroup.subtype _, Subgroup.subtype _, Subgroup.subtype_injective _,
    Subgroup.subtype_injective _, Group.isPerfect_def.mp hq₁.1, Group.isPerfect_def.mp hq₂.1,
    psu_card_of_lieModel_psl_two_nine hO hadm hm₁, psu_card_of_lieModel_psl_two_nine hO hadm hm₂,
    fun x y => hcomm12 x x.2 y y.2⟩

open CatalogueBOrthogonalFourNonsplit CatalogueBOrthogonalSix in
theorem psu_orth_six_nonsplit_has27 (hO : LieOrderFormulasInput) (he : 1 ≤ e)
    (hk : Nat.card k = 3 ^ e) (Q : QuadraticForm k W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 6)
    (hno : ¬ ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    PSUHas27Sub (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left
      (by norm_num)).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hfact, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_six_derived hodd Q hQ hdim hno
  have : Finite (extension (δ : k)) :=
    Finite.of_equiv (k × k) (QuadraticAlgebra.equivProd (δ : k) 0).symm
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e'
    (sixSpecialUnitary_quasisimple (δ : k) h2) (sixSpecialKappa (δ : k) h2)
    (sixSpecialImage_quasisimple (δ : k) h2) hcomm
  obtain ⟨eU⟩ := exists_six_special_unitary_equiv (δ : k) h2
  have hcardE : Nat.card (extension (δ : k)) = 3 ^ (2 * e) := by
    rw [extension_card, hk, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData 3 e (extension (δ : k)) := ⟨Nat.prime_three, he, hcardE⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP (extension (δ : k)) 3 := hU.charP
  have hF : Nat.card (extension (δ : k)) = (3 ^ e) ^ 2 := by
    rw [hcardE, ← pow_mul, mul_comm]
  have hσ2 : (conjugation (δ : k)).toRingEquiv * (conjugation (δ : k)).toRingEquiv = 1 := by
    rw [← pow_two]
    exact conjugation_square (δ : k)
  have hconj : (conjugation (δ : k)).toRingEquiv =
      LieType.BorelTits.unitaryInvolution (extension (δ : k)) 3 e := by
    rcases UnitaryHigher.ringEquiv_eq_refl_or_bar hU hσ2 with h | h
    · exact absurd h (conjugation_ne_one (δ : k) h2)
    · exact RingEquiv.ext fun c =>
        (h c).trans (LieType.BorelTits.unitaryInvolution_apply _ 3 e c).symm
  have hSU : LieType.Universal.Unitary.SUid (conjugation (δ : k)).toRingEquiv 4 =
      StatedSU 4 (3 ^ e) (extension (δ : k)) := by
    rw [hconj]
    exact LieType.Universal.Unitary.SUid_eq_statedSU hF 4
  have hq3 : 3 ≤ 3 ^ e := (psu_three_pow_facts he).1
  have hnq : ((4 : ℕ), 3 ^ e) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  obtain ⟨-, hZ⟩ := LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF (by norm_num) hnq
  let eSU := eU.trans (MulEquiv.subgroupCongr hSU)
  let eTot := E.trans ((QuotientGroup.congr _ _ eSU (Subgroup.map_center_eq eSU)).trans
    (QuotientGroup.quotientMulEquivOfEq hZ))
  have hadm : StatedLieAdmissible .PSU 4 3 e := ⟨Nat.prime_three, he, by norm_num, hnq⟩
  have hmod : LieModel (commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ⧸
      Subgroup.center (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))) .PSU 4 3 e :=
    LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
      (Or.inl ⟨by decide, ⟨hadm, extension (δ : k), inferInstance, inferInstance, hF,
        ⟨MulEquiv.refl _⟩⟩⟩)
  exact PSUHas27Sub.of_lieModel hO _ hq.1 hadm hmod (by simp [lieSylowExponent]; omega)

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CatLeafProof.KleinSix CatalogueBOrthogonal in
theorem psu_orth_quadPlus_has27 (hO : LieOrderFormulasInput) (he : 1 ≤ e) (hk : Nat.card k = 3 ^ e) :
    PSUHas27Sub (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k)) := by
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left
      (by norm_num)).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hq := derived_quasisimple (quadPlus 3 k) h2 quadPlus_nondegenerate finrank_singularT.ge
    singularT_singular
  have hmap := derived_map_eq_elementary (quadPlus 3 k) h2 quadPlus_nondegenerate
    finrank_singularT.ge singularT_singular
  have hrange := range_eq_elementaryGroup (K := k) h2
  let eD : commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k)) ≃*
      (rhoGL (K := k)).range :=
    ((commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k))).equivMapOfInjective
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k)).subtype
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k)).subtype_injective).trans
      (MulEquiv.subgroupCongr (hmap.trans hrange.symm))
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 4 k (by norm_num)
    (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hrq : CFSG.IsQuasisimple (rhoGL (K := k)).range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eD hq
  obtain ⟨eS⟩ := nonempty_centerQuotient_equiv_range hSL rhoGL (ne_bot_of_isQuasisimple hrq)
  let eTot : commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k)) ⧸
      Subgroup.center (commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k))) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 4) k :=
    (QuotientGroup.congr _ _ eD (Subgroup.map_center_eq eD)).trans eS.symm
  have hq3 : 3 ≤ 3 ^ e := (psu_three_pow_facts he).1
  have hadm : StatedLieAdmissible .PSL 4 3 e :=
    ⟨Nat.prime_three, he, by norm_num, fun h => by have := (Prod.mk.inj h).1; omega,
      fun h => by have := (Prod.mk.inj h).1; omega⟩
  have hmod : LieModel (commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k)) ⧸
      Subgroup.center (commutator (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k)))) .PSL 4 3 e :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
      (Or.inl ⟨by decide, ⟨hadm, k, inferInstance, inferInstance, hk,
        ⟨projectiveSpecialLinearGroupEquivStatedProj 4 k⟩⟩⟩)
  exact PSUHas27Sub.of_lieModel hO _ hq.1 hadm hmod (by simp [lieSylowExponent]; omega)

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalDescent CatLeafProof.KleinSix CatalogueBOrthogonal in
theorem psu_orth_six_split_has27 (hO : LieOrderFormulasInput) (he : 1 ≤ e) (hk : Nat.card k = 3 ^ e)
    (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 6)
    (hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0) :
    PSUHas27Sub (TauCeti.QuadraticMap.orthogonalGroup Q₀) := by
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hQ₀
  have hfin := H.finrank_eq
  have hwitt := H.sourceWittIndex_eq hQ₀
  obtain ⟨T, hTdim, hTQ⟩ := hT
  have h3 := CFSG.Blueprint.EvenSource.le_sourceWittIndex (K := k) (V := W) (⇑Q₀) (W := T) hTQ
  have hm : m = 3 := by omega
  have hδ0 : δ = 0 := by omega
  have H' : HypSplit Q₀ 3 0 := by rw [← hm, ← hδ0]; exact H
  let bk := H'.b.reindex (HypSplit.plusEquiv 3)
  have hS : ∀ w, quadPlus 3 k (bk.equivFun w) = ((1 : kˣ) : k) * Q₀ w := fun w => by
    rw [Units.val_one, one_mul, show quadPlus 3 k (bk.equivFun w) =
      StatedQuadPlus 3 k (bk.equivFun w) from congrFun (coe_quadPlus 3 k) _]
    exact H'.displayPlus w
  let eO : TauCeti.QuadraticMap.orthogonalGroup Q₀ ≃*
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 k) :=
    ((TauCeti.QuadraticMap.orthogonalGroup Q₀).equivMapOfInjective
      (linConj bk.equivFun).toMonoidHom (linConj bk.equivFun).injective).trans
      (MulEquiv.subgroupCongr (map_orthogonalGroup bk.equivFun 1 hS))
  exact PSUHas27Sub.of_mulEquiv eO.symm (psu_orth_quadPlus_has27 hO he hk)

theorem psu_orth_has27 (hO : LieOrderFormulasInput) (he : 1 ≤ e) (hk : Nat.card k = 3 ^ e)
    (Q : QuadraticForm k W) (hQ : Q.polarBilin.Nondegenerate)
    (hcase : 5 ≤ Module.finrank k W ∨ (Module.finrank k W = 3 ∧ 3 ≤ e) ∨
      (Module.finrank k W = 4 ∧ 3 ≤ e) ∨
      (Module.finrank k W = 4 ∧ e = 2 ∧
        ¬ ∃ S : Submodule k W, Module.finrank k S = 2 ∧ ∀ x ∈ S, Q x = 0)) :
    PSUHas27Sub (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  rcases hcase with h5 | ⟨h3, he3⟩ | ⟨h4, he3⟩ | ⟨h4, he2, hno⟩
  · by_cases h5' : Module.finrank k W = 5
    · exact psu_orth_five_has27 hO he hk Q hQ h5'
    · by_cases h6 : Module.finrank k W = 6
      · by_cases hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q x = 0
        · exact psu_orth_six_split_has27 hO he hk Q hQ h6 hT
        · exact psu_orth_six_nonsplit_has27 hO he hk Q hQ h6 hT
      · exact psu_orth_big_has27 hO he hk Q hQ (by omega)
  · exact psu_orth_three_has27 hO he3 hk Q hQ h3
  · by_cases hS : ∃ S : Submodule k W, Module.finrank k S = 2 ∧ ∀ x ∈ S, Q x = 0
    · exact (psu_orth_split_four hO (by omega) hk Q hQ h4 hS).1 he3
    · exact psu_orth_nonsplit_four_has27 hO (by omega) hk Q hQ h4 hS
  · exact psu_orth_nonsplit_four_has27 hO (by omega) hk Q hQ h4 hno

theorem psu_orth_hasPair (hO : LieOrderFormulasInput) (hk : Nat.card k = 3 ^ 2)
    (Q : QuadraticForm k W) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank k W = 4)
    (hS : ∃ S : Submodule k W, Module.finrank k S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    PSUHasPair360 (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  (psu_orth_split_four hO le_rfl hk Q hQ hdim hS).2 rfl

end Orthogonal

section Symplectic

variable {k W : Type} [Field k] [Finite k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  {e : ℕ}

theorem psu_symp_has27 (hO : LieOrderFormulasInput) (he : 1 ≤ e) (hk : Nat.card k = 3 ^ e)
    (B : LinearMap.BilinForm k W) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hdim : 4 ≤ Module.finrank k W) :
    PSUHas27Sub (CatalogueBAlternatingIsometry.isometryGroup B) := by
  obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  obtain ⟨eS⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B hB hnd hdm
  have hm2 : 2 ≤ m := by omega
  have hq3 : 3 ≤ 3 ^ e := (psu_three_pow_facts he).1
  have hadm : StatedLieAdmissible .PSp m 3 e := by
    refine ⟨Nat.prime_three, he, hm2, fun h => ?_⟩
    have h1 : 3 ^ e = 2 := (Prod.mk.inj h).2
    omega
  have hq : CFSG.IsQuasisimple (StatedSp m k) :=
    LieType.Universal.Symplectic.isQuasisimple_of_admissible m k hadm hk
  have hmod : LieModel (↥(StatedSp m k) ⧸ Subgroup.center ↥(StatedSp m k)) .PSp m 3 e :=
    Or.inl ⟨by decide, LieType.Universal.Symplectic.statedClassicalModel_center_quotient m k hadm hk⟩
  refine PSUHas27Sub.of_mulEquiv eS.symm ⟨↥(StatedSp m k), inferInstance, MonoidHom.id _,
    Function.injective_id, Group.isPerfect_def.mp hq.1, psu_dvd_27_of_lieModel hO hadm hmod ?_⟩
  simp only [lieSylowExponent]
  nlinarith

end Symplectic

end CFSG.ComponentClassification.CatFC

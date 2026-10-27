module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3ABridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511
import CFSG.Quasithin.Background.GoldschmidtListedSolv
import CFSG.GH74.KGroups.L3EpsLin
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.Quasithin.SteinbergBYEvenUnitaryTwoThreeControl
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem centerDescend_conj {Y : Type*} [Group Y] (g : Y) :
    centerDescend Y (MulAut.conj g) = MulAut.conj (g : Y ⧸ Subgroup.center Y) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [centerDescend_mk, MulAut.conj_apply, MulAut.conj_apply]
  simp

theorem pow_eq_two_of_not_two_lt {p f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p f F)
    (hle : ¬ 2 < p ^ f) : p ^ f = 2 := by
  have hp := hF.prime
  have hf := hF.one_le
  have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  omega

theorem isSolvable_statedProj_of_pow_eq_two {p f : ℕ} {F : Type} [Field F]
    (hF : UnitaryFieldData p f F) (h2 : p ^ f = 2) :
    Group.IsSolvable (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) := by
  have := hF.finite
  have h2' : p ^ f = 2 ^ 1 := by rw [h2]; rfl
  have hcard : Nat.card F = (2 ^ 1) ^ 2 := by
    rw [hF.card, pow_mul', h2']
  rw [h2']
  exact CFSG.Quasithin.isSolvable_statedProj_one hcard

theorem card_statedProj_of_pow_eq_two {p f : ℕ} {F : Type} [Field F]
    (hF : UnitaryFieldData p f F) (h2 : p ^ f = 2) :
    Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F)) = 72 := by
  have := hF.finite
  have h2' : p ^ f = 2 ^ 1 := by rw [h2]; rfl
  have hcard : Nat.card F = (2 ^ 1) ^ 2 := by
    rw [hF.card, pow_mul', h2']
  rw [h2']
  exact (CFSG.Quasithin.SteinbergBY.card_statedProj_statedSU_three_two le_rfl hcard).trans
    (by norm_num)

theorem two_lt_pow_of_quasisimple {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    {p f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p f F)
    (e : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU hF 3) : 2 < p ^ f := by
  by_contra hle
  have hsol := isSolvable_statedProj_of_pow_eq_two hF (pow_eq_two_of_not_two_lt hF hle)
  have hsolQ : Group.IsSolvable (Y ⧸ Subgroup.center Y) :=
    Group.isSolvable_of_isSolvable_injective (f := (e.trans (psuO hF)).toMonoidHom)
      (e.trans (psuO hF)).injective
  have hsolY : Group.IsSolvable Y :=
    CFSG.Quasithin.isSolvable_of_ker_le_center (QuotientGroup.mk' (Subgroup.center Y))
      (by rw [QuotientGroup.ker_mk'])
  have : Group.IsPerfect Y := (Group.isPerfect_def (G := Y)).2 hY.1
  have : Nontrivial Y := by
    have := hY.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
  exact Group.IsPerfect.not_isSolvable Y hsolY

theorem input7_fieldInn_holds : LocalBalance.Lemma53Ns.Input7_FieldInn := by
  intro K _ _ hK α hα hin
  obtain ⟨g, rfl⟩ := hin
  rcases hα with h1 | hL | hU
  · exact h1
  · obtain ⟨F, _, _, e, σ, γ, he⟩ := fieldAutPSL3_data hL
    have hfin : γ * fieldAut 3 F σ * γ⁻¹ ∈ (stdPinnedPSL 3 F).inndiag := by
      rw [← he, centerDescend_conj, congr_mulAutConj]
      exact (stdPinnedPSL 3 F).inn_le ⟨_, rfl⟩
    have h0 := eq_one_of_isField_mem_inndiag (stdPinnedPSL 3 F) (stdPinnedPSL_separated le_rfl)
      (stdPinnedPSL_stable le_rfl).normal ⟨σ, rfl⟩ γ hfin
    rw [← he] at h0
    exact eq_one_of_centerDescend_eq_one hK
      ((MulAut.congr e).injective (by rw [map_one]; exact h0))
  · obtain ⟨p, f, F, _, hF, e, σ, γ, -, he⟩ := fieldAutPSU3_data hU
    have hq := two_lt_pow_of_quasisimple hK hF e
    have hfin : γ * psuField hF σ * γ⁻¹ ∈ (stdPinnedPSU3 hF).inndiag := by
      rw [← he, centerDescend_conj, congr_mulAutConj]
      exact (stdPinnedPSU3 hF).inn_le ⟨_, rfl⟩
    have h0 := eq_one_of_isField_mem_inndiag (stdPinnedPSU3 hF) (stdPinnedPSU3_separated hF)
      (stdPinnedPSU3_stable hq).normal ⟨σ, rfl⟩ γ hfin
    rw [← he] at h0
    exact eq_one_of_centerDescend_eq_one hK
      ((MulAut.congr e).injective (by rw [map_one]; exact h0))

theorem eq_one_of_odd_orderOf_card_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 2)
    {σ : F ≃+* F} (hσ : Odd (orderOf σ)) : σ = 1 := by
  obtain ⟨-, -, -, -, hc, -⟩ := CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality
    2 2 Nat.prime_two (by norm_num) F hF
  have hd : orderOf σ ∣ 2 := hc ▸ orderOf_dvd_natCard σ
  have h2 : orderOf σ ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  have h1 : orderOf σ = 1 := by
    obtain ⟨k, hk⟩ := hσ
    omega
  exact orderOf_eq_one_iff.1 h1

theorem centerDescend_eq_one_of_field_inner {Y : Type*} [Group Y] {y : Y}
    (h : IsFieldAutThree (MulAut.conj y)) :
    centerDescend Y (MulAut.conj y) = 1 ∧
      (MulAut.conj y = 1 ∨
        (∃ (F : Type) (_ : Field F) (_ : Finite F),
          Nonempty ((Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 F)) ∨
        ∃ (p f : ℕ) (F : Type) (_ : Field F) (hF : UnitaryFieldData p f F),
          Nonempty ((Y ⧸ Subgroup.center Y) ≃* unitaryPSU hF 3)) := by
  rcases h with h1 | hL | hU
  · exact ⟨by rw [h1, map_one], Or.inl h1⟩
  · obtain ⟨F, _, _, e, σ, γ, he⟩ := fieldAutPSL3_data hL
    have hfin : γ * fieldAut 3 F σ * γ⁻¹ ∈ (stdPinnedPSL 3 F).inndiag := by
      rw [← he, centerDescend_conj, congr_mulAutConj]
      exact (stdPinnedPSL 3 F).inn_le ⟨_, rfl⟩
    have h0 := eq_one_of_isField_mem_inndiag (stdPinnedPSL 3 F) (stdPinnedPSL_separated le_rfl)
      (stdPinnedPSL_stable le_rfl).normal ⟨σ, rfl⟩ γ hfin
    rw [← he] at h0
    exact ⟨(MulAut.congr e).injective (by rw [map_one]; exact h0),
      Or.inr (Or.inl ⟨F, inferInstance, inferInstance, ⟨e⟩⟩)⟩
  · obtain ⟨p, f, F, _, hF, e, σ, γ, hodd, he⟩ := fieldAutPSU3_data hU
    have hmain : γ * psuField hF σ * γ⁻¹ = 1 := by
      by_cases hq : 2 < p ^ f
      · have hfin : γ * psuField hF σ * γ⁻¹ ∈ (stdPinnedPSU3 hF).inndiag := by
          rw [← he, centerDescend_conj, congr_mulAutConj]
          exact (stdPinnedPSU3 hF).inn_le ⟨_, rfl⟩
        exact eq_one_of_isField_mem_inndiag (stdPinnedPSU3 hF) (stdPinnedPSU3_separated hF)
          (stdPinnedPSU3_stable hq).normal ⟨σ, rfl⟩ γ hfin
      · have hp := hF.prime
        have hf := hF.one_le
        have := hF.finite
        have h2 : p ^ f = 2 := by
          have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
          omega
        have hcard : Nat.card F = 2 ^ 2 := by rw [hF.card, pow_mul', h2]
        rw [eq_one_of_odd_orderOf_card_four hcard hodd, map_one]
        group
    rw [← he] at hmain
    exact ⟨(MulAut.congr e).injective (by rw [map_one]; exact hmain),
      Or.inr (Or.inr ⟨p, f, F, inferInstance, hF, ⟨e⟩⟩)⟩

theorem eq_one_of_centerDescend_eq_one_of_center_bot {Y : Type*} [Group Y]
    (hZ : Subgroup.center Y = ⊥) {α : MulAut Y} (h : centerDescend Y α = 1) : α = 1 := by
  ext z
  have h1 := congrArg (fun τ : MulAut (Y ⧸ Subgroup.center Y) => τ (z : Y ⧸ Subgroup.center Y)) h
  simp only [centerDescend_mk, MulAut.one_apply] at h1
  have h2 := QuotientGroup.eq.mp h1.symm
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h2
  simpa using h2.symm

theorem center_eq_bot_of_card_eq {Y Q : Type*} [Group Y] [Finite Y] [Group Q]
    (e : (Y ⧸ Subgroup.center Y) ≃* Q) (h : Nat.card Q = Nat.card Y) :
    Subgroup.center Y = ⊥ := by
  have h1 := (Subgroup.center Y).card_mul_index
  have h2 : Nat.card (Y ⧸ Subgroup.center Y) = Nat.card Y := by rw [Nat.card_congr e.toEquiv, h]
  have hpos : 0 < Nat.card Y := Nat.card_pos
  rw [Subgroup.index, h2] at h1
  have : Nat.card (Subgroup.center Y) = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hpos (h1.trans (one_mul _).symm)
    exact this
  exact Subgroup.eq_bot_of_card_eq _ this

theorem isPerfect_nontrivial_projectiveSL (F : Type) [Field F] :
    Group.IsPerfect (projectiveSL 3 F) ∧ Nontrivial (projectiveSL 3 F) := by
  have hsimple : IsSimpleGroup (projectiveSL 3 F) := by
    have := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by omega)
      (Or.inl le_rfl)).2.1
    exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.isSimpleGroup
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  exact ⟨Group.IsPerfect.ofSurjective (proj_surjective 3 F),
    hsimple.toNontrivial⟩

theorem isPerfect_nontrivial_unitaryPSU {p f : ℕ} {F : Type} [Field F]
    (hF : UnitaryFieldData p f F) (hq : 2 < p ^ f) :
    Group.IsPerfect (unitaryPSU hF 3) ∧ Nontrivial (unitaryPSU hF 3) := by
  have := hF.finite
  have : Fact p.Prime := ⟨hF.prime⟩
  have hcard : Nat.card F = (p ^ f) ^ 2 := by rw [hF.card, ← pow_mul, mul_comm]
  have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := fun h => by
    simp only [Prod.mk.injEq, true_and] at h
    omega
  obtain ⟨hqs, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard
    le_rfl hnq
  have hperf : Group.IsPerfect (unitarySU p f F 3) := isPerfect_unitarySU_three hF hq
  have hs : IsSimpleGroup (↥(unitarySU p f F 3) ⧸ Subgroup.center ↥(unitarySU p f F 3)) := hqs.2.1
  have : Nontrivial (↥(unitarySU p f F 3) ⧸ Subgroup.center ↥(unitarySU p f F 3)) :=
    hs.toNontrivial
  exact ⟨Group.IsPerfect.ofSurjective (unitaryProj_surjective hF 3),
    (suCenterEquiv hF hq).injective.nontrivial⟩

theorem inputL3FieldInner_holds : LocalBalance.Lemma511Ns.InputL3FieldInner := by
  intro Y _ _ hExt y hα
  obtain ⟨hcd, hcase⟩ := centerDescend_eq_one_of_field_inner hα
  have key : Subgroup.center Y = ⊥ → MulAut.conj y = 1 := fun hZ =>
    eq_one_of_centerDescend_eq_one_of_center_bot hZ hcd
  rcases hExt with ⟨F, _, _, -, ⟨e⟩⟩ | ⟨F, _, _, q, hcard, -, -, ⟨e⟩⟩
  · exact key (center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans (psiO F))
      (CFSG.GH74.KGroups.L3Eps.center_projectiveSL_three_eq_bot))
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    by_cases hq : 2 < p ^ f
    · exact key (center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans (psuO hF).symm)
        (center_unitaryPSU_three_eq_bot hF hq))
    · have h2 := pow_eq_two_of_not_two_lt hF hq
      have hsolY : Group.IsSolvable Y := by
        have := isSolvable_statedProj_of_pow_eq_two hF h2
        exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      have hsolQ : Group.IsSolvable (Y ⧸ Subgroup.center Y) := inferInstance
      rcases hcase with h1 | ⟨F', _, _, ⟨e'⟩⟩ | ⟨p', f', F', _, hF', ⟨e'⟩⟩
      · exact h1
      · exfalso
        obtain ⟨hperf, hnt⟩ := isPerfect_nontrivial_projectiveSL F'
        have : Group.IsSolvable (projectiveSL 3 F') :=
          Group.isSolvable_of_isSolvable_injective (f := e'.symm.toMonoidHom) e'.symm.injective
        exact Group.IsPerfect.not_isSolvable _ this
      · by_cases hq' : 2 < p' ^ f'
        · exfalso
          obtain ⟨hperf, hnt⟩ := isPerfect_nontrivial_unitaryPSU hF' hq'
          have : Group.IsSolvable (unitaryPSU hF' 3) :=
            Group.isSolvable_of_isSolvable_injective (f := e'.symm.toMonoidHom) e'.symm.injective
          exact Group.IsPerfect.not_isSolvable _ this
        · refine key (center_eq_bot_of_card_eq e' ?_)
          have := hF'.finite
          have c1 : Nat.card (unitaryPSU hF' 3) = 72 := by
            rw [Nat.card_congr (psuO hF').toEquiv]
            exact card_statedProj_of_pow_eq_two hF' (pow_eq_two_of_not_two_lt hF' hq')
          have c2 : Nat.card Y = 72 := by
            rw [Nat.card_congr e.toEquiv]
            exact card_statedProj_of_pow_eq_two hF h2
          rw [c1, c2]

end CFSG.HardMathSupport.Solomon.Coordinator

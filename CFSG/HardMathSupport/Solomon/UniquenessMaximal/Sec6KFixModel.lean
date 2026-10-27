module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap510
public import CFSG.HardMathSupport.Solomon.Proving.L34Cover
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldCases
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldGlue
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldPSU

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem kfix_center_bot_psl {Y : Type*} [Group Y] {F : Type} [Field F]
    (e : Y ≃* StatedProj (StatedSL 3 F)) : Subgroup.center Y = ⊥ := by
  have := CFSG.HardMathSupport.Solomon.Proving.isPerfect_statedSL_three F
  have h0 := Group.IsPerfect.center_quotient_center_eq_bot ↥(StatedSL 3 F)
  have hc : Subgroup.center ↥(StatedSL 3 F) =
      (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) := by
    exact (Subgroup.map_center_eq
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F)).symm.trans
      (CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 3 F)
  let E : (↥(StatedSL 3 F) ⧸ Subgroup.center ↥(StatedSL 3 F)) ≃* StatedProj (StatedSL 3 F) :=
    QuotientGroup.quotientMulEquivOfEq hc
  exact center_eq_bot_of_mulEquiv_of_center_eq_bot e
    (center_eq_bot_of_mulEquiv_of_center_eq_bot E.symm h0)

theorem kfix_exists_unitaryFieldData {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq1 : q ≠ 1) :
    ∃ p f : ℕ, q = p ^ f ∧ UnitaryFieldData p f K := by
  have := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  have hdvd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hcard]; ring⟩
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨p, k, rfl, hp, ?_, by rw [hK, ← pow_mul, mul_comm]⟩
  by_contra h
  have hk : k = 0 := by omega
  rw [hk, pow_zero] at hq1
  exact hq1 rfl

theorem kfix_center_bot_psu {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) {p f : ℕ}
    {K : Type} [Field K] (hK : UnitaryFieldData p f K)
    (e : Y ≃* StatedProj (StatedSU 3 (p ^ f) K)) : Subgroup.center Y = ⊥ := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have hcard : Nat.card K = (p ^ f) ^ 2 := by rw [hK.card, ← pow_mul, mul_comm]
  have h2 : (3, p ^ f) ≠ (3, 2) := by
    intro h
    have h' : p ^ f = 2 := (Prod.mk.inj h).2
    have hsol := isSolvable_statedProj_of_pow_eq_two hK h'
    have hsolY : Group.IsSolvable Y :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have : Group.IsPerfect Y := (Group.isPerfect_def (G := Y)).2 hY.1
    have : Nontrivial Y := by
      have := hY.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
    exact Group.IsPerfect.not_isSolvable Y hsolY
  obtain ⟨hq, hc⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard
    (le_refl 3) h2
  have : Group.IsPerfect ↥(StatedSU 3 (p ^ f) K) := hq.1
  have h0 := Group.IsPerfect.center_quotient_center_eq_bot ↥(StatedSU 3 (p ^ f) K)
  let E : (↥(StatedSU 3 (p ^ f) K) ⧸ Subgroup.center ↥(StatedSU 3 (p ^ f) K)) ≃*
      StatedProj (StatedSU 3 (p ^ f) K) := QuotientGroup.quotientMulEquivOfEq hc
  exact center_eq_bot_of_mulEquiv_of_center_eq_bot e
    (center_eq_bot_of_mulEquiv_of_center_eq_bot E.symm h0)

theorem kfix_center_bot {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) {r : ℕ}
    (hr : IsL3Raw r Y) : Subgroup.center Y = ⊥ := by
  rcases hr with ⟨F, _, _, -, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · exact kfix_center_bot_psl e
  · have hr1 : r ≠ 1 := by
      rintro rfl
      have := Finite.one_lt_card (α := F)
      rw [hF] at this
      simp at this
    obtain ⟨p, f, rfl, hK⟩ := kfix_exists_unitaryFieldData hF hr1
    exact kfix_center_bot_psu hY hK e

noncomputable def kfixEquivOfMap {Y P : Type*} [Group Y] [Group P] (π : Y →* P)
    (hπ : Function.Injective π) {L : Subgroup Y} {T : Subgroup P} (hL : L.map π = T) :
    ↥L ≃* ↥T :=
  (L.equivMapOfInjective π hπ).trans (MulEquiv.subgroupCongr hL)

theorem kfix_barOf_equiv_of_simple {Y : Type} [Group Y] [Finite Y] {P : Type*} [Group P]
    (π : Y →* P) (hπ : Function.Injective π) {L : Subgroup Y} {T : Subgroup P}
    (hL : L.map π = T) (hq : CFSG.Open.IsQuasisimple ↥L) (hs : IsSimpleGroup ↥T)
    (hna : ∃ a b : ↥T, a * b ≠ b * a) (h3 : 3 ∣ Nat.card ↥T) :
    Nonempty (barOf 3 L ≃* ↥T) := by
  have hTZ : Subgroup.center ↥T = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥T) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hna
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  have e := kfixEquivOfMap π hπ hL
  have hLZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_mulEquiv_of_center_eq_bot e hTZ
  have h3L : 3 ∣ Nat.card ↥L := by rwa [Nat.card_congr e.toEquiv]
  have hO : GLAPPrimeCore 3 ↥L = ⊥ :=
    glaPPrimeCore_eq_bot_of_quasisimple hq (fun z hz => by
      rw [hLZ, Subgroup.mem_bot] at hz; rw [hz, one_pow]) h3L
  exact ⟨(barEquivOfCore hO).symm.trans e⟩

open CFSG.GH74.GLS.IVK CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem kfix_orderOf_eq_three {F : Type} [Field F] [Finite F] {σ : F ≃+* F}
    (h : (fieldAut 3 F σ) ^ 3 = 1) (h1 : fieldAut 3 F σ ≠ 1) : orderOf σ = 3 := by
  have hinj : ∀ τ : F ≃+* F, fieldAut 3 F τ = 1 → τ = 1 := fun τ hτ =>
    (eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) le_rfl 1 τ
      (by rw [map_one, one_mul]; exact hτ)).1
  have h3 : σ ^ 3 = 1 := hinj _ (by rw [map_pow]; exact h)
  have hne : σ ≠ 1 := fun h' => h1 (by rw [h', map_one])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h3 hne

theorem kfix_fixSub_eq {Y : Type*} [Group Y] (α : MulAut Y) :
    Lemma53Ns.fixSub α = Lemma510Ns.fixSub α := rfl

theorem kfix_no_comp_of_layer_bot {Y : Type*} [Group Y] [Finite Y] {X : Subgroup Y}
    (h : GLAPLayer 3 X = ⊥) : ∀ J : Subgroup Y, ¬ GLAPComponent 3 X J := fun _ hJ =>
  Lemma510Ns.glaPComponent_ne_bot hJ (le_bot_iff.1 (h ▸ le_sSup hJ))

open CFSG.GH74.GLS.IVK CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem kfix_yfix_psl {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hcore : GLAPPrimeCore 3 Y = ⊥) (hiso : InputL3iso) {r : ℕ} (hr : IsL3Raw r Y)
    {α : MulAut Y} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) (hf : IsFieldAutPSL3 α) :
    ∃ r0 : ℕ, r = r0 ^ 3 ∧ IsPSLn 3 r Y ∧ ¬ IsPSUn 3 r Y ∧ ∃ L : Subgroup Y,
      (∀ J : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub α) J ↔ J = L) ∧
        IsPSLn 3 r0 (barOf 3 L) := by
  have hZ := kfix_center_bot hY hr
  obtain ⟨F, _, _, e, σ, hψ⟩ := l3bf_cases_psl hf
  let eY : Y ≃* projectiveSL 3 F := (barEquivBot hZ).symm.trans e
  have h2 : IsPSLn 3 (Nat.card F) Y := ⟨F, inferInstance, inferInstance, rfl, ⟨eY.trans (psiO F).symm⟩⟩
  have hrF : r = Nat.card F := (hiso Y r (Nat.card F) hr (Or.inl h2)).1
  have hψ3 : (fieldAut 3 F σ) ^ 3 = 1 := by
    rw [← hψ, ← map_pow, ← map_pow, hα3, map_one, map_one]
  have hψ1 : fieldAut 3 F σ ≠ 1 := by
    intro h
    apply hα1
    apply eq_one_of_centerDescend_eq_one hY
    apply (MulAut.congr e).injective
    rw [hψ, h, map_one]
  have hσ := kfix_orderOf_eq_three hψ3 hψ1
  have hcard : Nat.card F = Nat.card (fixedField σ) ^ 3 := by
    rw [← fixedField_card_pow σ, hσ]
  obtain ⟨-, L, -, hLq, hLmap, hcomp, -⟩ := l3bf_core_layer hcore e α hψ (l3bf_fixData_psl σ)
  let π : Y →* projectiveSL 3 F :=
    (e : _ →* projectiveSL 3 F).comp (QuotientGroup.mk' (Subgroup.center Y))
  have hπ : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = 1 :=
      e.injective (by simpa [π] using hy)
    have h2 := (QuotientGroup.eq_one_iff y).1 this
    rwa [hZ, Subgroup.mem_bot] at h2
  rw [commutator_fix_eq σ] at hLmap
  obtain ⟨hs, hna⟩ := l3bT_quasisimple_data σ
  obtain ⟨eb⟩ := kfix_barOf_equiv_of_simple π hπ hLmap hLq hs hna (three_dvd_card_l3bT σ)
  refine ⟨Nat.card (fixedField σ), by rw [hrF, hcard], ?_, ?_, L,
    fun J => by rw [kfix_fixSub_eq] at hcomp; exact hcomp J, ?_⟩
  · exact ⟨F, inferInstance, inferInstance, hrF.symm, ⟨eY.trans (psiO F).symm⟩⟩
  · exact fun h => (hiso Y (Nat.card F) r (Or.inl h2) hr).2 ⟨h2, h⟩
  · refine ⟨fixedField σ, inferInstance, inferInstance, rfl, ⟨?_⟩⟩
    exact eb.trans ((l3bTEquiv σ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 (fixedField σ))).symm.trans
        (psiO (fixedField σ)).symm))

open CFSG.GH74.GLS.IVK in
theorem kfix_yfix_psu {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hcore : GLAPPrimeCore 3 Y = ⊥) (hiso : InputL3iso) {r : ℕ} (hr : IsL3Raw r Y)
    {α : MulAut Y} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) (hf : IsFieldAutPSU3 α) :
    ∃ r0 : ℕ, r = r0 ^ 3 ∧ IsPSUn 3 r Y ∧ ¬ IsPSLn 3 r Y ∧
      ((∃ L : Subgroup Y, (∀ J : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub α) J ↔ J = L) ∧
          IsPSUn 3 r0 (barOf 3 L)) ∨
        ((∀ J : Subgroup Y, ¬ GLAPComponent 3 (Lemma510Ns.fixSub α) J) ∧ r = 8)) := by
  have hZ := kfix_center_bot hY hr
  have hα : orderOf α = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hα3 hα1
  obtain ⟨p, f, f₀, K, _, hK, e, σ, hσ, hff, h₀, hψ⟩ := l3bf_cases_psu hY hα hf
  have := hK.finite
  have hKc : Nat.card K = (p ^ f) ^ 2 := by rw [hK.card, ← pow_mul, mul_comm]
  let eY : Y ≃* unitaryPSU hK 3 := (barEquivBot hZ).symm.trans e
  have h2 : IsPSUn 3 (p ^ f) Y :=
    ⟨K, inferInstance, inferInstance, hKc, ⟨eY.trans (psuO hK)⟩⟩
  have hrF : r = p ^ f ∧ ¬ (IsPSLn 3 r Y ∧ IsPSUn 3 (p ^ f) Y) :=
    hiso Y r (p ^ f) hr (Or.inr h2)
  have hcube : p ^ f = (p ^ f₀) ^ 3 := (congrArg (p ^ ·) hff).trans (pow_mul' p 3 f₀)
  refine ⟨p ^ f₀, by rw [hrF.1, hcube], by rw [hrF.1]; exact h2, fun h => hrF.2 ⟨h, h2⟩, ?_⟩
  by_cases hq : p ^ f₀ = 2
  · refine Or.inr ⟨?_, by rw [hrF.1, hcube, hq]; norm_num⟩
    have := l3bf_layer_bot_of_descent e α hψ (l3bUfix_solvable hK hff h₀ hq)
    rw [kfix_fixSub_eq] at this
    exact kfix_no_comp_of_layer_bot this
  · refine Or.inl ?_
    obtain ⟨-, L, -, hLq, hLmap, hcomp, -⟩ :=
      l3bf_core_layer hcore e α hψ (l3bf_fixData_psu hK hff h₀ hq)
    let π : Y →* unitaryPSU hK 3 :=
      (e : _ →* unitaryPSU hK 3).comp (QuotientGroup.mk' (Subgroup.center Y))
    have hπ : Function.Injective π := by
      rw [injective_iff_map_eq_one]
      intro y hy
      have : (QuotientGroup.mk y : Y ⧸ Subgroup.center Y) = 1 :=
        e.injective (by simpa [π] using hy)
      have h2 := (QuotientGroup.eq_one_iff y).1 this
      rwa [hZ, Subgroup.mem_bot] at h2
    rw [commutator_fix_eq_U hK hff h₀ hq] at hLmap
    obtain ⟨hs, hna⟩ := l3bUT_quasisimple_data hK hff h₀ hq
    obtain ⟨eb⟩ := kfix_barOf_equiv_of_simple π hπ hLmap hLq hs hna
      (three_dvd_card_l3bUT hK hff h₀)
    refine ⟨L, fun J => by rw [kfix_fixSub_eq] at hcomp; exact hcomp J, ?_⟩
    have := h₀.finite
    refine ⟨fixedField σ, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
    · rw [h₀.card, ← pow_mul, mul_comm]
    · exact eb.trans ((l3bUTEquiv hK hff h₀).symm.trans (psuO h₀))

theorem kfix_yfix {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hcore : GLAPPrimeCore 3 Y = ⊥) (hiso : InputL3iso) {r : ℕ} (hr : IsL3Raw r Y)
    {α : MulAut Y} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) (hfld : IsFieldAutThree α) :
    ∃ r0 : ℕ, r = r0 ^ 3 ∧
      ((∃ L : Subgroup Y, (∀ J : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub α) J ↔ J = L) ∧
          (IsPSLn 3 r Y → IsPSLn 3 r0 (barOf 3 L)) ∧ (IsPSUn 3 r Y → IsPSUn 3 r0 (barOf 3 L))) ∨
        ((∀ J : Subgroup Y, ¬ GLAPComponent 3 (Lemma510Ns.fixSub α) J) ∧ r = 8 ∧
          IsPSUn 3 8 Y)) := by
  rcases hfld with h1 | hpsl | hpsu
  · exact absurd h1 hα1
  · obtain ⟨r0, hr0, hPSL, hnPSU, L, hc, hL⟩ := kfix_yfix_psl hY hcore hiso hr hα3 hα1 hpsl
    exact ⟨r0, hr0, Or.inl ⟨L, hc, fun _ => hL, fun h => absurd h hnPSU⟩⟩
  · obtain ⟨r0, hr0, hPSU, hnPSL, h⟩ := kfix_yfix_psu hY hcore hiso hr hα3 hα1 hpsu
    refine ⟨r0, hr0, ?_⟩
    rcases h with ⟨L, hc, hL⟩ | ⟨hno, hr8⟩
    · exact Or.inl ⟨L, hc, fun h => absurd h hnPSL, fun _ => hL⟩
    · exact Or.inr ⟨hno, hr8, hr8 ▸ hPSU⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

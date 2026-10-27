module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClSetup
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClUnitary
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClNum
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClRank
import CFSG.ClassicalInvolution.Orders.Symplectic
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private theorem derived_equiv {G : Type*} [Group G] {X B : Type*} [Group X] [Group B] {A : Subgroup G}
    (φ : A ≃* B) (θ : X →* B) (hθi : Function.Injective θ) (hθ : θ.range = commutator B) :
    Nonempty (X ≃* ↥⁅A, A⁆) := by
  have hr := range_comp_eq_commutator φ θ hθ
  have hi : Function.Injective (A.subtype.comp (φ.symm.toMonoidHom.comp θ)) :=
    Subtype.val_injective.comp (φ.symm.injective.comp hθi)
  exact ⟨(MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr)⟩

private theorem psp_card_ne_sixty {E : Type} [Field E] [Finite E] {m : ℕ} (hm : 2 ≤ m)
    (hne : (m, Nat.card E) ≠ (2, 2)) : Nat.card (StatedProj (StatedSp m E)) ≠ 60 := by
  intro h60
  have hq : 2 ≤ Nat.card E := Nat.succ_le_of_lt Finite.one_lt_card
  have hlt := lt_order_sp (Nat.card E) m hq hm hne
  by_cases h2 : ringChar E = 2
  · haveI : CharP E 2 := h2 ▸ ringChar.charP E
    have := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo (K := E) m
    omega
  · have := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero (K := E) (n := m)
      (Ring.two_ne_zero h2) (by omega)
    omega

private theorem paired_a5 {G : Type*} [Group G] {E : Type} [Field E] [Fintype E] {m : ℕ} {A : Subgroup G}
    (φ : A ≃* Matrix.GeneralLinearGroup (Fin m) E) (hdvd : 5 ∣ Fintype.card E - 1)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆)
    (h60 : Nat.card (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) = 60) : False := by
  classical
  have hE2 : 2 ≤ Fintype.card E := Fintype.one_lt_card
  have h4 : 4 ≤ Fintype.card E := by
    have h0 : 0 < Fintype.card E - 1 := by omega
    have := Nat.le_of_dvd h0 hdvd
    omega
  have hm : 2 ≤ m := by
    by_contra hlt
    haveI := isSolvable_gl_of_le_one (E := E) (Nat.lt_succ_iff.1 (not_le.1 hlt))
    exact not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤ := by
    by_cases h3 : 3 ≤ m
    · exact (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le h3).commutator_eq_top
    · obtain rfl : m = 2 := by omega
      exact (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card E
        (by rwa [Nat.card_eq_fintype_card])).commutator_eq_top
  let θ : Matrix.SpecialLinearGroup (Fin m) E →* Matrix.GeneralLinearGroup (Fin m) E :=
    Matrix.SpecialLinearGroup.toGL
  have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin m) E) := by
    refine range_eq_commutator_of_perfect θ hperf
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) E →* Eˣ) fun g hg => ?_
    rw [MonoidHom.mem_ker] at hg
    have hdet : (g : Matrix (Fin m) (Fin m) E).det = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  obtain ⟨e⟩ := derived_equiv φ θ Matrix.SpecialLinearGroup.toGL_injective hθ
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin m) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) = 60 := by
    rw [card_quotient_center_of_mulEquiv e, h60]
  obtain ⟨-, h45⟩ := sl_a5 hm hcard
  rw [Nat.card_eq_fintype_card] at h45
  omega

open CFSG.ComponentClassification.PresentationLocal (sympFour isSimpleGroup_commutator_sympFour
  isPerfect_commutator_sympFour commutatorEquivAlternating) in
private theorem fixed_a5 {G : Type*} [Group G] {F : Type} [Field F] [Fintype F] {s : ℕ} {A : Subgroup G}
    (φ : A ≃* StatedSp s F) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆)
    (h60 : Nat.card (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) = 60) :
    s = 1 ∧ (Fintype.card F = 4 ∨ Fintype.card F = 5) := by
  classical
  have hFc : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rcases Nat.lt_or_ge s 2 with hs | hs
  · interval_cases s
    · exfalso
      haveI : Subsingleton (StatedSp 0 F) := inferInstance
      haveI : Subsingleton A := φ.toEquiv.subsingleton
      have hsub : Subsingleton ↥⁅A, A⁆ := ⟨fun x y => Subtype.ext (by
        have hx : (x : G) ∈ A := commutator_le_self' A x.2
        have hy : (y : G) ∈ A := commutator_le_self' A y.2
        have hxy : (⟨x, hx⟩ : A) = ⟨y, hy⟩ := Subsingleton.elim _ _
        exact congrArg (Subtype.val : A → G) hxy)⟩
      have : Nat.card (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) = 1 := by
        haveI : Subsingleton (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) := by
          refine ⟨fun a b => ?_⟩
          obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
          obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
          rw [Subsingleton.elim a b]
        exact Nat.card_of_subsingleton (1 : ↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆)
      omega
    · let e1 : Matrix.SpecialLinearGroup (Fin 2) F ≃* StatedSp 1 F :=
        CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne F
      have h4 : 4 ≤ Fintype.card F := four_le_card_of_equiv_sl_two (φ.trans e1.symm) hQ
      have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F
        (by rwa [Nat.card_eq_fintype_card])
      obtain ⟨e⟩ := derived_equiv φ e1.toMonoidHom e1.injective
        (range_equiv_eq_commutator e1 hperf.commutator_eq_top)
      have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F ⧸
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = 60 := by
        rw [card_quotient_center_of_mulEquiv e, h60]
      obtain ⟨-, h45⟩ := sl_a5 (le_refl 2) hcard
      rw [Nat.card_eq_fintype_card] at h45
      exact ⟨rfl, h45⟩
  · exfalso
    by_cases hspecial : s = 2 ∧ Fintype.card F = 2
    · obtain ⟨rfl, hc2⟩ := hspecial
      have hk : Nat.card F = 2 := by rwa [Nat.card_eq_fintype_card]
      obtain ⟨e⟩ := derived_equiv φ (commutator (StatedSp 2 F)).subtype Subtype.val_injective
        (Subgroup.range_subtype _)
      haveI : IsSimpleGroup ↥(commutator sympFour) := isSimpleGroup_commutator_sympFour
      haveI : Group.IsPerfect ↥(commutator sympFour) := isPerfect_commutator_sympFour
      have hcen : Subgroup.center ↥(commutator sympFour) = ⊥ := by
        rcases (inferInstance : (Subgroup.center ↥(commutator sympFour)).Normal).eq_bot_or_eq_top
          with h | h
        · exact h
        · exact absurd (Subgroup.center_eq_top_iff.1 h) (Group.IsPerfect.not_isMulCommutative _)
      have h360 : Nat.card (↥(commutator sympFour) ⧸ Subgroup.center ↥(commutator sympFour)) =
          360 := by
        rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hcen).toEquiv,
          Nat.card_congr QuotientGroup.quotientBot.toEquiv,
          Nat.card_congr commutatorEquivAlternating.toEquiv, Nat.card_eq_fintype_card,
          card_alternatingGroup]
        simp [Nat.factorial]
      have h1 : Nat.card (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) =
          Nat.card (↥(commutator sympFour) ⧸ Subgroup.center ↥(commutator sympFour)) :=
        (card_quotient_center_of_mulEquiv e.symm).trans
          (card_quotient_center_of_mulEquiv (commutatorSpFourEquiv hk))
      omega
    · have hne : (s, Nat.card F) ≠ (2, 2) := fun h => hspecial ⟨congrArg Prod.fst h, by
        rw [Nat.card_eq_fintype_card] at h; exact congrArg Prod.snd h⟩
      have hF' : (Infinite F ∨ 4 ≤ Nat.card F) ∨ (Nat.card F = 3 ∧ 2 ≤ s) ∨
          (Nat.card F = 2 ∧ 3 ≤ s) := by
        have hq : 2 ≤ Nat.card F := Nat.succ_le_of_lt Finite.one_lt_card
        rcases Nat.lt_or_ge (Nat.card F) 4 with h4 | h4
        · rcases (show Nat.card F = 2 ∨ Nat.card F = 3 by omega) with h2 | h3
          · refine Or.inr (Or.inr ⟨h2, ?_⟩)
            by_contra hlt
            exact hne (by rw [show s = 2 by omega, h2])
          · exact Or.inr (Or.inl ⟨h3, hs⟩)
        · exact Or.inl (Or.inr h4)
      obtain ⟨hperf, -, -⟩ := CFSG.LieType.Universal.Symplectic.isQuasisimple s F (by omega) hF'
      obtain ⟨e⟩ := derived_equiv φ (MonoidHom.id _) Function.injective_id (by
        rw [MonoidHom.range_eq_top.2 Function.surjective_id, hperf.commutator_eq_top])
      have hcard : Nat.card (StatedSp s F ⧸ Subgroup.center (StatedSp s F)) = 60 := by
        rw [card_quotient_center_of_mulEquiv e, h60]
      have h60' : Nat.card (StatedProj (StatedSp s F)) = 60 := by
        rw [← Nat.card_congr (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv s F).toEquiv]
        exact hcard
      exact psp_card_ne_sixty hs hne h60'

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.CentralLift CFSG.RankThree.Classical in
private theorem selfdual_a5 {ℓ g : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData ℓ g E) (hℓ5 : ℓ ≠ 5)
    {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) {m : ℕ}
    (b : Module.Basis (Fin m) E V) (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0)
    {G : Type*} [Group G] {A : Subgroup G} (φ : A ≃* sesqUnitaryGroup Hf)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆)
    (h60 : Nat.card (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) = 60) : m = 2 ∧ ℓ ^ g = 4 := by
  classical
  have hfin : Module.finrank E V = m := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hsolv : ¬ (Module.finrank E V ≤ 1 ∨ ¬ ((Module.finrank E V = 2 → 4 ≤ ℓ ^ g) ∧
      (Module.finrank E V = 3 → 3 ≤ ℓ ^ g))) := fun h => by
    haveI := isSolvable_sesqUnitaryGroup_of_small hE hHf hHfl h
    exact not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  rw [hfin] at hsolv
  push Not at hsolv
  obtain ⟨hm, hq2, hq3⟩ := hsolv
  haveI := hE.finite
  haveI := Fintype.ofFinite E
  haveI : Fact ℓ.Prime := ⟨hE.prime⟩
  haveI : CharP E ℓ := hE.charP
  have hEcard : Nat.card E = (ℓ ^ g) ^ 2 := hE.card_eq_sq
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · obtain rfl : m = 2 := by omega
    obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hfin
    haveI : Finite ↥hE.fixedField := inferInstance
    haveI : Fintype ↥hE.fixedField := Fintype.ofFinite _
    have hFcard : Nat.card ↥hE.fixedField = ℓ ^ g := hE.card_fixedField
    have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card ↥hE.fixedField
      (by rw [hFcard]; exact hq2 rfl)
    obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv hE hHf hHfl (by omega) φ
      hperf.commutator_eq_top e
    have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField)) = 60 := by
      rw [card_quotient_center_of_mulEquiv
        ((MonoidHom.ofInjective hψi).trans (MulEquiv.subgroupCongr hψ)), h60]
    obtain ⟨-, h45⟩ := sl_a5 (le_refl 2) hcard
    rw [hFcard] at h45
    refine ⟨rfl, ?_⟩
    rcases h45 with h4 | h5
    · exact h4
    · exact absurd (prime_pow_eq_five hE.prime h5) hℓ5
  · exfalso
    have hnq : (m, ℓ ^ g) ≠ (3, 2) := by
      intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      have := hq3 h1
      omega
    obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin m) (Fin m) E)) (fun i j => by rw [hb i j, Matrix.one_apply])
    have hSUeq : StatedSU m (ℓ ^ g) E = gramSU hE (1 : Matrix (Fin m) (Fin m) E) :=
      unitarySU_eq_gramSU hE m
    let e' : ↥(sesqSpecialUnitaryGroup Hf) ≃* ↥(StatedSU m (ℓ ^ g) E) :=
      e.trans (MulEquiv.subgroupCongr hSUeq.symm)
    have hperf := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hEcard hm3 hnq).1
    obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv hE hHf hHfl (by omega) φ
      hperf.1.commutator_eq_top e'
    have hcard : Nat.card (↥(StatedSU m (ℓ ^ g) E) ⧸ Subgroup.center ↥(StatedSU m (ℓ ^ g) E)) =
        60 := by
      rw [card_quotient_center_of_mulEquiv
        ((MonoidHom.ofInjective hψi).trans (MulEquiv.subgroupCongr hψ)), h60]
    exact su_a5_false hE hm3 hcard

section Orbit

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {F : Type} [Field F]

private theorem sp_orbit_a5 [Finite F] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ5 : ℓ ≠ 5)
    (hK : Nat.card F = ℓ ^ f) {x : StatedSp r F} {a : StatedProj (StatedSp r F)}
    (blocks : SpPrimaryBlocks ℓ f 5 x a) (h : primaryFactors (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {(h : F[X]), reciprocalPolynomial (h : F[X])},
      spSupported x {(h : F[X]), reciprocalPolynomial (h : F[X])}⁆)
    (h60 : Nat.card (↥⁅spSupported x {(h : F[X]), reciprocalPolynomial (h : F[X])},
      spSupported x {(h : F[X]), reciprocalPolynomial (h : F[X])}⁆ ⧸ Subgroup.center
      ↥⁅spSupported x {(h : F[X]), reciprocalPolynomial (h : F[X])},
      spSupported x {(h : F[X]), reciprocalPolynomial (h : F[X])}⁆) = 60) :
    ((h : F[X]) = X - 1 ∧ Module.finrank F (primaryComponent (spEnd x) (X - 1)) = 2 ∧
        ℓ ^ f = 4) ∨
    (reciprocalPolynomial (h : F[X]) = h ∧ (h : F[X]) ≠ X - 1 ∧
      ∃ d : ℕ, (h : F[X]).natDegree = 2 * d ∧ (ℓ ^ f) ^ d = 4 ∧
        primaryMultiplicity (spEnd x) (h : F[X]) = 2) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  by_cases hself : reciprocalPolynomial (h : F[X]) = h
  · have hO : ({(h : F[X]), reciprocalPolynomial (h : F[X])} : Set F[X]) = {(h : F[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO] at hQ h60
    by_cases h1 : (h : F[X]) = X - 1
    · left
      obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r F).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → F)) blocks.fixed_nondegenerate
      obtain ⟨hs1, hF45⟩ := fixed_a5 (φ.trans e) hQ h60
      subst hs1
      refine ⟨rfl, by simpa using hs, ?_⟩
      rw [Fintype.card_eq_nat_card, hK] at hF45
      rcases hF45 with h4 | h5
      · exact h4
      · exact absurd (prime_pow_eq_five hℓ h5) hℓ5
    · right
      obtain ⟨d, hdeg, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, hφ⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      obtain ⟨hm2, hQ4⟩ := selfdual_a5 hE hℓ5 hHf hHfl e he φ hQ h60
      refine ⟨hself, h1, d, hdeg, ?_, hm2⟩
      rw [← pow_mul]
      exact hQ4
  · exfalso
    have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ⟩ := hP.matrixFactor
    haveI : Finite (AdjoinRoot (h : F[X])) := Module.finite_of_finite F
    haveI := Fintype.ofFinite (AdjoinRoot (h : F[X]))
    have hdvd : 5 ∣ Fintype.card (AdjoinRoot (h : F[X])) - 1 := by
      rw [Fintype.card_eq_nat_card, hP.card_field]
      exact hP.dvd
    exact paired_a5 φ hdvd hQ h60

private def OrbitA5 {r : ℕ} {F : Type} [Field F] (ℓ f : ℕ) (x : StatedSp r F)
    (h : primaryFactors (spEnd x)) : Prop :=
  ((h : F[X]) = X - 1 ∧ Module.finrank F (primaryComponent (spEnd x) (X - 1)) = 2 ∧ ℓ ^ f = 4) ∨
    (reciprocalPolynomial (h : F[X]) = h ∧ (h : F[X]) ≠ X - 1 ∧
      ∃ d : ℕ, (h : F[X]).natDegree = 2 * d ∧ (ℓ ^ f) ^ d = 4 ∧
        primaryMultiplicity (spEnd x) (h : F[X]) = 2)

private theorem pow_eq_four {q d : ℕ} (hq : 2 ≤ q) (h : q ^ d = 4) : (d = 1 ∧ q = 4) ∨ (d = 2 ∧ q = 2) := by
  rcases Nat.lt_or_ge d 3 with hd | hd
  · interval_cases d
    · simp at h
    · simp at h
      exact Or.inl ⟨rfl, h⟩
    · have : q ≤ 2 := by
        by_contra hcon
        have h3 : 3 ≤ q := by omega
        have : 3 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h3 2
        omega
      exact Or.inr ⟨rfl, by omega⟩
  · exfalso
    have : 2 ^ 3 ≤ q ^ d := (Nat.pow_le_pow_left hq 3).trans (Nat.pow_le_pow_right (by omega) hd)
    omega

private theorem sum_natDegree_le_five [Finite F] {x : StatedSp r F} (hx : x ^ 5 = 1)
    (hsq : Squarefree (minpoly F (spEnd x))) :
    ∑ h ∈ primaryFactors (spEnd x), h.natDegree ≤ 5 := by
  classical
  have hprod := prod_primaryFactors hsq
  have hne : ∀ h ∈ primaryFactors (spEnd x), h ≠ 0 := fun h hh =>
    (monic_of_mem_primaryFactors hh).ne_zero
  have hdeg : ∑ h ∈ primaryFactors (spEnd x), h.natDegree = (minpoly F (spEnd x)).natDegree := by
    rw [← hprod, Polynomial.natDegree_prod _ _ hne]
  have hX : (spEnd x) ^ 5 = 1 := CFSG.RankThree.Classical.spEnd_pow hx
  have hdvd : minpoly F (spEnd x) ∣ (X ^ 5 - 1 : F[X]) := by
    refine minpoly.dvd F _ ?_
    rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
    exact hX
  rw [hdeg]
  have hX1 : (X ^ 5 - 1 : F[X]) = X ^ 5 - C 1 := by simp
  have hne1 : (X ^ 5 - 1 : F[X]) ≠ 0 := by
    rw [hX1]
    exact Polynomial.X_pow_sub_C_ne_zero (by norm_num) 1
  have h1 := Polynomial.natDegree_le_of_dvd hdvd hne1
  rw [hX1, Polynomial.natDegree_X_pow_sub_C] at h1
  exact h1

private theorem sp_core [Finite F] {ℓ f : ℕ} {x : StatedSp r F} {a : StatedProj (StatedSp r F)}
    (blocks : SpPrimaryBlocks ℓ f 5 x a) (hx5 : x ^ 5 = 1)
    (hsq : Squarefree (minpoly F (spEnd x))) (h₁ h₂ : primaryFactors (spEnd x))
    (hne : ({(h₁ : F[X]), reciprocalPolynomial (h₁ : F[X])} : Set F[X]) ≠
      {(h₂ : F[X]), reciprocalPolynomial (h₂ : F[X])})
    (hq : 2 ≤ ℓ ^ f) (o₁ : OrbitA5 ℓ f x h₁) (o₂ : OrbitA5 ℓ f x h₂) :
    ℓ ^ f = 4 ∧ 3 ≤ r ∧
      (Module.finrank F (primaryComponent (spEnd x) (X - 1)) = 2 ∨ 4 ≤ r) := by
  classical
  obtain ⟨s, hs, ⟨P, hP⟩, hrank⟩ := blocks.rank
  have hr := hrank P hP
  set SD := (primaryFactors (spEnd x)).filter
    (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1) with hSD
  let T : F[X] → ℕ := fun h => h.natDegree / 2 * primaryMultiplicity (spEnd x) h
  have hmem : ∀ h : primaryFactors (spEnd x), reciprocalPolynomial (h : F[X]) = h →
      (h : F[X]) ≠ X - 1 → (h : F[X]) ∈ SD := fun h h1 h2 =>
    Finset.mem_filter.2 ⟨h.2, h1, h2⟩
  have hsingle : ∀ h : primaryFactors (spEnd x), reciprocalPolynomial (h : F[X]) = h →
      (h : F[X]) ≠ X - 1 → T h ≤ ∑ h ∈ SD, T h := fun h h1 h2 =>
    Finset.single_le_sum (f := T) (fun _ _ => Nat.zero_le _) (hmem h h1 h2)
  rcases o₁ with ⟨hf1, hfin1, hq1⟩ | ⟨hs1, hne1, d₁, hd₁, hq₁, hm₁⟩ <;>
  rcases o₂ with ⟨hf2, hfin2, hq2⟩ | ⟨hs2, hne2, d₂, hd₂, hq₂, hm₂⟩
  · exfalso
    apply hne
    rw [hf1, hf2]
  · have hd : d₂ = 1 := by
      rcases pow_eq_four hq hq₂ with ⟨hd, -⟩ | ⟨-, hq2'⟩
      · exact hd
      · omega
    have h2le := hsingle h₂ hs2 hne2
    simp only [T] at h2le
    rw [hd₂, hd, hm₂] at h2le
    have hs1' : s = 1 := by omega
    refine ⟨hq1, by omega, Or.inl hfin1⟩
  · have hd : d₁ = 1 := by
      rcases pow_eq_four hq hq₁ with ⟨hd, -⟩ | ⟨-, hq2'⟩
      · exact hd
      · omega
    have h1le := hsingle h₁ hs1 hne1
    simp only [T] at h1le
    rw [hd₁, hd, hm₁] at h1le
    have hs1' : s = 1 := by omega
    refine ⟨hq2, by omega, Or.inl hfin2⟩
  · have hne12 : (h₁ : F[X]) ≠ h₂ := by
      intro heq
      apply hne
      rw [heq]
    have hsub : ({(h₁ : F[X]), (h₂ : F[X])} : Finset F[X]) ⊆ SD := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hmem h₁ hs1 hne1
      · exact hmem h₂ hs2 hne2
    have hpair : T h₁ + T h₂ ≤ ∑ h ∈ SD, T h := by
      have := Finset.sum_le_sum_of_subset (f := T) hsub
      rwa [Finset.sum_pair hne12] at this
    rcases pow_eq_four hq hq₁ with ⟨hd1, hq4⟩ | ⟨hd1, hq2⟩
    · have hd2 : d₂ = 1 := by
        rcases pow_eq_four hq hq₂ with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · omega
      simp only [T] at hpair
      rw [hd₁, hd₂, hd1, hm₁, hm₂] at hpair
      exact ⟨hq4, by omega, Or.inr (by omega)⟩
    · exfalso
      have hd2 : d₂ = 2 := by
        rcases pow_eq_four hq hq₂ with ⟨-, h⟩ | ⟨h, -⟩
        · omega
        · exact h
      have hsum := sum_natDegree_le_five hx5 hsq
      have hsub' : ({(h₁ : F[X]), (h₂ : F[X])} : Finset F[X]) ⊆ primaryFactors (spEnd x) := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact h₁.2
        · exact h₂.2
      have := Finset.sum_le_sum_of_subset (f := fun h : F[X] => h.natDegree) hsub'
      rw [Finset.sum_pair hne12, hd₁, hd₂, hd1, hd2] at this
      omega

end Orbit

private theorem card_center_quotient_of_map {G T : Type*} [Group G] [Group T] (π : G →* T)
    (hker : π.ker ≤ Subgroup.center G) {H : Subgroup G} (hH : Group.IsPerfect ↥H)
    (h60 : Nat.card (↥(H.map π) ⧸ Subgroup.center ↥(H.map π)) = 60) :
    Nat.card (↥H ⧸ Subgroup.center ↥H) = 60 := by
  have hk : (π.subgroupMap H).ker ≤ Subgroup.center ↥H := by
    intro u hu
    have h1 : π (u : G) = 1 := congrArg Subtype.val hu
    have h3 := hker h1
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.1 h3 _
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hH.commutator_eq_top (π.subgroupMap H)
    (MonoidHom.subgroupMap_surjective π H) hk
  rw [Nat.card_congr e.toEquiv]
  exact h60

section Main

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194 (le_pRank_statedProj_sp statedProjEquivSp)

theorem i1434Cl_PSp {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hm : StatedClassicalModel K .PSp n ℓ f) (hℓ : ℓ ≠ 5) {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (D : I1434.Data K Q x J₁ J₂) :
    ℓ = 2 ∧ f = 2 ∧ n = 3 ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F)
        (e : K ≃* StatedSp 3 F) (A : StatedSp 3 F), Fintype.card F = 4 ∧ e x = A ∧ A ^ 5 = 1 ∧
          A ≠ 1 ∧ Module.finrank F (LinearMap.ker (Matrix.toLin'
            (((A : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) - 1))) = 2 := by
  classical
  obtain ⟨⟨hℓp, hf, hn2, hnq⟩, F, _, _, hF, ⟨eT⟩⟩ := hm
  have hq2 : 2 ≤ ℓ ^ f := hℓp.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ hℓp.ne_zero)
  haveI := hFfin
  haveI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hF]
  haveI : CharP F ℓ := charP_of_card_eq_prime_pow (f := f) hcardF
  have hpℓ : 5 ≠ ℓ := Ne.symm hℓ
  have hr : 1 ≤ n := by omega
  have hx1 := D.ne_one
  have hx5 := D.pow_five
  have hxord : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have hord : orderOf (eT x) = 5 := by
    rw [← hxord]
    exact orderOf_injective eT.toMonoidHom eT.injective x
  obtain ⟨⟨A, ⟨hAa, hAord⟩, -⟩, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks hℓp
    hf hF Nat.prime_five (by norm_num) hpℓ hr (eT x) hord
  have hA5 : A ^ 5 = 1 := by rw [← hAord]; exact pow_orderOf_eq_one A
  have blocks := hblocks A hAa hAord
  have hpK : ((5 : ℕ) : F) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff F ℓ] at h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_five).mp h0).symm
  have hsq := (altPrimaryData_spLin hpK hA5).squarefree
  have hlayer0 := LieSemisimple.perfectInLayer_conj_sp hℓp hf hF hr Nat.prime_five (by norm_num)
    hpℓ A hA5
  have hβ : MulAut.congr eT (MulAut.conj x) = MulAut.conj (SymplecticFlag.proj n F A) := by
    rw [congr_conj_eq, hAa]
  have hlayer : PerfectInLayer (MulAut.congr eT (MulAut.conj x)) := by
    rw [hβ]
    exact hlayer0
  obtain ⟨hc₁, h₁⟩ := five_component_data eT hlayer D.five.comp₁ D.five.quot₁
  obtain ⟨hc₂, h₂⟩ := five_component_data eT hlayer D.five.comp₂ D.five.quot₂
  rw [hβ] at hc₁ hc₂
  have hZc : (SymplecticFlag.proj n F).ker ≤ Subgroup.center (StatedSp n F) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  haveI : Finite (reciprocalOrbits (spEnd A)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hcomp := components_conj_of_orbit_family (SymplecticFlag.proj n F)
    SymplecticHigher.proj_surjective hZc A
    (fun O : reciprocalOrbits (spEnd A) => spSupported A (O : Set F[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
    hjoin (fun O => LieSemisimple.quasisimple_or_solvable_spSupported (by norm_num) hq2 hsq
      blocks O)
  obtain ⟨⟨O₁, h₁', hh₁, rfl⟩, hQ₁, hJ₁⟩ := hcomp _ hc₁
  obtain ⟨⟨O₂, h₂', hh₂, rfl⟩, hQ₂, hJ₂⟩ := hcomp _ hc₂
  have h60₁ : Nat.card (↥⁅spSupported A {h₁', reciprocalPolynomial h₁'},
      spSupported A {h₁', reciprocalPolynomial h₁'}⁆ ⧸ Subgroup.center
      ↥⁅spSupported A {h₁', reciprocalPolynomial h₁'},
      spSupported A {h₁', reciprocalPolynomial h₁'}⁆) = 60 := by
    refine card_center_quotient_of_map (SymplecticFlag.proj n F) hZc hQ₁.1 ?_
    rw [← hJ₁]
    exact h₁
  have h60₂ : Nat.card (↥⁅spSupported A {h₂', reciprocalPolynomial h₂'},
      spSupported A {h₂', reciprocalPolynomial h₂'}⁆ ⧸ Subgroup.center
      ↥⁅spSupported A {h₂', reciprocalPolynomial h₂'},
      spSupported A {h₂', reciprocalPolynomial h₂'}⁆) = 60 := by
    refine card_center_quotient_of_map (SymplecticFlag.proj n F) hZc hQ₂.1 ?_
    rw [← hJ₂]
    exact h₂
  have o₁ := sp_orbit_a5 hℓp hℓ hF blocks ⟨h₁', hh₁⟩ hQ₁ h60₁
  have o₂ := sp_orbit_a5 hℓp hℓ hF blocks ⟨h₂', hh₂⟩ hQ₂ h60₂
  have hne : ({h₁', reciprocalPolynomial h₁'} : Set F[X]) ≠ {h₂', reciprocalPolynomial h₂'} := by
    intro heq
    apply D.five.ne
    apply Subgroup.map_injective (f := (eT : K →* StatedProj (StatedSp n F))) eT.injective
    have hJ₁' : J₁.map (eT : K →* StatedProj (StatedSp n F)) =
        (⁅spSupported A {h₁', reciprocalPolynomial h₁'},
          spSupported A {h₁', reciprocalPolynomial h₁'}⁆).map (SymplecticFlag.proj n F) := hJ₁
    have hJ₂' : J₂.map (eT : K →* StatedProj (StatedSp n F)) =
        (⁅spSupported A {h₂', reciprocalPolynomial h₂'},
          spSupported A {h₂', reciprocalPolynomial h₂'}⁆).map (SymplecticFlag.proj n F) := hJ₂
    rw [hJ₁', hJ₂', heq]
  obtain ⟨hq4, hr3, hfin⟩ := sp_core blocks hA5 hsq ⟨h₁', hh₁⟩ ⟨h₂', hh₂⟩ hne hq2 o₁ o₂
  obtain ⟨hℓ2, hf2⟩ := prime_pow_eq_four hℓp hq4
  subst hℓ2
  subst hf2
  have hFcard4 : Nat.card F = 4 := by rw [hF]; norm_num
  have h5dvd : 5 ∣ Nat.card F ^ 2 - 1 := by rw [hFcard4]; norm_num
  have hn3 : n ≤ 3 := by
    by_contra hn4
    have := le_pRank_statedProj_sp (K := F) (n := n) Nat.prime_five h5dvd
    exact false_of_four_le_pRank_top
      eT D.rank (by omega)
  have hfin2 : Module.finrank F (primaryComponent (spEnd A) (X - 1)) = 2 := by
    rcases hfin with h | h
    · exact h
    · omega
  obtain rfl : n = 3 := by omega
  refine ⟨rfl, rfl, rfl, F, inferInstance, inferInstance, inferInstance, eT.trans statedProjEquivSp,
    A, ?_, ?_, hA5, ?_, ?_⟩
  · rw [Fintype.card_eq_nat_card, hFcard4]
  · show statedProjEquivSp (eT x) = A
    rw [← hAa]
    rfl
  · intro h1
    apply hx1
    apply eT.injective
    rw [← hAa, h1, map_one, map_one]
  · have h1 : spEnd A - 1 = Matrix.toLin' (((A : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) - 1) := by
      ext v i
      simp [spEnd_apply, Matrix.sub_mulVec]
    rw [← h1, ← blocks.fixed_eq]
    exact hfin2

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

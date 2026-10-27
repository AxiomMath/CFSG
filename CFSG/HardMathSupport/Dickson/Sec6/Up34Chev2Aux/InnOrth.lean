module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnOrthSB
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnOrthFix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
public import CFSG.RankThree.PartOne.S15K.OrthModel
public import CFSG.GroupTheory.WeirSylow.OrthogonalTypes

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Polynomial Module CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks
open Up34Chev2

namespace Up34Chev2

section TLevel


variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem noL34Layer_conj_projOrth_two (hO : LieOrderFormulasInput)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {f₀ : ℕ} (hf₀ : 1 ≤ f₀)
    (hK : Nat.card K = 2 ^ f₀) {b : ProjOrthDerived Q} (hb : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hPIL : PerfectInLayer (MulAut.conj b)) : NoL34Layer (MulAut.conj b) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf₀ hK
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Nontrivial V := by
    obtain ⟨U, hU3, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K) (by
      have := Submodule.finrank_le U
      omega)
  have hord : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hpl : (3 : ℕ) ≠ ringChar K := by rw [ringChar.eq K 2]; omega
  obtain ⟨x, Rep, hxa, hxp, hx, hRep, hNeq, hcases⟩ :=
    exists_lift_isComponentOf_centralizer_cases hQ hT Nat.prime_three (by norm_num) hpl hord
  intro A hA hT3
  obtain ⟨hcomp, hIT, hIZ⟩ := exists_component_of_isLThreeFour_two hPIL hA hT3
  have hcomp' : CFSG.Open.IsComponentOf A
      (Subgroup.centralizer ({b} : Set (ProjOrthDerived Q))) := by
    rw [← fixSubgroup_conj_eq_centralizer']
    exact hcomp
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  rcases hcases A hcomp' with ⟨h, hh, hne1, hq, hAeq⟩ | ⟨hlist, n, C, hsup, hC, hCc, i, hAeq⟩
  ·
    have hhp : h ∈ primaryFactors xe.toLinearMap := hRep.1 hh
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hhp⟩
    have hFΩ : specialBlock Q xe h ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hq.1
        ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    have hinj := CFSG.RankThree.PartOne.S15K.mk_injective_orth hQ
    let eF : ↥(specialBlock Q xe h) ≃* ↥A :=
      (((Subgroup.subgroupOfEquivOfLe hFΩ).symm.trans
        (((specialBlock Q xe h).subgroupOf (orthDerived Q)).equivMapOfInjective _ hinj)).trans
        (MulEquiv.subgroupCongr hAeq.symm))
    have hLF : IsLThreeFour (↥(specialBlock Q xe h) ⧸ Subgroup.center ↥(specialBlock Q xe h)) :=
      IsLThreeFour.of_mulEquiv
        (QuotientGroup.congr _ _ eF.symm (Subgroup.map_center_eq eF.symm)) hIT
    have hZF : ∀ z ∈ Subgroup.center ↥(specialBlock Q xe h), z ^ 3 = 1 → z = 1 := by
      intro z hz hz3
      have hzA : eF z ∈ Subgroup.center ↥A := by
        rw [← Subgroup.map_center_eq eF]
        exact Subgroup.mem_map_of_mem _ hz
      have : eF z = 1 := hIZ _ hzA (by rw [← map_pow, hz3, map_one])
      exact eF.injective (this.trans (map_one eF).symm)
    have hm : 2 ≤ primaryMultiplicity xe.toLinearMap h := by
      by_contra hlt
      have hpos := hx.primaryMultiplicity_pos hhp
      have h1 : primaryMultiplicity xe.toLinearMap h = 1 := by omega
      exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hhp h1)
    by_cases hself : h = reciprocalPolynomial h
    · exact false_of_specialBlock_selfDual hO hf₀ hK hx hhp hne1 hself hm hLF
    · obtain ⟨z, hzF, hzc, hz3, hz1⟩ :=
        specialBlock_central_of_paired hO hf₀ hK hx hhp hne1 hself hm hLF
      have hzm : (⟨z, hzF⟩ : ↥(specialBlock Q xe h)) ∈ Subgroup.center ↥(specialBlock Q xe h) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hzc g g.2)
      exact hz1 (congrArg Subtype.val (hZF _ hzm (Subtype.ext hz3)))
  ·
    have hAle : A ≤ fixedComponentImage Q xe := by
      rw [← hsup, hAeq]
      exact le_iSup C i
    rw [hNeq] at hcomp'
    exact false_of_isComponentOf_fixedLayer hO hf₀ hK hQ hx hlist hcomp' hAle hIT

end TLevel

section Model

theorem exists_projOrth_model_two {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {G : Type} [Group G] {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (Q : QuadraticForm K V),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
        (∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
        Module.finrank K V = 2 * n ∧
        Nat.card K = ℓ ^ f ∧ Nonempty (G ≃* ProjOrthDerived Q) := by
  rcases ht with rfl | rfl
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n)
      (by omega)
    exact ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT,
      CFSG.GroupTheory.WeirSylow.finrank_quadPlus_space (K := K) n, hcard,
      ⟨e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadPlus (n := n) (K := K)))⟩⟩
  · obtain ⟨hadm, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := n) h4 hirr
    exact ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT,
      CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (K := K) (m := n) (by omega), hcard,
      ⟨e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c))⟩⟩

end Model

section Closed


theorem noL34Layer_conj_omega_two (hO : LieOrderFormulasInput) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hG : StatedClassicalModel G t n 2 f) (a : G) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    NoL34Layer (MulAut.conj a) := by
  have hf : 1 ≤ f := hG.1.2.1
  have hPIL : PerfectInLayer (MulAut.conj a) :=
    perfectInLayer_conj_omega (ht.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h)))
      hG Nat.prime_three (by norm_num) (by norm_num) a ha3
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, -, hK, ⟨ε⟩⟩ := exists_projOrth_model_two ht hG
  haveI : Finite (ProjOrthDerived Q) := Finite.of_equiv G ε.toEquiv
  refine noL34Layer_congr ε ?_
  rw [CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj]
  have hb : (ε a) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hb1 : ε a ≠ 1 := fun h => ha1 (ε.injective (h.trans (map_one ε).symm))
  have hPIL' : PerfectInLayer (MulAut.conj (ε a)) := by
    refine perfectInLayer_of_congr ε.symm (MulAut.conj (ε a)) ?_
    rw [CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj, MulEquiv.symm_apply_apply]
    exact hPIL
  exact noL34Layer_conj_projOrth_two hO hQ hT hf hK hb hb1 hPIL'

theorem not_up34Pumpup_conj_omega_two (hO : LieOrderFormulasInput) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {n f : ℕ} (hG : StatedClassicalModel S t n 2 f) (x : S) :
    ¬ Up34Pumpup S (MulAut.conj x) := by
  intro hx
  haveI := hs
  obtain ⟨hx3, hx1, hnl⟩ := (up34Pumpup_iff _).1 hx
  have hcen : Subgroup.center S = ⊥ := up34_center_eq_bot_of_simple hnab
  have hxcube : x ^ 3 = 1 := by
    have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow]; exact hx3
    have h2 : x ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut S => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hcen, Subgroup.mem_bot] at h2
    exact h2
  have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
  exact hnl (noL34Layer_conj_omega_two hO ht hG x hxcube hx1')

end Closed

end Up34Chev2

section Family

open Up34Chev2 CFSG.RankThree.PartOne.Sec66T


theorem up34C2Inn_DHigh_holds : Up34Chev2Inn FamDHigh := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hx
  cases d with
  | D r q =>
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_D r q hv e
    have hC : StatedClassicalModel S .POmegaPlus r q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    rw [hq2] at hC
    exact not_up34Pumpup_conj_omega_two CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      (Or.inl rfl) hs hnab hC x hx
  | _ => exact hF.elim

theorem up34C2Inn_TwD_holds : Up34Chev2Inn FamTwD := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hx
  cases d with
  | twistedD r q =>
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_twistedD r q hv e
    have hC : StatedClassicalModel S .POmegaMinus r q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    rw [hq2] at hC
    exact not_up34Pumpup_conj_omega_two CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      (Or.inr rfl) hs hnab hC x hx
  | _ => exact hF.elim

theorem up34C2Inn_D4_holds : Up34Chev2Inn FamD4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hx
  cases d with
  | D r q =>
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_D r q hv e
    have hC : StatedClassicalModel S .POmegaPlus r q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    rw [hq2] at hC
    exact not_up34Pumpup_conj_omega_two CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      (Or.inl rfl) hs hnab hC x hx
  | _ => exact hF.elim

end Family

end CFSG.HardMathSupport.Dickson.Sec6

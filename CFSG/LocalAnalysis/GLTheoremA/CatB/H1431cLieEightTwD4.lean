module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightOrth
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Image
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHOut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open Polynomial Module QuadraticMap CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.GroupTheory.WeirSylow
open CFSG.HardMathSupport.Dickson.Bal207.OrthFix
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)

local notation "fixSub" => CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup

theorem lieSEight_orth_not_sp48 {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hK : Nat.card K = 8) (hQ : (polarBilin Q).Nondegenerate) (x : orthDerived Q)
    (hx3 : orderOf x = 3) {L : Subgroup (ProjOrthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L
      (Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q))))
    (hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = 1056706560) : False := by
  classical
  have hKor : Nat.card K = 2 ∨ Nat.card K = 8 := Or.inr hK
  have hKf : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hpl : (3 : ℕ) ≠ ringChar K := by
    rw [ringChar.eq K 2]
    norm_num
  have hx := oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ x hx3
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    haveI := hV
    have h1 : x = 1 := Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)
    rw [h1, orderOf_one] at hx3
    omega
  have hLc : Nat.card ↥L = 1056706560 * Nat.card (Subgroup.center ↥L) := by
    rw [← hcard]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hv2 : (1056706560 : ℕ).factorization 2 = 12 :=
    factorization_two_of_eq (N := 1056706560) (a := 12) (u := 257985) (by norm_num) (by decide)
  rcases inner_comp_cases hKor hQ x hx3 hL with ⟨hmem, hq, rfl⟩ | ⟨F, -, hFle, -, hF, rfl⟩
  ·
    set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
    haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) :=
      ⟨irreducible_of_mem_primaryFactors hmem⟩
    have hm2 : 2 ≤ primaryMultiplicity xe.toLinearMap (X ^ 2 + X + 1) := by
      have h1 := hx.primaryMultiplicity_pos hmem
      by_contra hlt
      have hbot := hx.specialBlock_eq_bot_of_finrank_eq_one hmem (by omega)
      have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hq
      rw [hbot] at hnt
      exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt rfl
    have hsΩ : specialBlock Q xe (X ^ 2 + X + 1) ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hq.1
        ((specialBlock_le_isometryCentralizer _).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    let eL : ↥(componentImage Q xe (X ^ 2 + X + 1)) ≃* ↥(specialBlock Q xe (X ^ 2 + X + 1)) :=
      (Subgroup.equivMapOfInjective _ (piOrth Q) (piOrth_injective hQ)).symm.trans
        (Subgroup.subgroupOfEquivOfLe hsΩ)
    have hZ : Odd (Nat.card (Subgroup.center ↥(componentImage Q xe (X ^ 2 + X + 1)))) := by
      rw [Nat.card_congr (Subgroup.centerCongr eL).toEquiv]
      exact odd_card_center_specialBlock_phi hx hmem hm2
    have h12 := factorization_two_card_of_odd_center hZ
    rw [hcard, hv2, Nat.card_congr eL.toEquiv,
      factorization_two_card_specialBlock hx hmem hKf] at h12
    generalize primaryMultiplicity xe.toLinearMap (X ^ 2 + X + 1) = m at h12 hm2
    have hm5 : m ≤ 5 := by
      by_contra hc
      have h : 6 * 5 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases m <;> omega
  ·
    set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
    have : Finite (fixedSpace xe ≃ₗ[K] fixedSpace xe) :=
      Finite.of_injective (fun e : fixedSpace xe ≃ₗ[K] fixedSpace xe => (e : fixedSpace xe → _))
        fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    set R := Q.comp (fixedSpace xe).subtype with hRdef
    have hR : (polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
    have hFΩ : F ≤ orthDerived Q := hFle.trans hx.supportedFixedDerived_le_orthDerived
    let eL : ↥((F.subgroupOf (orthDerived Q)).map (piOrth Q)) ≃* ↥F :=
      (Subgroup.equivMapOfInjective _ (piOrth Q) (piOrth_injective hQ)).symm.trans
        (Subgroup.subgroupOfEquivOfLe hFΩ)
    have hFW : Nat.card ↥(supportedFixedDerived Q xe) = Nat.card ↥(orthDerived R) :=
      Nat.card_congr (supportedFixedDerivedEquiv hx).toEquiv
    have hle : orthDerived R ≤ TauCeti.QuadraticMap.orthogonalGroup R :=
      Subgroup.commutator_le_self _
    obtain ⟨s, hs⟩ := hx.even_finrank_fixed
    by_cases h4 : finrank K (fixedSpace xe) ≤ 4
    ·
      have h12 : 2 ^ 12 ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
        have h1 : 2 ^ 12 ∣ Nat.card ↥((F.subgroupOf (orthDerived Q)).map (piOrth Q)) := by
          rw [hLc]
          exact Dvd.dvd.mul_right (by norm_num) _
        rw [Nat.card_congr eL.toEquiv] at h1
        have h2 := Subgroup.card_dvd_of_le hFle
        rw [hFW] at h2
        exact h1.trans (h2.trans (Subgroup.card_dvd_of_le hle))
      have h12' := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h12
      rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with hs0 | hs1 | hs2
      · have : Subsingleton (fixedSpace xe) := (Module.finrank_zero_iff (R := K)).mp (by omega)
        have h1 : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext (LinearEquiv.ext fun w =>
            Subsingleton.elim _ _)⟩, ⟨1⟩⟩
        rw [h1] at h12
        norm_num at h12
      · rw [factorization_two_card_orthogonalGroup hR (m := 0) (by omega) hKf] at h12'
        omega
      · rw [factorization_two_card_orthogonalGroup hR (m := 1) (by omega) hKf] at h12'
        omega
    · have hFe : F = supportedFixedDerived Q xe := hF.resolve_left h4
      have : Nontrivial (fixedSpace xe) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
      let eLW : ↥((F.subgroupOf (orthDerived Q)).map (piOrth Q)) ≃* ↥(orthDerived R) :=
        eL.trans ((MulEquiv.subgroupCongr hFe).trans (supportedFixedDerivedEquiv hx))
      have hLF : Nat.card ↥((F.subgroupOf (orthDerived Q)).map (piOrth Q)) =
          Nat.card ↥(orthDerived R) := Nat.card_congr eLW.toEquiv
      have hZ : Nat.card (Subgroup.center ↥((F.subgroupOf (orthDerived Q)).map (piOrth Q))) =
          Nat.card (Subgroup.center ↥(orthDerived R)) :=
        Nat.card_congr (Subgroup.centerCongr eLW).toEquiv
      by_cases hT : ∃ U : Submodule K (fixedSpace xe), finrank K U = 3 ∧ ∀ u ∈ U, R u = 0
      ·
        rw [hZ, center_orthDerived_eq_bot hR hT, Subgroup.card_bot, mul_one, hLF] at hLc
        obtain ⟨m, hm⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
        have h1 := factorization_two_card_orthDerived hR hT (m := m) (by omega) hKf
        rw [hLc, hv2] at h1
        have hm4 : m ≤ 4 := by
          by_contra hc
          have h : 5 * 6 ≤ m * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
          omega
        interval_cases m <;> omega
      ·
        have h6 : finrank K (fixedSpace xe) = 6 := by
          by_contra h6
          exact hT (exists_threeSingular_of_dim R hR (m := s) (by omega) (by omega))
        have hts : ∀ U : Submodule K (fixedSpace xe), finrank K U = 3 → ∃ u ∈ U, R u ≠ 0 := by
          intro U hU
          by_contra hcon
          push Not at hcon
          exact hT ⟨U, hU, hcon⟩
        obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hsimple, -, hnab, hcardρ, -, -, -⟩ :=
          even_minus_six_actual_derived_extraction R hR h6 hts
        have he : orthDerived R = ρ.range := hcomm
        haveI := hsimple
        have hZ1 : Nat.card (Subgroup.center ↥ρ.range) = 1 := by
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥ρ.range) with hb | ht
          · rw [hb]
            exact Subgroup.card_bot
          · refine absurd (fun a b => ?_) hnab
            have hb : b ∈ Subgroup.center ↥ρ.range := by
              rw [ht]
              exact Subgroup.mem_top b
            exact Subgroup.mem_center_iff.mp hb a
        rw [hZ, he, hZ1, mul_one, hLF, he, hcardρ, hK] at hLc
        norm_num at hLc

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalAut

theorem lieSEight_d4m_coords {S : Type} [Group S]
    (hM : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .POmegaMinus 4 2 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (Q : QuadraticForm F (Fin (2 * 4) → F)) (_ : S ≃* ProjOrthDerived Q),
      Nat.card F = 2 ^ 3 ∧ (polarBilin Q).Nondegenerate ∧
      (∃ U : Submodule F (Fin (2 * 4) → F), finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) := by
  obtain ⟨hadm, F, hFf, hFfin, hF, b, c, hirr, ⟨e₀⟩⟩ := id hM
  haveI : CharP F 2 := by
    haveI := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 3) (by rw [Fintype.card_eq_nat_card, hF])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hM F hF b c hirr e₀
  exact ⟨F, hFf, hFfin, inferInstance, coordinateQuadMinus 4 F (by norm_num) b c,
    (coordinateMinusWitnessEquiv F (by norm_num) b c e₀).trans
      (coordBridge (coordinateQuadMinus 4 F (by norm_num) b c) (by norm_num)), hF, hnd, hT⟩

theorem lieSEight_d4m_inner_noSp (hLO : LieOrderBridge) {S : Type} [Group S] [Finite S]
    (hM : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .POmegaMinus 4 2 3) {s : S}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ¬ CompOfType S (MulAut.conj s) S8.L84.isSp48 := by
  rintro ⟨J, hJ, hT⟩
  obtain ⟨F, hFf, hFfin, hFchar, Q, eQ, hF, hQ, hT3⟩ := lieSEight_d4m_coords hM
  have ht3 : orderOf (eQ s) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hs3, map_one])
      (fun h => hs1 (eQ.injective (h.trans (map_one eQ).symm)))
  haveI : Finite (ProjOrthDerived Q) := Finite.of_equiv S eQ.toEquiv
  have hJ' : GLAPComponent 3 (fixSub (MulAut.conj (eQ s))) (J.map eQ.toMonoidHom) := by
    rw [← CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj eQ s]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_transport eQ (MulAut.conj s) hJ
  have hpl : (3 : ℕ) ≠ ringChar F := by
    rw [ringChar.eq F 2]
    norm_num
  haveI : Nonempty (Fin (2 * 4)) := ⟨⟨0, by norm_num⟩⟩
  have hlayer := perfectInLayer_conj_projOrth_of_orderOf hQ hT3 Nat.prime_three (by norm_num)
    hpl (eQ s) ht3
  have hle := hlayer _ hJ'.1 (glaPComponent_perfect hJ')
  have hcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJ' hle).1
  haveI : Nontrivial (Fin (2 * 4) → F) := by
    obtain ⟨U, hU3, -⟩ := hT3
    exact Module.nontrivial_of_finrank_pos (R := F)
      (lt_of_lt_of_le (by norm_num : 0 < 3) (hU3 ▸ Submodule.finrank_le U))
  obtain ⟨x, hxt, hx3⟩ := exists_lift_orderOf_three hQ ht3
  rw [fixSubgroup_conj_eq_centralizer, ← hxt] at hcomp
  have hT' : catalogIs (PSimple 3 (J.map eQ.toMonoidHom)) S8.L84.isSp48 :=
    (CFSG.LocalAnalysis.GLTheoremA.T123C.catalogIs_pSimple_map_iff (f := eQ.toMonoidHom)
      eQ.injective 3 J _).2 hT
  have hc := lieSEight_card_quot_center hLO hJ' hcomp.2.2 hT'
  exact lieSEight_orth_not_sp48 (by rw [hF]; norm_num) hQ x hx3 hcomp hc

theorem lieSEightNoAt_twistedD4 (hLO : LieOrderBridge) :
    LieSEightNoAt fun d => ∃ q, d = .twistedD 4 q := by
  rintro Y _ _ hY - - ⟨d, hv⟩ ⟨q, rfl⟩ hc hf ⟨e⟩ α hα hα3 hα1
  have hq8 : q.card = 8 := hf
  have hp2 : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_twistedD 4 q).symm.trans hc
  have hexp : q.exponent = 3 := by
    have h := q.card_def
    rw [hq8, hp2] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num : 8 = 2 ^ 3))
  have hM := CFSG.Models.lieModel_twistedD 4 q hv e
  rw [hp2, hexp] at hM
  have hM' : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Y ⧸ Subgroup.center Y)
      .POmegaMinus 4 2 3 := hM.2.resolve_right (fun h0 => absurd h0.1 (by norm_num))
  have hM'' : CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .POmegaMinus 4 2 3 :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).mpr hM'
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
  have hZ : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := I1431C2.cl_center_eq_bot_of_simple
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY)
  obtain ⟨s, hs⟩ := CFSG.HardMathSupport.Dickson.Sec6.I1431.outDerived3_orthMinusNe3
    (Y ⧸ Subgroup.center Y) .POmegaMinus 4 2 3 ⟨Nat.prime_two, by norm_num, by norm_num⟩
    (by decide) ⟨rfl, by norm_num⟩ hM'' α hα hα3
  rw [← hs] at hα3 hα1 ⊢
  have hs3 : s ^ 3 = 1 := by
    apply CFSG.mulAutConj_injective_of_center_eq_bot hZ
    rw [map_pow, hα3, map_one]
  have hs1 : s ≠ 1 := fun h => hα1 (by rw [h, map_one])
  exact lieSEight_d4m_inner_noSp hLO hM' hs3 hs1

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end

module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Dickson.Bal207.OrthFix

private theorem ordD_four_two_eq_mul : CFSG.Open.ordD 4 2 = 2 ^ 12 * 42525 := by
  unfold CFSG.Open.ordD
  decide

private theorem factorization_two_ordD_four_two : (CFSG.Open.ordD 4 2).factorization 2 = 12 :=
  factorization_two_of_eq ordD_four_two_eq_mul (by decide)

private theorem choose_two_ne_twelve (m : ℕ) : m * (m - 1) / 2 ≠ 12 := by
  intro h
  have hm : m ≤ 6 := by
    by_contra hc
    have h7 : 7 * 6 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  interval_cases m <;> omega

private theorem eq_three_of_mul_succ_eq_twelve {m : ℕ} (h : m * (m + 1) = 12) : m = 3 := by
  have hm : m ≤ 3 := by
    by_contra hc
    have h4 : 4 * 5 ≤ m * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  interval_cases m <;> omega

theorem eq_fixedComponentImage_of_card_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate) (x : orthDerived Q)
    (hx3 : orderOf x = 3) {L : Subgroup (ProjOrthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L
      (Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q))))
    (hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = CFSG.Open.ordD 4 2) :
    finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 8 ∧ L = fixedComponentImage Q (x : V ≃ₗ[K] V) := by
  classical
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
    have h1 : x = 1 := Subtype.ext (LinearEquiv.ext fun _ => Subsingleton.elim _ _)
    rw [h1, orderOf_one] at hx3
    omega
  have hKf : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hLc : Nat.card ↥L = CFSG.Open.ordD 4 2 * Nat.card (Subgroup.center ↥L) := by
    rw [← hcard]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rcases inner_comp_cases (Or.inl hK) hQ x hx3 hL with ⟨hmem, hq, rfl⟩ | ⟨F, -, hFle, -, hF, rfl⟩
  ·
    exfalso
    set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V)
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
    rw [hcard, factorization_two_ordD_four_two, Nat.card_congr eL.toEquiv,
      factorization_two_card_specialBlock hx hmem hKf, one_mul] at h12
    exact choose_two_ne_twelve _ h12
  ·
    set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V)
    have : Finite (fixedSpace xe ≃ₗ[K] fixedSpace xe) :=
      Finite.of_injective (fun e : fixedSpace xe ≃ₗ[K] fixedSpace xe => (e : fixedSpace xe → _))
        fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    set R := Q.comp (fixedSpace xe).subtype
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
      exfalso
      have h12 : 2 ^ 12 ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
        have h1 : 2 ^ 12 ∣ Nat.card ↥((F.subgroupOf (orthDerived Q)).map (piOrth Q)) := by
          rw [hLc, ordD_four_two_eq_mul]
          exact Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _
        rw [Nat.card_congr eL.toEquiv] at h1
        have h2 := Subgroup.card_dvd_of_le hFle
        rw [hFW] at h2
        exact h1.trans (h2.trans (Subgroup.card_dvd_of_le hle))
      have h12' := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h12
      rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with hs0 | hs1 | hs2
      · have : Subsingleton (fixedSpace xe) := (Module.finrank_zero_iff (R := K)).mp (by omega)
        have h1 : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨⟨fun _ _ => Subtype.ext (LinearEquiv.ext fun _ =>
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
        rw [hLc, factorization_two_ordD_four_two, one_mul] at h1
        obtain rfl := eq_three_of_mul_succ_eq_twelve h1.symm
        refine ⟨by omega, ?_⟩
        rw [hFe]
        rfl
      ·
        exfalso
        have h6 : finrank K (fixedSpace xe) = 6 := by
          by_contra h6
          exact hT (exists_threeSingular_of_dim R hR (m := s) (by omega) (by omega))
        have hts : ∀ U : Submodule K (fixedSpace xe), finrank K U = 3 → ∃ u ∈ U, R u ≠ 0 := by
          intro U hU
          by_contra hcon
          push Not at hcon
          exact hT ⟨U, hU, hcon⟩
        obtain ⟨_, _, _, _, -, ρ, -, -, -, -, hcomm, hsimple, -, hnab, hcardρ, -, -, -⟩ :=
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
        rw [hZ, he, hZ1, mul_one, hLF, he, hcardρ, hK, ordD_four_two_eq_mul] at hLc
        norm_num at hLc

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end

module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.GroupTheory.WeirSylow

theorem ordD_four_eight_eq : CFSG.Open.ordD 4 8 = 2 ^ 36 * 276940598796225 := by
  unfold CFSG.Open.ordD
  decide

theorem factorization_two_ordD_four_eight : (CFSG.Open.ordD 4 8).factorization 2 = 36 :=
  factorization_two_of_eq ordD_four_eight_eq (by decide)

theorem seventy_three_dvd_card_d4Eight : 73 ∣ CFSG.Open.ordD 4 8 := by
  rw [ordD_four_eight_eq]
  decide

theorem not_seventy_three_dvd_su_nine_two :
    ¬ (73 : ℤ) ∣ ((2 ^ 1 : ℕ) : ℤ) ^ (9 * (9 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 9, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  decide

theorem eq_nine_of_mul_choose_two {f m : ℕ} (hf : f = 1 ∨ f = 3) (hm : 2 ≤ m)
    (h : f * (m * (m - 1) / 2) = 36) : f = 1 ∧ m = 9 := by
  have hm9 : m ≤ 9 := by
    by_contra hc
    have h10 : 10 * 9 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    rcases hf with rfl | rfl <;> omega
  interval_cases m <;> rcases hf with rfl | rfl <;> exact ⟨by omega, by omega⟩

theorem eq_three_of_mul_succ {f m : ℕ} (hf : f = 1 ∨ f = 3) (h : f * (m * (m + 1)) = 36) :
    f = 3 ∧ m = 3 := by
  have hm : m ≤ 6 := by
    by_contra hc
    have h7 : 7 * 8 ≤ m * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
    rcases hf with rfl | rfl <;> omega
  interval_cases m <;> rcases hf with rfl | rfl <;> exact ⟨by omega, by omega⟩

section Components

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem card_specialBlock_phi {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    (hmem : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors x.toLinearMap) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) :
    (Nat.card (specialBlock Q x (X ^ 2 + X + 1)) : ℤ) =
      ((2 ^ f : ℕ) : ℤ) ^ (primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) *
        (primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 (primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1)),
          (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hirr := irreducible_of_mem_primaryFactors hmem
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨hirr⟩
  obtain ⟨d, ℓ, f', hU, B, -, hq, hBsymm, hBl, hrange⟩ :=
    orth2_exists_unitary_model hx ⟨1, rfl⟩ hmem phi_ne (reciprocal_cyc3 K).symm
  have e₁ : ↥(specialBlock Q x (X ^ 2 + X + 1)) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hmem)).trans
      (MulEquiv.subgroupCongr hrange)
  obtain ⟨-, h1, -⟩ := CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl
    (n := primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1)) rfl
    (hx.primaryMultiplicity_pos hmem)
  have hℓ : ℓ = 2 := by
    have hf' : f' ≠ 0 := by
      rintro rfl
      have := hU.one_le
      rw [zero_mul] at this
      omega
    have h2 : ℓ ∣ 2 ^ f := by
      rw [← hK, hq]
      exact dvd_pow_self ℓ hf'
    exact (Nat.prime_dvd_prime_iff_eq hU.prime Nat.prime_two).mp (hU.prime.dvd_of_dvd_pow h2)
  subst hℓ
  have : Module.Finite K (AdjoinRoot (X ^ 2 + X + 1 : K[X])) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hcardE : Nat.card (AdjoinRoot (X ^ 2 + X + 1 : K[X])) = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, monic_phi.2]
  have hqf : f' * d = f := by
    have h2 := hU.card
    rw [hcardE, hK, ← pow_mul] at h2
    have := Nat.pow_right_injective le_rfl h2
    omega
  rw [Nat.card_congr e₁.toEquiv, h1, hqf]

theorem inner_comp_cases (hK : Nat.card K = 2 ∨ Nat.card K = 8)
    (hQ : (polarBilin Q).Nondegenerate) (x : orthDerived Q) (hx3 : orderOf x = 3)
    {L : Subgroup (ProjOrthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L
      (Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q)))) :
    ((X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap ∧
        CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) (X ^ 2 + X + 1)) ∧
        L = componentImage Q (x : V ≃ₗ[K] V) (X ^ 2 + X + 1)) ∨
      ∃ F : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple ↥F ∧
        F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
        (F.subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal ∧
        (finrank K (fixedSpace (x : V ≃ₗ[K] V)) ≤ 4 ∨
          F = supportedFixedDerived Q (x : V ≃ₗ[K] V)) ∧
        L = (F.subgroupOf (orthDerived Q)).map (piOrth Q) := by
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
    have h1 : x = 1 := Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)
    rw [h1, orderOf_one] at hx3
    omega
  have hpq : 3 ∣ Nat.card K + 1 := by
    rcases hK with h | h <;> rw [h] <;> norm_num
  rw [← centralizerImage_eq hQ x] at hL
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  set N : Subgroup (ProjOrthDerived Q) := centralizerImage Q xe with hN
  obtain ⟨n, F, hFq, hFsup, hFn0, hFix⟩ := exists_fixedFactors' hx
  have hFΩ : ∀ i, F i ≤ orthDerived Q := fun i =>
    (hFq i).2.1.trans hx.supportedFixedDerived_le_orthDerived
  set C : Fin n → Subgroup (ProjOrthDerived Q) := fun i => ((F i).subgroupOf (orthDerived Q)).map ρ
    with hC
  have hCsup : (⨆ i, C i) = fixedLayerImage Q xe := by
    by_cases hlist : FixedLayerListed Q xe
    · rw [fixedLayerImage_of_listed hlist]
      unfold fixedComponentImage
      rw [← hFsup hlist, subgroupOf_iSup_of_le F _ hFΩ, Subgroup.map_iSup]
    · have hn := hFn0 hlist
      subst hn
      simp [fixedLayerImage, hlist]
  have hCle : ∀ i, C i ≤ fixedComponentImage Q xe := fun i =>
    Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
      ((hFq i).2.1 (Subgroup.mem_subgroupOf.mp hg))
  have hCcomp : ∀ i, CFSG.Open.IsComponentOf (C i) N := by
    intro i
    have hconj := map_conj_mem ρ (F := (F i).subgroupOf (orthDerived Q))
      (F' := (supportedFixedDerived Q xe).subgroupOf (orthDerived Q)) (fun h k hh hk => by
        have := (Subgroup.normal_subgroupOf_iff (hFq i).2.1).mp (hFq i).2.2 (h : V ≃ₗ[K] V)
          (k : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr this)
    refine isComponentOf_of_normal_normal (hCle i) fixedComponentImage_le_centralizerImage ?_
      hx.normal_fixedComponentImage (isQuasisimple_map_projective (hFΩ i) (hFq i).1)
    rw [Subgroup.normal_subgroupOf_iff (hCle i)]
    intro h k hh hk
    exact hconj _ _ hh hk
  let ι₁ := {r : ↥Rep // r.1 ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q xe r.1)}
  have hspecΩ : ∀ r : ι₁, specialBlock Q xe r.1.1 ≤ orthDerived Q := fun r =>
    specialBlock_le_orthDerived_of_perfect r.2.2.1
      ((specialBlock_le_isometryCentralizer r.1.1).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let S : ι₁ → Subgroup (ProjOrthDerived Q) := fun r => componentImage Q xe r.1.1
  have hScomp : ∀ r, CFSG.Open.IsComponentOf (S r) N := fun r =>
    isComponentOf_of_normal_normal componentImage_le_centralizerImage le_rfl normal_componentImage
      (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
      (isQuasisimple_map_projective (hspecΩ r) r.2.2)
  set EN : Subgroup (ProjOrthDerived Q) := (⨆ r, S r) ⊔ fixedLayerImage Q xe with hEN
  have hSN : ∀ r, S r ≤ N := fun r => componentImage_le_centralizerImage
  have hENN : EN ≤ N := sup_le (iSup_le hSN) fixedLayerImage_le_centralizerImage
  have hENnormal : (EN.subgroupOf N).Normal :=
    normal_subgroupOf_sup (iSup_le hSN) fixedLayerImage_le_centralizerImage
      (normal_subgroupOf_iSup S hSN fun r => normal_componentImage) hx.normal_fixedLayerImage
  have hENn : ∀ c ∈ N, ∀ e ∈ EN, c * e * c⁻¹ ∈ EN := fun c hc e he =>
    (Subgroup.normal_subgroupOf_iff hENN).mp hENnormal e c he hc
  have hperf : ∀ P : Subgroup (ProjOrthDerived Q), P ≤ N → commutator ↥P = ⊤ → P ≤ EN := by
    intro P hPN hP
    obtain ⟨S₀, hS₀N, hS₀sol, hcomm⟩ := exists_solvable_comm_le hQ Nat.prime_three
      (by norm_num) x hx hRep EN
      (fun h hh hne hq => le_sup_of_le_left (le_iSup S (⟨⟨h, hh⟩, hne, hq⟩ : ι₁)))
      (fun hlist => by
        rw [← fixedLayerImage_of_listed hlist]
        exact le_sup_right)
    haveI := hS₀sol
    exact perfect_le_of_le_sup_solvable hENN hS₀N hENn hcomm hPN (Subgroup.isPerfect_iff.1 ⟨hP⟩)
  let Fm : ι₁ ⊕ Fin n → Subgroup (ProjOrthDerived Q) := Sum.elim S C
  have hFm : ∀ i, CFSG.Open.IsComponentOf (Fm i) N := by
    rintro (r | i)
    · exact hScomp r
    · exact hCcomp i
  have hiSup : (⨆ i, Fm i) = EN := by
    rw [iSup_sum]
    simp only [Fm, Sum.elim_inl, Sum.elim_inr]
    rw [hCsup]
  obtain ⟨i, rfl⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.component_mem_named_factors
    Fm hFm (fun P hPN hP => hiSup ▸ hperf P hPN hP) hL
  rcases i with ⟨⟨h, hh⟩, hne, hq⟩ | i
  · have hh' : h ∈ primaryFactors xe.toLinearMap := hRep.1 hh
    obtain rfl : h = X ^ 2 + X + 1 := eq_phi hx hpq hh' hne
    exact Or.inl ⟨hh', hq, rfl⟩
  · exact Or.inr ⟨F i, (hFq i).1, (hFq i).2.1, (hFq i).2.2, hFix i, rfl⟩

theorem eq_fixedComponentImage_of_card (hK : Nat.card K = 2 ∨ Nat.card K = 8)
    (hQ : (polarBilin Q).Nondegenerate) (x : orthDerived Q) (hx3 : orderOf x = 3)
    {L : Subgroup (ProjOrthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L
      (Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q))))
    (hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = CFSG.Open.ordD 4 8) :
    Nat.card K = 8 ∧ finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 8 ∧
      L = fixedComponentImage Q (x : V ≃ₗ[K] V) := by
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
    have h1 : x = 1 := Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)
    rw [h1, orderOf_one] at hx3
    omega
  obtain ⟨f, hf, hKf⟩ := exists_exp hK
  have hLc : Nat.card ↥L = CFSG.Open.ordD 4 8 * Nat.card (Subgroup.center ↥L) := by
    rw [← hcard]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rcases inner_comp_cases hK hQ x hx3 hL with ⟨hmem, hq, rfl⟩ | ⟨F, -, hFle, -, hF, rfl⟩
  ·
    exfalso
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
    have h36 := factorization_two_card_of_odd_center hZ
    rw [hcard, factorization_two_ordD_four_eight, Nat.card_congr eL.toEquiv,
      factorization_two_card_specialBlock hx hmem hKf] at h36
    obtain ⟨rfl, hm9⟩ := eq_nine_of_mul_choose_two hf hm2 h36
    have h73 : 73 ∣ Nat.card ↥(specialBlock Q xe (X ^ 2 + X + 1)) := by
      rw [← Nat.card_congr eL.toEquiv]
      exact seventy_three_dvd_card_d4Eight.trans ⟨_, hLc⟩
    have h73' : (73 : ℤ) ∣ (Nat.card ↥(specialBlock Q xe (X ^ 2 + X + 1)) : ℤ) := by
      exact_mod_cast h73
    rw [card_specialBlock_phi hx hmem hKf, hm9] at h73'
    exact not_seventy_three_dvd_su_nine_two h73'
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
      exfalso
      have h36 : 2 ^ 36 ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
        have h1 : 2 ^ 36 ∣ Nat.card ↥((F.subgroupOf (orthDerived Q)).map (piOrth Q)) := by
          rw [hLc, ordD_four_eight_eq]
          exact Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _
        rw [Nat.card_congr eL.toEquiv] at h1
        have h2 := Subgroup.card_dvd_of_le hFle
        rw [hFW] at h2
        exact h1.trans (h2.trans (Subgroup.card_dvd_of_le hle))
      have h36' := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h36
      rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with hs0 | hs1 | hs2
      · have : Subsingleton (fixedSpace xe) := (Module.finrank_zero_iff (R := K)).mp (by omega)
        have h1 : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext (LinearEquiv.ext fun w =>
            Subsingleton.elim _ _)⟩, ⟨1⟩⟩
        rw [h1] at h36
        norm_num at h36
      · rw [factorization_two_card_orthogonalGroup hR (m := 0) (by omega) hKf] at h36'
        omega
      · rw [factorization_two_card_orthogonalGroup hR (m := 1) (by omega) hKf] at h36'
        rcases hf with rfl | rfl <;> omega
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
        rw [hLc, factorization_two_ordD_four_eight] at h1
        obtain ⟨rfl, rfl⟩ := eq_three_of_mul_succ hf h1.symm
        refine ⟨by rw [hKf]; norm_num, by omega, ?_⟩
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
        rw [hZ, he, hZ1, mul_one, hLF, he, hcardρ, hKf, ordD_four_eight_eq] at hLc
        rcases hf with rfl | rfl <;> norm_num at hLc

end Components

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end

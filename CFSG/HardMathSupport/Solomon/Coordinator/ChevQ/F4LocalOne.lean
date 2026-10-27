module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4InnerEx
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldEvenF4G2
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

namespace F4LocalOneAux

theorem oneBalanced_at_of_good {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hcen : Subgroup.center K = ⊥) {M : Type*} [Group M] (Θ : MulAut K →* M)
    (hΘ : ∀ α : MulAut K, Θ α = 1 ↔ α ∈ innerAut K)
    (hM : ∀ x : M, Nat.Coprime p (orderOf x) → x ^ 2 = 1) {s : K}
    (h1 : GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K)) = ⊥)
    (h2 : ∀ σ : MulAut K, σ ^ 2 = 1 → σ ∉ innerAut K → ∃ t : K, s * t = t * s ∧ σ t ≠ t)
    (H : Subgroup (MulAut K)) (hH : innerAut K ≤ H) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K))) = ⊥ := by
  have hψ : Function.Injective (MulAut.conj : K →* MulAut K) :=
    conj_injective_of_center_eq_bot hcen
  set A : Subgroup (MulAut K) := H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K))
    with hA
  set N := GLAPPrimeCoreOf p A with hN
  have hNA : N ≤ A := GLAPPrimeCoreOf_le A
  have hNinn : N ⊓ innerAut K = ⊥ := by
    set B : Subgroup (MulAut K) :=
      innerAut K ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K)) with hB
    have hBA : B ≤ A := inf_le_inf hH le_rfl
    have hOB : GLAPPrimeCoreOf p B = ⊥ := by
      have hmap := map_glaPPrimeCoreOf_of_injective p (MulAut.conj : K →* MulAut K) hψ
        (Subgroup.centralizer ({s} : Set K))
      have hc := map_inf_centralizer_of_injective (MulAut.conj : K →* MulAut K) hψ ⊤ s
      rw [top_inf_eq] at hc
      have hrange : (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) = innerAut K :=
        MonoidHom.range_eq_map _ |>.symm
      rw [hrange] at hc
      rw [h1, Subgroup.map_bot, hc] at hmap
      exact hmap.symm
    rw [eq_bot_iff, ← hOB]
    refine le_GLAPPrimeCoreOf_of_normal (fun y hy => ⟨hy.2, (hNA hy.1).2⟩) ?_ ?_
    · intro g hg y hy
      have hgA := hBA hg
      refine ⟨GLAPPrimeCoreOf_conj_mem g hgA y hy.1, ?_⟩
      exact (inner_normal K).conj_mem y hy.2 g
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_GLAPPrimeCoreOf hp A)
  rw [eq_bot_iff]
  intro σ hσ
  by_contra hσ1
  have hσ1' : σ ≠ 1 := by simpa using hσ1
  have hσinn : σ ∉ innerAut K := fun hi => hσ1 (by
    have : σ ∈ N ⊓ innerAut K := ⟨hσ, hi⟩
    rw [hNinn] at this
    exact this)
  have hσ2 : σ ^ 2 = 1 := by
    have hmem : σ ^ 2 ∈ N ⊓ innerAut K := by
      refine ⟨N.pow_mem hσ 2, (hΘ _).1 ?_⟩
      rw [map_pow]
      apply hM
      have h3 : orderOf (Θ σ) ∣ orderOf σ := orderOf_map_dvd Θ σ
      have h4 : orderOf σ ∣ Nat.card N := by
        have := orderOf_dvd_natCard (⟨σ, hσ⟩ : N)
        rwa [Subgroup.orderOf_mk] at this
      exact Nat.Coprime.coprime_dvd_right (h3.trans h4) (coprime_card_GLAPPrimeCoreOf hp A)
    rw [hNinn] at hmem
    exact hmem
  obtain ⟨t, hts, hσt⟩ := h2 σ hσ2 hσinn
  have ht : MulAut.conj t ∈ A := by
    refine Subgroup.mem_inf.2 ⟨hH ⟨t, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh, ← map_mul, ← map_mul, hts]
  have hcent : MulAut.conj t * σ * (MulAut.conj t)⁻¹ = σ := by
    have hmem : MulAut.conj t * σ * (MulAut.conj t)⁻¹ * σ⁻¹ ∈ N ⊓ innerAut K := by
      refine ⟨N.mul_mem (GLAPPrimeCoreOf_conj_mem _ ht σ hσ) (N.inv_mem hσ), (hΘ _).1 ?_⟩
      have hct : Θ (MulAut.conj t) = 1 := (hΘ _).2 ⟨t, rfl⟩
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hct]
      group
    rw [hNinn] at hmem
    have h1' : MulAut.conj t * σ * (MulAut.conj t)⁻¹ * σ⁻¹ = 1 := hmem
    exact mul_inv_eq_one.1 h1'
  have hc2 : σ * MulAut.conj t * σ⁻¹ = MulAut.conj t := by
    have h3 : MulAut.conj t * σ = σ * MulAut.conj t := by
      have := congrArg (fun y => y * MulAut.conj t) hcent
      simpa [mul_assoc] using this
    rw [← h3]
    group
  rw [mulAut_mul_conj_mul_inv] at hc2
  exact hσt (hψ hc2)

open CFSG.Blueprint CFSG.Blueprint.Chevalley in
@[expose] def F4EightOPrimeCore : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ 3 →
    OPrimeCoreTrivialAt 3 ↥(adjointGroup Tag.F4 K)

open CFSG.Blueprint CFSG.Blueprint.Chevalley in
@[expose] def F4EightNoOuterFixes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ 3 →
    NoOuterFixesCentralizer 3 ↥(adjointGroup Tag.F4 K)

theorem sq_eq_one_of_coprime_three (x : Multiplicative (ZMod (2 * 3)))
    (hx : Nat.Coprime 3 (orderOf x)) : x ^ 2 = 1 := by
  have h6 : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one ((by decide : ∀ y : Multiplicative (ZMod (2 * 3)),
    y ^ 6 = 1) x)
  have h2 : orderOf x ∣ 2 := by
    have h : orderOf x ∣ 3 * 2 := by simpa [mul_comm] using h6
    exact Nat.Coprime.dvd_of_dvd_mul_left hx.symm h
  exact orderOf_dvd_iff_pow_eq_one.1 h2

end F4LocalOneAux

section F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

namespace F4LocalOneAux

theorem fieldCoreAt_eight {x : MulAut ↥(adjointGroup Tag.F4 (GaloisField 2 3))} (hxp : orderOf x = 3)
    (hxo : x ∉ innerAut ↥(adjointGroup Tag.F4 (GaloisField 2 3))) :
    CFSG.HardMathSupport.Timmesfeld.CrossChar.FieldCoreAt 3 x := by
  have hKcard : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  haveI : CharP (GaloisField 2 3) CFSG.LieType.Ree.ReeTag.F4.prime :=
    inferInstanceAs (CharP (GaloisField 2 3) 2)
  have hdvd : ∀ σ : GaloisField 2 3 ≃+* GaloisField 2 3, orderOf σ = 3 →
      ¬ Nat.Coprime 3 (Nat.card (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag
        (fixSubfield σ))) := by
    intro σ hσ
    obtain ⟨-, hc⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
      (by norm_num : 1 ≤ 3) hKcard σ
    rw [hσ] at hc
    have h2 : Nat.card (fixSubfield σ) = 2 := by simpa using hc
    rw [← Nat.Prime.dvd_iff_not_coprime Nat.prime_three]
    show 3 ∣ Nat.card (adjointGroup Tag.F4 (fixSubfield σ))
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, h2]
    norm_num [CFSG.Open.ordF4]
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.fieldCoreAt_F4_even (f := 3) (by norm_num)
    (GaloisField 2 3) hKcard Nat.prime_three (by norm_num) hdvd hxp hxo

theorem isLocallyBalancedAbs_one_eight (hCore : F4EightOPrimeCore) (hOut : F4EightNoOuterFixes) :
    IsLocallyBalancedAbs 3 1 ↥(adjointGroup Tag.F4 (GaloisField 2 3)) := by
  classical
  have hKcard : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  haveI : CharP (GaloisField 2 3) CFSG.LieType.Ree.ReeTag.F4.prime :=
    inferInstanceAs (CharP (GaloisField 2 3) 2)
  have hcen : Subgroup.center ↥(adjointGroup Tag.F4 (GaloisField 2 3)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hψ : Function.Injective
      (MulAut.conj : ↥(adjointGroup Tag.F4 (GaloisField 2 3)) →*
        MulAut ↥(adjointGroup Tag.F4 (GaloisField 2 3))) :=
    conj_injective_of_center_eq_bot hcen
  obtain ⟨-, -, ⟨Θ, -, -, hΘker⟩, -⟩ :=
    even_F4_exact_automorphism_normal_form (f := 3) (by norm_num) (GaloisField 2 3) hKcard
  have hΘ : ∀ α : MulAut ↥(adjointGroup Tag.F4 (GaloisField 2 3)), Θ α = 1 ↔
      α ∈ innerAut ↥(adjointGroup Tag.F4 (GaloisField 2 3)) := by
    intro α
    have h : α ∈ Θ.ker ↔ α ∈ (MulAut.conj : ↥(adjointGroup Tag.F4 (GaloisField 2 3)) →*
        MulAut ↥(adjointGroup Tag.F4 (GaloisField 2 3))).range := by
      rw [hΘker]
      exact Iff.rfl
    exact h
  intro D hD hcard H hH hDH
  have hD1 : 1 < Nat.card D := by rw [hcard]; norm_num
  haveI : Finite D := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hD1
  obtain ⟨d, hd⟩ := exists_ne (1 : D)
  have hd1 : (d : MulAut ↥(adjointGroup Tag.F4 (GaloisField 2 3))) ≠ 1 := fun h => hd (Subtype.ext h)
  have hdp : (d : MulAut ↥(adjointGroup Tag.F4 (GaloisField 2 3))) ^ 3 = 1 := hD.2 d d.2
  have hord : orderOf (d : MulAut ↥(adjointGroup Tag.F4 (GaloisField 2 3))) = 3 :=
    orderOf_eq_prime hdp hd1
  by_cases hin : (d : MulAut ↥(adjointGroup Tag.F4 (GaloisField 2 3))) ∈
      innerAut ↥(adjointGroup Tag.F4 (GaloisField 2 3))
  · obtain ⟨s, hs⟩ := hin
    have hs3 : orderOf s = 3 := by
      have h1 := orderOf_injective _ hψ s
      rw [hs] at h1
      exact h1.symm.trans hord
    rw [eq_bot_iff]
    calc localDeltaIn 3 H D
        ≤ GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer
            ({(d : MulAut ↥(adjointGroup Tag.F4 (GaloisField 2 3)))} :
              Set (MulAut ↥(adjointGroup Tag.F4 (GaloisField 2 3))))) :=
          iInf₂_le_of_le (d : MulAut ↥(adjointGroup Tag.F4 (GaloisField 2 3))) d.2
            (iInf_le_of_le hd1 le_rfl)
      _ = ⊥ := by
          rw [← hs]
          exact oneBalanced_at_of_good Nat.prime_three hcen Θ hΘ sq_eq_one_of_coprime_three
            (hCore (GaloisField 2 3) hKcard s hs3)
            (fun σ hσ2 hσi => hOut (GaloisField 2 3) hKcard σ hσ2 hσi s hs3) H hH
      _ ≤ ⊥ := le_rfl
  · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.localDeltaIn_eq_bot_of_fieldCore Nat.prime_three
      hψ hH d.2 hd1 (fieldCoreAt_eight hord hin)

end F4LocalOneAux

theorem f4LocalOne_of_inputs (hCore : F4LocalOneAux.F4EightOPrimeCore)
    (hOut : F4LocalOneAux.F4EightNoOuterFixes) : Bal209F4Aux.F4LocalOne := by
  intro X _ _ K A hK hLie _ _
  classical
  obtain ⟨hZK, ⟨eK⟩⟩ := F4InnerExAux.center_bot_and_equiv hK.2.2 hLie
  have hbalK : IsLocallyBalancedAbs 3 1 ↥K :=
    IsLocallyBalancedAbs.of_mulEquiv eK (F4LocalOneAux.isLocallyBalancedAbs_one_eight hCore hOut)
  have hsimple : IsSimpleGroup ↥K :=
    (MulEquiv.isSimpleGroup_congr ((QuotientGroup.quotientMulEquivOfEq hZK).trans
      QuotientGroup.quotientBot)).1 hK.2.2.2
  have h3 : 3 ∣ Nat.card ↥K := by
    rw [Nat.card_congr eK.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
      GaloisField.card 2 3 (by norm_num)]
    norm_num [CFSG.Open.ordF4]
  have hbot : GLAPPrimeCore 3 ↥K = ⊥ := by
    haveI := GLAPPrimeCore.normal 3 ↥K
    rcases hsimple.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥K) with h | h
    · exact h
    · exfalso
      have hcop := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore
        Nat.prime_three ↥K
      rw [h, Subgroup.card_top] at hcop
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)
  have e' : barOf 3 K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact (IsLocallyBalancedAbs.of_mulEquiv e' hbalK).isLocallyBalanced _

end F4

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

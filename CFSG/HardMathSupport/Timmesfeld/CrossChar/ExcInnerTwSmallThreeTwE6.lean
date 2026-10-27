module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwSmallThree
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTwE6Class

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.LieType.SeitzGeneration
open scoped Pointwise

section Perfect


theorem model_le_Γ_of_fix_le_commutator {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    (h : D.fix ≤ ⁅D.fix, D.fix⁆) : D.model ≤ D.Γ := by
  rw [LangDatum.Γ, LangDescent.model_eq D, ← Subgroup.map_commutator]
  exact Subgroup.map_mono h


theorem twistedFixedGroup_le_commutator_of_eq_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hq3 : ℓ ^ f = 3) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    twistedFixedGroup TwistTag.E6 Ω Fr ≤
      ⁅twistedFixedGroup TwistTag.E6 Ω Fr, twistedFixedGroup TwistTag.E6 Ω Fr⁆ := by
  classical
  obtain ⟨-, hprod, hder, ⟨k, hk⟩, hT, -, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ hσ Ω Fr hFr
  set R := twistedFixedGroup TwistTag.E6 Ω Fr with hR
  set C := (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K Ω)) with hC
  set T := graphFixedTorus TwistTag.E6 Ω Fr with hTdef
  have hCR : C ≤ R := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hTR : T ≤ R := fun x hx => (Subgroup.mem_inf.1 hx).2
  have hnormal : (C.subgroupOf R).Normal := by
    have e : C.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
      have h1 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup R), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  have hsup : T.subgroupOf R ⊔ C.subgroupOf R = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ (T : Set (ModGL TwistTag.E6.tag Ω)) * (C : Set (ModGL TwistTag.E6.tag Ω)) := by
      rw [← hprod]
      exact hx
    obtain ⟨t, ht, c, hc, rfl⟩ := hx'
    have e : (⟨t * c, hx⟩ : R) = ⟨t, hTR ht⟩ * ⟨c, hCR hc⟩ := rfl
    rw [e]
    exact Subgroup.mul_mem_sup ht hc
  have hdvd : 3 ^ k ∣ Nat.card T := by
    rw [← hk, ← Subgroup.relIndex_top_right, ← hsup, Subgroup.relIndex_sup_right]
    exact (Subgroup.relIndex_dvd_card (H := C.subgroupOf R) (K := T.subgroupOf R)).trans
      (dvd_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv))
  rw [hT, hq3] at hdvd
  have hk0 : k = 0 := by
    by_contra h0
    have h3 := (dvd_pow_self 3 h0).trans hdvd
    norm_num at h3
  rw [hk0, pow_zero] at hk
  rw [hder]
  exact Subgroup.relIndex_eq_one.1 hk

end Perfect

section Sign


theorem rho_ne_of_rel6 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (h6 : ∀ δ, IsRoot τ δ → S.ρ (S.ρ δ) = S.ρ δ - δ)
    (γ : Fin τ.rank → ℤ) (hγ : IsRoot τ γ) : S.ρ γ ≠ γ ∧ S.ρ γ ≠ -γ := by
  have hww := h6 γ hγ
  refine ⟨fun h1 => hγ.ne_zero ?_, fun h1 => hγ.ne_zero ?_⟩
  · rw [h1, h1, sub_self] at hww
    exact hww
  · rw [h1, S.frob.neg_eq, h1, neg_neg] at hww
    have h3 : (3 : ℤ) • γ = 0 := by
      have : (3 : ℤ) • γ = γ - (-γ - γ) := by module
      rw [this, ← hww, sub_self]
    exact (smul_eq_zero.1 h3).resolve_left (by norm_num)

end Sign

section Rigid

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}


theorem cosetCentralizerEmpty_three_of_pbig (hAK3 : AnyKindCommuteThreeFull) {K : Type}
    [Field K] [Finite K] [Algebra K L] [Algebra.IsAlgebraic K L]
    (S : LangSetup TwistTag.E6.tag L p) (hq : S.D.q = 3) (hP : BigAnyPBig S)
    (hA1 : ∀ γ, IsRoot TwistTag.E6.tag γ → S.ρ γ ≠ γ ∧ S.ρ γ ≠ -γ)
    {D₁ : Subgroup (ModGL TwistTag.E6.tag L)} (hD₁E : D₁ ≤ S.E) (hc : Nat.card D₁ = p ^ 2) :
    CosetCentralizerEmpty S D₁ (diagramMap TwistTag.E6 L) := by
  intro w hw hcomm
  exact not_forall_commute_mul_diagramMap_E6 (K := K) hw
    (commute_adjointGroup_three_of_pbig hAK3 S (Or.inr (Or.inl rfl)) hq hP hA1 hD₁E hc
      fun x hx => hcomm x (Or.inl hx))

theorem setupRigid_twistedE6_three_of_pbig (hAK3 : AnyKindCommuteThreeFull) {K : Type}
    [Field K] [Finite K] [Algebra K L] [Algebra.IsAlgebraic K L]
    (S : LangSetup TwistTag.E6.tag L p) (hq : S.D.q = 3)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 L Fr)
    (hAlg : S.IsAlgebraic) (hP : BigAnyPBig S)
    (hA1 : ∀ γ, IsRoot TwistTag.E6.tag γ → S.ρ γ ≠ γ ∧ S.ρ γ ≠ -γ) : SetupRigid S :=
  setupRigid_twistedE6 S hΦ hAlg
    (fun D₁ _ _ => noFrobeniusInner_of_q_prime S (by rw [hq]; norm_num) D₁)
    (fun D₁ hD₁ hc => centralizerTrivial_three_of_pbig hAK3 S (Or.inr (Or.inl rfl)) hq hP hA1 hD₁
      hc)
    (fun D₁ hD₁ hc => cosetCentralizerEmpty_three_of_pbig hAK3 (K := K) S hq hP hA1 hD₁ hc)

end Rigid

section Row


theorem innerPlaneBalance_twistedE6_six_three (hcp : LangComponentPieces)
    (hAK3 : AnyKindCommuteThreeFull) :
    ∀ (q : TauCeti.PrimePower) (hv : (excIndex .twistedE6 q).Valid), q.card = 3 →
      InnerPlaneBalance 7 (CatT ⟨excIndex .twistedE6 q, hv⟩) := by
  intro q hv hq3
  obtain ⟨K, _, σ, hK, hσ, ⟨eq⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hq3' : q.p ^ q.exponent = 3 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq3
  have hpK : ¬ 7 ∣ q.p ^ q.exponent := by
    rw [hq3']
    norm_num
  have he' : orderOf (((q.p ^ q.exponent : ℕ)) : ZMod 7) = 6 := by
    rw [hq3']
    exact orderOf_three_zmod_seven
  obtain ⟨Fr, hFr, g0, hg0C, hg0, S, hSD, hsyl, ⟨ε⟩⟩ :=
    springer_exists_langSetup_twistedE6_six frobeniusOnRoots_proved q.prime_p q.exponent_pos K
      hK σ hσ (by norm_num) le_rfl hpK he'
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have hq : S.D.q = q.p ^ q.exponent := by rw [hSD]; rfl
  have hΦ' : S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr := by rw [hSD]; rfl
  have hΦ : ∃ Fr' : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr' c = c ^ S.D.q) ∧
      S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr' :=
    ⟨Fr, fun c => by rw [hq]; exact hFr c, hΦ'⟩
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 2 (by rw [hK, hq])
  have hfix : S.D.fix = twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr := by
    ext x
    rw [LangDatum.mem_fix, hΦ']
    rfl
  have hMΓ : S.D.model ≤ S.Γ := model_le_Γ_of_fix_le_commutator S.D (by
    rw [hfix]
    exact twistedFixedGroup_le_commutator_of_eq_three q.prime_p q.exponent_pos hq3' K hK
      σ.toRingHom hσ _ Fr hFr)
  have hcl : S.IsTwE6SixClass := ⟨Fr, fun c => by rw [hq]; exact hFr c, hΦ', by rw [hSD]; rfl⟩
  have hP : BigAnyPBig S :=
    S.bigAnyPBig_of_twE6SixClass hcl le_rfl (LangSetup.HexGroupInGamma.of_model_le S hMΓ)
  have hrig := setupRigid_twistedE6_three_of_pbig hAK3 (K := K) S (hq.trans hq3') hΦ hAlg hP
    (rho_ne_of_rel6 S (S.hexStep_of_twE6SixClass hcl).rel6)
  have hC : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)
  have hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ) :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.conj_injective_of_mulEquiv ε hC
  exact InnerPlaneBalance.of_mulEquiv (eq.trans ε)
    (innerPlaneBalance_of_langSetup_rigid S hsyl hrig hcp hinj)

end Row

end CFSG.HardMathSupport.Timmesfeld.CrossChar

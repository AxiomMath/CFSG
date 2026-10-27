module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4ThreeSixAux.Frame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodWiringTw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTwHex
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwistedLineFix
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwSmallThree
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyRhoHex

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


@[expose] def triD4SixMat : List (List ℤ) :=
  [[0, 0, 1, -1], [0, 1, 0, -1], [-1, 1, 1, -1], [0, 1, 0, 0]]

theorem toMat_triD4SixMat : toMat Tag.D4.rank triD4SixMat = d4SixM := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem triD4SixMat_sq : toMat Tag.D4.rank triD4SixMat * toMat Tag.D4.rank triD4SixMat =
    toMat Tag.D4.rank triD4SixMat - 1 := by decide +kernel

section Six

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem six_rel (S : LangSetup Tag.D4 L p) (hρ : RhoIs S triD4SixMat) {δ : Fin Tag.D4.rank → ℤ}
    (hδ : IsRoot Tag.D4 δ) : S.ρ (S.ρ δ) = S.ρ δ - δ := by
  have hδ' : IsRoot Tag.D4 (S.ρ δ) := (S.frob.isRoot_iff δ).2 hδ
  rw [hρ _ hδ', hρ _ hδ, Matrix.mulVec_mulVec, triD4SixMat_sq, Matrix.sub_mulVec,
    Matrix.one_mulVec]

theorem iform_rho_six (S : LangSetup Tag.D4 L p) (hρ : RhoIs S triD4SixMat)
    {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) : iform γ (S.ρ γ) = 1 := by
  have hsl : SimplyLacedTag Tag.D4 := Or.inl rfl
  have h1 := S.frob.iform_eq γ (S.ρ γ)
  rw [six_rel S hρ hγ, iform_sub_right,
    iform_self_eq_two_of_simplyLaced hsl ((S.frob.isRoot_iff γ).2 hγ),
    iform_comm (S.ρ γ) γ] at h1
  omega

theorem hexStep_of_rhoIs_D4 (S : LangSetup TwistTag.D4.tag L p) (hρ : RhoIs S triD4SixMat)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr) :
    S.HexStep := by
  obtain ⟨Fr, hFr, hΦ'⟩ := hΦ
  obtain ⟨v, hn⟩ := S.D.n_weyl
  exact
    { hel := fun x hx u => by
        rw [twist_hel S hFr hΦ' hn x u, ← twist_rho S hFr hΦ' hn hx]
      nsl := fun β hβ => by
        obtain ⟨s, hs⟩ := twist_nsl S hFr hΦ' hn hβ
        exact ⟨s, fun c => by rw [hs c, twist_rho S hFr hΦ' hn hβ]⟩
      rel6 := fun δ hδ => six_rel S hρ hδ }

theorem hexGroupInGamma_D4 (S : LangSetup Tag.D4 L p) (hρ : RhoIs S triD4SixMat)
    (hAlg : S.IsAlgebraic) (hq3 : 3 ≤ S.D.q) : S.HexGroupInGamma := by
  intro γ hγ
  have hργ : IsRoot Tag.D4 (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have hform : iform γ (-S.ρ γ) = -1 := by
    rw [iform_neg_right_tri, iform_rho_six S hρ hγ]
  obtain ⟨ρ', σ, hfr, hinj, h01, h12, -⟩ :=
    exists_d4_signedFrame (L := L) hγ (IsRoot.neg hργ) hform
  exact twistedLine_hexGroup_le_of_frame S hAlg hq3 (fun δ hδ => six_rel S hρ hδ) hγ hfr hinj
    h01 h12

theorem bigAnyPBig_D4_six (S : LangSetup TwistTag.D4.tag L p) (hρ : RhoIs S triD4SixMat)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) (hp7 : 7 ≤ p) (hq3 : 3 ≤ S.D.q) : BigAnyPBig S :=
  bigAnyPBig_of_hexStep S (hexStep_of_rhoIs_D4 S hρ hΦ) (Or.inl rfl) hp7
    (hexGroupInGamma_D4 S hρ hAlg hq3)

end Six

section Rigid

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem rho_ne_of_six (S : LangSetup Tag.D4 L p) (hρ : RhoIs S triD4SixMat)
    (γ : Fin Tag.D4.rank → ℤ) (hγ : IsRoot Tag.D4 γ) : S.ρ γ ≠ γ ∧ S.ρ γ ≠ -γ := by
  have hww := six_rel S hρ hγ
  refine ⟨fun h1 => hγ.ne_zero ?_, fun h1 => hγ.ne_zero ?_⟩
  · rw [h1, h1, sub_self] at hww
    exact hww
  · rw [h1, S.frob.neg_eq, h1, neg_neg] at hww
    have h3 : (3 : ℤ) • γ = 0 := by
      have : (3 : ℤ) • γ = γ - (-γ - γ) := by module
      rw [this, ← hww, sub_self]
    exact (smul_eq_zero.1 h3).resolve_left (by norm_num)

theorem orderOf_two_zmod_seven_aux : orderOf ((2 : ℕ) : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_ne_six {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    orderOf ((2 : ℕ) : ZMod p) ≠ 6 := by
  intro he
  haveI : Fact p.Prime := ⟨hp⟩
  have h6 : ((2 : ℕ) : ZMod p) ^ 6 = 1 := by
    rw [← he]
    exact pow_orderOf_eq_one _
  have h63 : ((63 : ℕ) : ZMod p) = 0 := by
    push_cast at h6 ⊢
    linear_combination h6
  have hd : p ∣ 63 := (ZMod.natCast_eq_zero_iff 63 p).1 h63
  have hd' : p ∣ 9 * 7 := by simpa using hd
  have hp7' : p = 7 := by
    rcases (Nat.Prime.dvd_mul hp).1 hd' with h | h
    · have h3 : p ∣ 3 := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by simpa using h)
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
  subst hp7'
  rw [orderOf_two_zmod_seven_aux] at he
  omega

theorem setupRigid_triD4_six (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius)
    (hAK3 : AnyKindCommuteThreeFull) (S : LangSetup TwistTag.D4.tag L p) (hp7 : 7 ≤ p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 6) (hρ : RhoIs S triD4SixMat) :
    SetupRigid S := by
  have hsl : SimplyLacedTag TwistTag.D4.tag := Or.inl rfl
  have hq2 : S.D.q ≠ 2 := fun h => orderOf_two_ne_six S.hp hp7 (by rw [← h]; exact he)
  have hq3 : 3 ≤ S.D.q := by
    have := S.hqpow.1.one_lt
    omega
  have hP := bigAnyPBig_D4_six S hρ hΦ hAlg hp7 hq3
  by_cases hq4 : 4 ≤ S.D.q
  · refine setupRigid_triD4 S hΦ hAlg
      (fun D₁ hD₁ hc => hAF _ L p S (by decide) (Or.inr hsl) D₁ hD₁
        (hasBigAnyComponent_of_pbig S hq4 hP hD₁ hc))
      (fun D₁ hD₁ hc => centralizerTrivial_of_bigAnyGenerate hAK S (by decide) hq3 hD₁
        (bigAnyComponentsGenerate_of_pbig S hsl hq4 hP hD₁ hc)) ?_
    intro D₁ hD₁ hc c hc' a ha0 ha3 hcomm
    refine noTriCosetCentralizes_D4 c hc' a ha0 ha3 ?_
    exact commute_adjointGroup_of_bigAnyGenerate hAK S (by decide) hq3 hD₁
      (bigAnyComponentsGenerate_of_pbig S hsl hq4 hP hD₁ hc) (fun x hx => hcomm x (Or.inl hx))
  · have hq : S.D.q = 3 := by omega
    have hA1 := rho_ne_of_six S hρ
    refine setupRigid_triD4 S hΦ hAlg
      (fun D₁ _ _ => noFrobeniusInner_of_q_prime S (by rw [hq]; norm_num) D₁)
      (fun D₁ hD₁ hc => centralizerTrivial_three_of_pbig hAK3 S hsl hq hP hA1 hD₁ hc) ?_
    intro D₁ hD₁ hc c hc' a ha0 ha3 hcomm
    refine noTriCosetCentralizes_D4 c hc' a ha0 ha3 ?_
    exact commute_adjointGroup_three_of_pbig hAK3 S hsl hq hP hA1 hD₁ hc
      (fun x hx => hcomm x (Or.inl hx))

end Rigid

section Wiring

open Polynomial

theorem langTorusAtAlgW_trialityD4_6 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgW .trialityD4 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 6)
      (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
        (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4SixMat S) :=
  langTorusAtAlgW_trialityD4_of_model triD4SixMat
    fun ℓ f hℓ hf K _ hK σ hσ p hp (h7 : 7 ≤ p) hpq hC he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hΦ, hsyl, hequiv⟩ :=
      exists_lang_triD4_of_class_alg_rho hF hℓ hf K hK σ hσ hp h7 hpq hC he (by decide)
      ((coxeterSystem TwistTag.D4.tag).wordProd d4SixWord) d4Six_hw (by norm_num)
      d4Six_pow (1) d4Six_det (by rw [eval_one]; exact not_dvd_one_int hp)
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hΦ, hsyl, hequiv⟩
    rw [hρ γ hγ, toMat_triD4SixMat]
    rfl

theorem langRigidityForAlgW_trialityD4_6 (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius)
    (hAK3 : AnyKindCommuteThreeFull) :
    LangRigidityForAlgW .trialityD4 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 6)
      (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
        (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4SixMat S) :=
  fun _ _ _ L _ _ S hR hq hAlg hW _ =>
    setupRigid_triD4_six hAK hAF hAK3 S hR.1 hW.2 hAlg (by rw [hq]; exact hR.2) hW.1

theorem innerPlaneBalanceAtP_trialityD4_6 (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius)
    (hAK3 : AnyKindCommuteThreeFull) (hF : FrobeniusOnRoots) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .trialityD4 q).Valid),
      Subgroup.center (CatT ⟨excIndex .trialityD4 q, hv⟩) = ⊥) :
    InnerPlaneBalanceAtP .trialityD4 6 fun p => 7 ≤ p :=
  innerPlaneBalanceAtP_of_lang_rigid_algW (k := .trialityD4) trivial
    (langTorusAtAlgW_trialityD4_6 hF) (langRigidityForAlgW_trialityD4_6 hAK hAF hAK3) hcp hZ

end Wiring

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

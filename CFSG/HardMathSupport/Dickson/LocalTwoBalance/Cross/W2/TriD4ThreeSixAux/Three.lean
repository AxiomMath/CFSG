module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4ThreeSixAux.SplitGood
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodWiringTw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTri
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4ThreeSixAux.Frame

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


@[expose] def triD4ThreeMat : List (List ℤ) :=
  [[-1, 1, 0, 0], [-1, 0, 0, 0], [-1, 1, 0, -1], [-1, 0, 1, -1]]

theorem toMat_triD4ThreeMat : toMat Tag.D4.rank triD4ThreeMat = d4ThreeM := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem triD4ThreeMat_sq : toMat Tag.D4.rank triD4ThreeMat * toMat Tag.D4.rank triD4ThreeMat =
    -toMat Tag.D4.rank triD4ThreeMat - 1 := by decide +kernel

@[expose] def D4TwoPoly : Prop :=
  ∀ (L : Type) [Field L] [CharP L 2] (Ψ : Set (Fin Tag.D4.rank → ℤ)),
    (∀ γ ∈ Ψ, IsRoot Tag.D4 γ) → (∀ γ ∈ Ψ, -γ ∈ Ψ) → (∀ α ∈ Ψ, ∃ δ ∈ Ψ, iform α δ = 1) →
    ∀ {zu z : ModGL Tag.D4 L},
      (∀ g : ModGL Tag.D4 L, g ∈ rootSpan Tag.D4 L Ψ ↔ zu * g * zu⁻¹ ∈ rootSpan Tag.D4 L Ψ) →
      (∀ γ ∈ Ψ, z * (zu * pinnedX Tag.D4 L γ 1 * zu⁻¹) = (zu * pinnedX Tag.D4 L γ 1 * zu⁻¹) * z) →
      ∀ g ∈ rootSpan Tag.D4 L Ψ, Commute z g

section Three

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem three_rel (S : LangSetup Tag.D4 L p) (hρ : RhoIs S triD4ThreeMat) {δ : Fin Tag.D4.rank → ℤ}
    (hδ : IsRoot Tag.D4 δ) : S.ρ (S.ρ δ) = -S.ρ δ - δ := by
  have hδ' : IsRoot Tag.D4 (S.ρ δ) := (S.frob.isRoot_iff δ).2 hδ
  rw [hρ _ hδ', hρ _ hδ, Matrix.mulVec_mulVec, triD4ThreeMat_sq, Matrix.sub_mulVec,
    Matrix.neg_mulVec, Matrix.one_mulVec]

theorem iform_rho_three (S : LangSetup Tag.D4 L p) (hρ : RhoIs S triD4ThreeMat)
    {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) : iform γ (S.ρ γ) = -1 := by
  have hsl : SimplyLacedTag Tag.D4 := Or.inl rfl
  have h1 := S.frob.iform_eq γ (S.ρ γ)
  rw [three_rel S hρ hγ, iform_sub_right, iform_neg_right_tri,
    iform_self_eq_two_of_simplyLaced hsl ((S.frob.isRoot_iff γ).2 hγ),
    iform_comm (S.ρ γ) γ] at h1
  omega

theorem dvd_q2_add_q_add_one_of_orderOf_three {p q : ℕ} (hp : p.Prime)
    (he : orderOf ((q : ℕ) : ZMod p) = 3) : p ∣ q ^ 2 + q + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3 : ((q : ℕ) : ZMod p) ^ 3 = 1 := by
    rw [← he]
    exact pow_orderOf_eq_one _
  have h1 : ((q : ℕ) : ZMod p) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at he
    omega
  have hz : (((q : ℕ) : ZMod p) - 1) * (((q : ℕ) : ZMod p) ^ 2 + ((q : ℕ) : ZMod p) + 1) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd (sub_eq_zero.1 h) h1
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact h

theorem frame_adj {τ : Tag} (hsl : SimplyLacedTag τ) {ρ' : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hfr : IsSLFrame ρ' σ)
    (h : iform (σ 0 1) (σ 1 2) = -1) : ∀ α ∈ frameRoots σ, ∃ δ ∈ frameRoots σ, iform α δ = 1 := by
  have r01 := hfr.isRoot 0 1 (by decide)
  have s01 := iform_self_eq_two_of_simplyLaced hsl r01
  have h02 : σ 0 2 = σ 0 1 + σ 1 2 := (hfr.add 0 1 2).symm
  have h10 : σ 1 0 = -σ 0 1 := hfr.neg 0 1
  have h21 : σ 2 1 = -σ 1 2 := hfr.neg 1 2
  have h20 : σ 2 0 = -σ 0 2 := hfr.neg 0 2
  have h' : iform (σ 1 2) (σ 0 1) = -1 := by rw [iform_comm]; exact h
  rintro α ⟨i, j, hij, rfl⟩
  fin_cases i <;> fin_cases j
  all_goals first | exact absurd rfl hij | skip
  · refine ⟨σ 2 1, ⟨2, 1, by decide, rfl⟩, ?_⟩
    show iform (σ 0 1) (σ 2 1) = 1
    rw [h21, iform_neg_right_tri, h]
    norm_num
  · refine ⟨σ 0 1, ⟨0, 1, by decide, rfl⟩, ?_⟩
    show iform (σ 0 2) (σ 0 1) = 1
    rw [h02, iform_add_left, s01, h']
    norm_num
  · refine ⟨σ 1 2, ⟨1, 2, by decide, rfl⟩, ?_⟩
    show iform (σ 1 0) (σ 1 2) = 1
    rw [h10, iform_neg_left', h]
    norm_num
  · refine ⟨σ 1 0, ⟨1, 0, by decide, rfl⟩, ?_⟩
    show iform (σ 1 2) (σ 1 0) = 1
    rw [h10, iform_neg_right_tri, h']
    norm_num
  · refine ⟨σ 1 0, ⟨1, 0, by decide, rfl⟩, ?_⟩
    show iform (σ 2 0) (σ 1 0) = 1
    rw [h20, h10, iform_neg_left', iform_neg_right_tri, neg_neg, h02, iform_add_left, s01, h']
    norm_num
  · refine ⟨σ 0 1, ⟨0, 1, by decide, rfl⟩, ?_⟩
    show iform (σ 2 1) (σ 0 1) = 1
    rw [h21, iform_neg_left', h']
    norm_num

theorem isGoodRoot_triD4_three (S : LangSetup Tag.D4 L p) (hp7 : 7 ≤ p) (hAlg : S.IsAlgebraic)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = 3) (hρ : RhoIs S triD4ThreeMat) (h2 : D4TwoPoly)
    {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) : IsGoodRoot S γ := by
  have hsl : SimplyLacedTag Tag.D4 := Or.inl rfl
  have hργ : IsRoot Tag.D4 (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have hform := iform_rho_three S hρ hγ
  obtain ⟨ρ', σ, hfr, hinj, h01, h12, hsign⟩ := exists_d4_signedFrame (L := L) hγ hργ hform
  have hrel : ∀ δ, IsRoot Tag.D4 δ → S.ρ (S.ρ δ) = -S.ρ δ - δ := fun δ hδ => three_rel S hρ hδ
  obtain ⟨hπ, horb⟩ := tri_shape S hrel hγ hfr h01 h12
  have hpq : p ∣ S.D.q ^ 2 + S.D.q + 1 := dvd_q2_add_q_add_one_of_orderOf_three S.hp he
  have hadj := frame_adj hsl hfr (by rw [h01, h12]; exact hform)
  rw [← h01]
  refine isGoodRoot_of_splitFrame S (by decide) hsl hAlg (by omega) hpq hfr hinj hsign hπ
    (by rwa [h01]) ?_
  intro hq2 zu z hzu hz
  have h2L : (2 : L) = 0 := by
    have h := S.hqpow.2
    rw [hq2] at h
    exact_mod_cast h
  haveI : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2L)
  refine h2 L (frameRoots σ) hfr.frameRoots_isRoot ?_ hadj ?_ hz
  · rintro _ ⟨i, j, hij, rfl⟩
    exact ⟨j, i, hij.symm, (hfr.neg i j).symm⟩
  · intro g
    constructor
    · intro hg
      exact mul_mem (mul_mem hzu hg) (inv_mem hzu)
    · intro hg
      have := mul_mem (mul_mem (inv_mem hzu) hg) hzu
      simpa [mul_assoc] using this

end Three

section Rigid

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem setupRigid_triD4_three (S : LangSetup TwistTag.D4.tag L p) (hp7 : 7 ≤ p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 3) (hρ : RhoIs S triD4ThreeMat)
    (h2 : D4TwoPoly) : SetupRigid S :=
  setupRigid_triD4_of_goodRoots S hΦ hAlg
    (fun γ hγ => ReflClosure.base (isGoodRoot_triD4_three S hp7 hAlg he hρ h2 hγ))
    noTriCosetCentralizes_D4

end Rigid


section Wiring

open Polynomial

theorem langTorusAtAlgW_trialityD4_3 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgW .trialityD4 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 3)
      (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
        (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4ThreeMat S) :=
  langTorusAtAlgW_trialityD4_of_model triD4ThreeMat
    fun ℓ f hℓ hf K _ hK σ hσ p hp (h7 : 7 ≤ p) hpq hC he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hΦ, hsyl, hequiv⟩ :=
      exists_lang_triD4_of_class_alg_rho hF hℓ hf K hK σ hσ hp h7 hpq hC he (by decide)
      ((coxeterSystem TwistTag.D4.tag).wordProd d4ThreeWord) d4Three_hw (by norm_num)
      d4Three_pow (1) d4Three_det (by rw [eval_one]; exact not_dvd_one_int hp)
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hΦ, hsyl, hequiv⟩
    rw [hρ γ hγ, toMat_triD4ThreeMat]
    rfl

theorem langRigidityForAlgW_trialityD4_3 (h2 : D4TwoPoly) :
    LangRigidityForAlgW .trialityD4 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 3)
      (fun {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
        (S : LangSetup (excTag .trialityD4) L p) => TwStructD4 triD4ThreeMat S) :=
  fun _ _ _ L _ _ S hR hq hAlg hW _ =>
    setupRigid_triD4_three S hR.1 hW.2 hAlg (by rw [hq]; exact hR.2) hW.1 h2

theorem innerPlaneBalanceAtP_trialityD4_3 (h2 : D4TwoPoly) (hF : FrobeniusOnRoots)
    (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .trialityD4 q).Valid),
      Subgroup.center (CatT ⟨excIndex .trialityD4 q, hv⟩) = ⊥) :
    InnerPlaneBalanceAtP .trialityD4 3 fun p => 7 ≤ p :=
  innerPlaneBalanceAtP_of_lang_rigid_algW (k := .trialityD4) trivial
    (langTorusAtAlgW_trialityD4_3 hF) (langRigidityForAlgW_trialityD4_3 h2) hcp hZ

end Wiring

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

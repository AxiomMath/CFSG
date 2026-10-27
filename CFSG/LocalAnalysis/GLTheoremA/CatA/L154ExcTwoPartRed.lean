module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158FgExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def CompTwoPart3D4 (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x y : Ω) (J : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore 3 ↥S = ⊥ →
    IsChevSimple 2 (PSimple 3 S) → catalogIs (PSimple 3 S) Q →
    x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x → x ∉ Subgroup.zpowers y → y ∉ Subgroup.zpowers x →
    InnDiagOn 3 (Subgroup.zpowers x) S → FieldOn 3 y S →
    GLAPComponent 3 (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J →
    y ∈ Subgroup.normalizer (J : Set Ω) →
    catalogIs (PSimple 3 J) isD4any → NonInnDiag 3 y J → ¬ FieldOn 3 y J →
    centCard2 3 J y ^ 3 = card2 3 J

theorem compTwoPart3D4_mono {Q Q' : TauCeti.CFSGIndex → Prop} (hsub : ∀ i, Q i → Q' i)
    (h : CompTwoPart3D4 Q') : CompTwoPart3D4 Q := by
  intro Ω _ _ S x y J hSn hqS hSp hSc hQ
  exact h Ω S x y J hSn hqS hSp hSc (catalogIs_imp hsub hQ)

theorem compTwoPart3D4_or {Q₁ Q₂ : TauCeti.CFSGIndex → Prop} (h₁ : CompTwoPart3D4 Q₁)
    (h₂ : CompTwoPart3D4 Q₂) : CompTwoPart3D4 (fun i => Q₁ i ∨ Q₂ i) := by
  intro Ω _ _ S x y J hSn hqS hSp hSc hQ
  obtain ⟨i, hi, e⟩ := hQ
  rcases hi with h | h
  · exact h₁ Ω S x y J hSn hqS hSp hSc ⟨i, h, e⟩
  · exact h₂ Ω S x y J hSn hqS hSp hSc ⟨i, h, e⟩

theorem l154_eq_of_centMod {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {x : Ω}
    {J : Subgroup Ω} (hqS : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hcm : CentMod p S x) (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J) :
    J = S := by
  have hcore : GLAPPrimeCoreOf p S = ⊥ := by
    unfold GLAPPrimeCoreOf
    unfold GLAPPrimeCore at hSp
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).2 hSp
  have hcen : S ≤ Subgroup.centralizer ({x} : Set Ω) := by
    intro s hs
    have h1 := (mem_centModSubgroup.1 (centMod_iff.1 hcm)).2 s hs
    rw [hcore, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subgroup.mem_centralizer_singleton_iff.2 h1
  have hJS : GLAPComponent p S J := by rwa [inf_eq_left.2 hcen] at hJ
  exact l154_eq_of_subnormal_quasisimple hJS.2.1 hqS (glaPComponent_perfect hJS)
    (CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hJS)

theorem l154_exists_d4any {X : Type} [Group X] (h : catalogIs X isD4any) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p = 2 ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | D m q =>
      rcases m with _ | _ | _ | _ | _ | m
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · exact ⟨q, hv, hi, ⟨e⟩⟩
      · exact hi.elim
    | E6 q => exact hi.elim
    | E7 q => exact hi.elim
    | E8 q => exact hi.elim
    | F4 q => exact hi.elim
    | G2 q => exact hi.elim
    | twistedE6 q => exact hi.elim
    | trialityD4 q => exact hi.elim
    | reeF4 m => exact hi.elim
    | suzuki m => exact hi.elim
    | tits => exact hi.elim
    | A r q => exact hi.elim
    | twistedA r q => exact hi.elim
    | B r q => exact hi.elim
    | C r q => exact hi.elim
    | twistedD r q => exact hi.elim
    | reeG2 m => exact hi.elim

theorem l154_padicVal_orderD_four {q : TauCeti.PrimePower} (hq : q.p = 2) :
    padicValNat 2 (orderD 4 q.card) = q.exponent * 12 := by
  have hc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
  rw [hc, ← Nat.factorization_def _ Nat.prime_two]
  exact CFSG.SeitzReduction.OmegaPilot.factorization_two_ordD q.exponent_pos (by norm_num)

section Small


theorem compTwoPart3D4_tits : CompTwoPart3D4 l154ExcTits := by
  intro Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy _ _ hInn hF hJ hJy _ _ _
  exact (l154_false_of_odd_inner Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hqS hSp) hSc hF.1 hyp hF
    (l154_oddInner_of_tits hQ)).elim

theorem compTwoPart3D4_suz : CompTwoPart3D4 l154ExcSuz := by
  intro Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy _ _ hInn hF hJ hJy _ _ hnF
  by_cases hcm : CentMod 3 S x
  · exact absurd (by rw [l154_eq_of_centMod hqS hSp hcm hJ]; exact hF) hnF
  · exact (l154_false_of_suzuki Nat.prime_three (by norm_num)
      (CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hqS hSp) hQ hxp
      (hInn.1 (Subgroup.mem_zpowers x)) hcm hInn hJ).elim

theorem compTwoPart3D4_two : CompTwoPart3D4 l154ExcTwo := by
  intro Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy _ _ hInn hF hJ hJy _ _ _
  exact (l154_false_of_fieldOn_exponent_one Nat.prime_three (by norm_num) hF
    (l154_labels_two hQ)).elim

theorem compTwoPart3D4_triD4 : CompTwoPart3D4 l154ExcTriD4 := by
  intro Ω _ _ S x y J hSn hqS hSp hSc hQ hxp hyp hxy _ _ hInn hF hJ hJy _ _ _
  obtain ⟨K, _, _, e, j, k, σ, θ, φx, φy, h, T, -, -, hjp, -⟩ :=
    excTriD4_marking_data Nat.prime_three (by norm_num) hQ hxp hyp hxy hInn hF
  omega

theorem compTwoPart3D4_ree : CompTwoPart3D4 l154ExcRee := by
  intro Ω _ _ S x y J hSn hqS hSp hc hQ hxp hyp hxy _ _ hInn hF hJ hJy hD4 _ hnF
  by_cases hcm : CentMod 3 S x
  · exact absurd (by rw [l154_eq_of_centMod hqS hSp hcm hJ]; exact hF) hnF
  exfalso
  obtain ⟨a, K, _, _, _, θ, s, φ, ha, hK, hs, -, -, -, hindx, hindy⟩ :=
    l154_ree_setup Nat.prime_three (by norm_num) hSn hqS hSp hc hQ hxp hyp hxy hInn hF hcm
  haveI : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := Subtype.finite
  have hxN := l154_mem_normalizer_of_normal hSn x
  have hJS : J ≤ S := hJ.1.trans inf_le_left
  have hTc := l154_JImage_glaPComponent Nat.prime_three hxp hxN hJ θ (MulAut.conj s) hindx
  have hTeq := l154_ree_T_eq_centralizer_three ha hK hs hTc
  have hqT : CFSG.Open.IsQuasisimple ↥(l154JImage 3 S J θ) := by
    rw [hTeq]
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple
      (CFSG.RankThree.PartTwo.Sec19.SimsC198.reeGamma_isQuasisimple_centralizer ha hK s hs)
  obtain ⟨-, e₀, -, -⟩ := l154_JImage_equiv Nat.prime_three hSp hJ hJS hJy θ φ hindy hqT
  obtain ⟨Q, hv, hQ2, ⟨f⟩⟩ := l154_exists_d4any hD4
  have h1 : Nat.card (↥(l154JImage 3 S J θ) ⧸ Subgroup.center ↥(l154JImage 3 S J θ)) =
      orderD 4 Q.card :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.D 4 Q, hv⟩ _
      ⟨e₀.symm.trans f⟩
  have h2 : padicValNat 2 (Nat.card (↥(l154JImage 3 S J θ) ⧸
      Subgroup.center ↥(l154JImage 3 S J θ))) = 3 * (2 * a + 1) := by
    generalize l154JImage 3 S J θ = T at hTeq ⊢
    subst hTeq
    exact l154_ree_padicVal_centralizer_quot ha hK hs
  rw [h1, l154_padicVal_orderD_four hQ2] at h2
  omega

end Small

section Reduction


theorem compTwoPart3_of_d4 {Q : TauCeti.CFSGIndex → Prop} (hN : L154OmegaNID Q)
    (hT : L154OmegaTD4 Q) (hD : CompTwoPart3D4 Q) : T158.CompTwoPart3 Q := by
  intro Ω _ _ S x y J hSn hSq hSp hSc hQ hxp hyp hxy hxny hynx hInn hF hJ hJy
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have h32 : (3 : ℕ) ≠ 2 := by norm_num
  have hnid : NonInnDiag 3 y J :=
    hN 3 hp3 h32 Ω S x y J hSn hSq hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  have htd4 : ¬ (3 = 3 ∧ IsTD4 3 J) :=
    hT 3 hp3 h32 Ω S x y J hSn hSq hSp hSc hQ hxp hyp hxy hInn hF hJ hJy
  have hcJ : IsChevSimple 2 (PSimple 3 J) :=
    T158.isChevSimple_comp_of_kd hp3 (T158.kdChevDownQ_two_holds hp3 h32) hSq hSp hSc
      (hInn.1 (Subgroup.mem_zpowers x)) hxp hJ
  by_cases hFJ : FieldOn 3 y J
  · exact FP.i91CentPartAt_of_stOrder (G := Ω) hp3 h32 (FQ.s10StOrderAt hp3 h32) _ J y hJ hcJ
      hyp hFJ
  · rcases i91_holds Ω 3 hp3 h32 _ J y hJ hcJ hJy hyp hnid with hFJ' | ⟨-, hD4 | hTD⟩
    · exact absurd hFJ' hFJ
    · exact hD Ω S x y J hSn hSq hSp hSc hQ hxp hyp hxy hxny hynx hInn hF hJ hJy hD4 hnid hFJ
    · exact absurd ⟨rfl, hTD⟩ htd4

theorem compTwoPart3_exc_of_d4 (hU : CompTwoPart3D4 l154ExcUntw)
    (hE : CompTwoPart3D4 l154ExcTwE6) : T158.CompTwoPart3 l154Exc :=
  compTwoPart3_of_d4 l154OmegaNID_exc_holds l154OmegaTD4_exc_holds
    (compTwoPart3D4_mono l154_exc_cover_all
      (compTwoPart3D4_or compTwoPart3D4_tits (compTwoPart3D4_or compTwoPart3D4_suz
        (compTwoPart3D4_or compTwoPart3D4_two (compTwoPart3D4_or hU
          (compTwoPart3D4_or hE (compTwoPart3D4_or compTwoPart3D4_triD4 compTwoPart3D4_ree)))))))

end Reduction

end CFSG.LocalAnalysis.GLTheoremA.K155X

end

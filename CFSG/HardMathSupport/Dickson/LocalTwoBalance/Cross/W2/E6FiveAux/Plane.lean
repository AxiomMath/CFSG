module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FiveAux.Steinberg
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FiveAux.Big
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTwE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldAny
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterT

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.TauCetiBridge CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false

section Toral


theorem planesToralBar_E6_five : PlanesToralBar Tag.E6 5 :=
  planesToralBar_five_of_chainBlock
    (fun _ hγ => EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl)) hγ)
    chainBlockToral_E6_four fun _ _ a ha =>
      (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E6_five a ha).le

theorem langToralPlane_E6_five : LangToralPlane Tag.E6 5 :=
  langToralPlane_of_bar Nat.prime_five planesToralBar_E6_five

end Toral

section Rigid


theorem graphCentralizerEmpty_of_bigAnyGenerate {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (hAK : AnyKindCommute) {K : Type} [Field K] [Finite K] [Algebra K L]
    [Algebra.IsAlgebraic K L] (S : LangSetup .E6 L p) (hq3 : 3 ≤ S.D.q)
    {D₁ : Subgroup (ModGL .E6 L)} (hD₁E : D₁ ≤ S.E) (hgen : BigAnyComponentsGenerate S D₁) :
    GraphCentralizerEmpty S D₁ := by
  intro w hw hcomm
  exact not_forall_commute_mul_diagramMap_E6 (K := K) hw
    (commute_adjointGroup_of_bigAnyGenerate hAK S (by decide) hq3 hD₁E hgen
      fun x hx => hcomm x (Or.inl hx))


theorem e6Five_setupRigid (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius) (K : Type) [Field K]
    [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {w : WeylGroup Tag.E6}
    {g0 : ModGL Tag.E6 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
    (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
    (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)
    (hq5 : Nat.card K % 5 = 1 ∨ Nat.card K % 5 = 4) : SetupRigid S := by
  have hq : S.D.q = Nat.card K := by rw [hSD]; rfl
  have hq5' : S.D.q % 5 = 1 ∨ S.D.q % 5 = 4 := by rw [hq]; exact hq5
  have hq4 : 4 ≤ S.D.q := by
    have := S.hqpow.1.two_le
    omega
  have hPS : BigAnyPBig S := bigAnyPBig_five S hq5'
  have hd : S.Descends := by
    have hd7 : LangDescent S.D 7 ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup Tag.E6 K).subtype) := by
      rw [hSD]
      exact langDescent_untw 3 (Or.inl ⟨rfl, rfl⟩) hFr _ rfl Nat.prime_seven (by norm_num)
        (commutator_adjointGroup_E6_eq_top K)
    have hι : Function.Injective ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup Tag.E6 K).subtype) :=
      (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
    exact ⟨K, inferInstance, inferInstance, inferInstance, hd7.mulEquiv' hι, hq.symm,
      fun x => hd7.coe_mulEquiv' hι x⟩
  refine setupRigid_of_descends_E6 S hd (fun D₁ hD₁ hc => ?_) (fun D₁ hD₁ hc => ?_)
    (fun D₁ hD₁ hc => ?_)
  · exact hAF _ _ 5 S (by decide) (Or.inr (Or.inr (Or.inl rfl))) D₁ hD₁
      (hasBigAnyComponent_of_pbig S hq4 hPS hD₁ hc)
  · exact centralizerTrivial_of_bigAnyGenerate hAK S (by decide) (by omega) hD₁
      (bigAnyComponentsGenerate_of_pbig S (Or.inr (Or.inl rfl)) hq4 hPS hD₁ hc)
  · exact graphCentralizerEmpty_of_bigAnyGenerate (K := K) hAK S (by omega) hD₁
      (bigAnyComponentsGenerate_of_pbig S (Or.inr (Or.inl rfl)) hq4 hPS hD₁ hc)

theorem e6Five_langTorusPlaneBalance (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc)
    (hAK : AnyKindCommute) (hAF : AnyKindNoFrobenius) (w : WeylGroup Tag.E6) :
    LangTorusPlaneBalance Tag.E6 w 5 fun q => 5 ∣ q - 1 :=
  langTorusPlaneBalance_of_setupRigidAt (Or.inr (Or.inl rfl))
    (fun K _ _ => commutator_adjointGroup_E6_eq_top K) w Nat.prime_five
    (fun q hq2 hQ => ⟨by omega, Or.inl le_rfl⟩)
    (fun K _ _ Fr hFr g0 hg0C hg0 S hSD hQK => by
      have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      exact e6Five_setupRigid hAK hAF K hFr hg0C hg0 S hSD (by omega))
    hsub hin hsu htw hex

end Rigid

section Inner


theorem e6Five_innerPlaneBalance_of_toralPlane {τ : Tag} {p : ℕ} (hp : p.Prime)
    (htor : LangToralPlane τ p) {Q : ℕ → Prop}
    (hT1 : ∀ w : WeylGroup τ, LangTorusPlaneBalance τ w p Q) (K : Type) [Field K] [Finite K]
    (hpK : ¬ p ∣ Nat.card K) (hQ : Q (Nat.card K)) : InnerPlaneBalance p (adjointGroup τ K) := by
  intro D hDin hD hcard H hH
  have hinj := mulAut_conj_injective_adjointGroup (τ := τ) (K := K)
  set D₀ := D.comap (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) with hD₀
  have hDD : D₀.map MulAut.conj = D := Subgroup.map_comap_eq_self hDin
  have hD₀card : Nat.card D₀ = p ^ 2 := by
    rw [← hcard, ← hDD, Subgroup.card_map_of_injective hinj]
  have hpow₀ : ∀ x ∈ D₀, x ^ p = 1 := fun x hx => by
    have hx' : (MulAut.conj x) ^ p = 1 := hD.2 _ hx
    exact hinj (by rw [map_pow, hx', map_one])
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ := htor K hpK D₀ hpow₀ hD₀card
  refine localDeltaIn_eq_bot_of_conj_sub hH (E := D₀) hDD.le c ?_
  refine hT1 w K hQ Fr hFr g0 hg0C hg0 _ ?_ ?_ ?_ H hH
  · rintro _ ⟨x, hx, rfl⟩
    change (c * x * c⁻¹) ^ p = 1
    rw [conj_pow, hpow₀ x hx, mul_one, mul_inv_cancel]
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hD₀card]
    have := hp.two_le
    nlinarith
  · rintro _ ⟨x, hx, rfl⟩
    exact hc x hx


theorem innerPlaneBalance_adjointE6_five_split (K : Type) [Field K] [Finite K]
    (h5 : ¬ 5 ∣ Nat.card K) (hq : 5 ∣ Nat.card K - 1) :
    InnerPlaneBalance 5 (adjointGroup Tag.E6 K) := by
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  exact e6Five_innerPlaneBalance_of_toralPlane Nat.prime_five langToralPlane_E6_five
    (e6Five_langTorusPlaneBalance hsub hin hsu htw hex (anyKindCommute_of_T anyKindCommuteT_holds)
      anyKindNoFrobenius_of_outer) K h5 hq

section Cat


theorem innerPlaneBalance_catE6_five_split (q : TauCeti.PrimePower)
    (hv : (excIndex .E6 q).Valid) (h : 5 ∣ q.card - 1) :
    InnerPlaneBalance 5 (CatT ⟨excIndex .E6 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  rw [← hK] at h
  have h5 : ¬ 5 ∣ Nat.card K := by
    have : 1 ≤ Nat.card K := Nat.card_pos
    omega
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointE6_five_split K h5 h)

end Cat

end Inner

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

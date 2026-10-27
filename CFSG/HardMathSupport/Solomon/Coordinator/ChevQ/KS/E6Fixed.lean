module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Field
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Fixed
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.E6

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux
  OuterFourInAux
open scoped commutatorElement

section Abstract

theorem fixSubgroup_sq_of_cube {G : Type*} [Group G] (x : MulAut G) (hx : x ^ 3 = 1) :
    fixSubgroup (x ^ 2) = fixSubgroup x := by
  ext g
  rw [mem_fixSubgroup, mem_fixSubgroup]
  constructor
  · intro h
    have h4 : x = x ^ 2 * x ^ 2 := by
      rw [← pow_add]
      calc x = x ^ 3 * x := by rw [hx, one_mul]
        _ = x ^ (2 + 2) := by rw [← pow_succ]
    rw [h4, MulAut.mul_apply, h, h]
  · intro h
    rw [pow_two, MulAut.mul_apply, h, h]

theorem glaPComponent_derived_of_simple {C : Type*} [Group C] [Finite C] {M T : Subgroup C}
    (hT : ⁅M, M⁆ = T) (hs : IsSimpleGroup ↥T) (hnc : ∃ x y : ↥T, x * y ≠ y * x)
    (h3 : 3 ∣ Nat.card T) :
    GLAPComponent 3 M T ∧ ∀ L : Subgroup C, GLAPComponent 3 M L → L = T := by
  have hTM : T ≤ M := by
    rw [← hT]
    exact Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  have hnorm : (T.subgroupOf M).Normal := by
    rw [← hT]
    have h := Subgroup.normal_subgroupOf_commutator_sup M M
    rwa [sup_idem] at h
  refine ⟨MovingAround.Claims126.glaPComponent_of_simple_normal Nat.prime_three hTM hnorm hs hnc
    h3, fun L hL => ?_⟩
  refine MovingAround.SporFacts.glaPComponent_eq_of_simple_normal hTM hnorm hs ?_ hL
  haveI := hnorm
  refine Group.isSolvable_of_comm fun a b => ?_
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e : (((x * y)⁻¹ * (y * x) : ↥M) : C) = ⁅((y : C))⁻¹, ((x : C))⁻¹⁆ := by
        rw [commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
      rw [e, ← hT]
      exact Subgroup.commutator_mem_commutator (M.inv_mem y.2) (M.inv_mem x.2)

theorem isLieQuot_of_simple_mulEquiv {G : Type} [Group G] (hs : IsSimpleGroup G)
    (hnc : ∃ x y : G, x * y ≠ y * x) {P : TauCeti.LieTypeIndex → Prop}
    {d : TauCeti.ValidLieTypeIndex} (hd : P d.1) (e : G ≃* (TauCeti.CFSGIndex.lie d).Group) :
    IsLieQuot G P := by
  haveI := hs
  have hZ : Subgroup.center G = ⊥ := by
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm
  exact ⟨d, hd, ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩⟩

end Abstract

section Certs

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley


theorem e6_fix_unique_component {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 3) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 3)) {η : K ≃+* K} (hη : orderOf η = 3) :
    ∃ T : Subgroup (twistedE6RootGroup K σ),
      GLAPComponent 3 (fixSubgroup (fieldActor σ η)) T ∧
      (∀ L : Subgroup (twistedE6RootGroup K σ),
        GLAPComponent 3 (fixSubgroup (fieldActor σ η)) L → L = T) ∧
      CFSG.Open.IsQuasisimple ↥T ∧ IsLieQuot ↥T Bal209TwoIndex := by
  classical
  have hη3 : η ^ 3 = 1 := by rw [← hη]; exact pow_orderOf_eq_one η
  have hη1 : η ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hη
    omega
  have hK6 : Nat.card K = 2 ^ 6 := by rw [hK]; norm_num
  obtain ⟨d, T, hd0, hd3, hT, hT3, hηT⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_frobenius_of_cube Nat.prime_two (by norm_num) K hK6
      η hη3 hη1
  have hd : d = 2 := by omega
  subst hd
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by norm_num : 1 ≤ 6) hK6
  have hε : ∀ c, (T ^ 2) c = c ^ 2 ^ (1 * (3 + 1)) := by
    intro c
    rw [pow_two, RingAut.mul_apply, hT, hT, ← pow_mul]
    norm_num
  let σ₀ : fixSubfield T ≃+* fixSubfield T := fixSubfieldRestrict fr T
  have hσ₀ : ∀ c : fixSubfield T, ((σ₀ c : fixSubfield T) : K) = (c : K) ^ 2 ^ 1 := by
    intro c
    rw [coe_fixSubfieldRestrict, hfr, pow_one]
  obtain ⟨-, hk4, hJC, -, hder, hsJ, hncJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer (ℓ := 2) (d := 1)
      (m := 3) Nat.prime_two (le_refl 1) (le_refl 3) (by decide) K (by rw [hK6]) T
      (fun c => hT c) σ (fun c => hσ c) σ₀ hσ₀ (T ^ 2) hε
  haveI : Finite (fixSubfield T) := Subtype.finite
  have hfix : fixSubgroup (fieldActor (t := TwistTag.E6) σ η) =
      fixSubgroup (fieldActor (t := TwistTag.E6) σ (T ^ 2)) := by
    rcases hηT with h | h
    · rw [h]
      have hy3 : (fieldActor (t := TwistTag.E6) σ T) ^ 3 = 1 := by
        have := map_pow (fieldActorHom (t := TwistTag.E6) σ) T 3
        rw [hT3, map_one] at this
        exact this.symm
      have hy2 : fieldActor (t := TwistTag.E6) σ (T ^ 2) =
          (fieldActor (t := TwistTag.E6) σ T) ^ 2 :=
        map_pow (fieldActorHom (t := TwistTag.E6) σ) T 2
      rw [hy2, fixSubgroup_sq_of_cube _ hy3]
    · rw [h]
  rw [hfix]
  set C := twistedE6RootGroup K σ with hC
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield T) σ₀ with hJ
  have hder' : ⁅fixSubgroup (fieldActor (t := TwistTag.E6) σ (T ^ 2)),
      fixSubgroup (fieldActor (t := TwistTag.E6) σ (T ^ 2))⁆ = J.subgroupOf C := hder
  haveI := hsJ
  let eJC : J.subgroupOf C ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  have hs : IsSimpleGroup (J.subgroupOf C) := eJC.isSimpleGroup_congr.2 hsJ
  have hnc : ∃ x y : J.subgroupOf C, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hncJ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  obtain ⟨q₂, hq₂p, hq₂e⟩ : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 :=
    ⟨⟨2, 1, Nat.prime_two, Nat.one_pos⟩, rfl, rfl⟩
  have hv₂ : (TauCeti.LieTypeIndex.twistedE6 q₂).Valid := by simp
  have hq₂c : q₂.card = 2 := by rw [TauCeti.PrimePower.card_def, hq₂p, hq₂e]; norm_num
  have hσ₀2 : ∀ c : fixSubfield T, σ₀ c = c ^ 2 := by
    intro c
    apply Subtype.ext
    rw [hσ₀, SubmonoidClass.coe_pow]
    norm_num
  have hkcard : Nat.card (fixSubfield T) = q₂.card ^ 2 := by rw [hk4, hq₂c]
  obtain ⟨eCat⟩ := LieComp.catEquiv_twistedE6_of_field q₂ hv₂ (fixSubfield T) hkcard σ₀
    (fun c => by rw [hq₂c]; exact hσ₀2 c)
  let eJ : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield T) σ₀.toRingHom) ≃* ↥J :=
    Subgroup.equivMapOfInjective _ (baseChangeGL (τ := TwistTag.E6.tag) (fixSubfield T).subtype)
      (baseChangeGL_injective _)
  let e : ↥(J.subgroupOf C) ≃* CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q₂, hv₂⟩ :=
    (eJC.trans eJ.symm).trans eCat.symm
  have hk' : Nat.card (fixSubfield T) = (2 ^ 1) ^ TwistTag.E6.order := hk4
  have hσ' : ∀ c : fixSubfield T, σ₀.toRingHom c = c ^ (2 ^ 1) := fun c => by
    rw [pow_one]
    exact hσ₀2 c
  have h3 : 3 ∣ Nat.card ↥(J.subgroupOf C) := by
    let eDCQ := CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.derivedCentralQuotientEquiv
      (t := TwistTag.E6) (p := 2) (f := 1) Nat.prime_two (le_refl 1) hk' σ₀.toRingHom hσ'
    obtain ⟨x, hx⟩ := exists_orderOf_eq_three_of_twisted (S := ↥(J.subgroupOf C))
      (t := TwistTag.E6) (p := 2) (f := 1) Nat.prime_two (le_refl 1)
      ⟨fixSubfield T, inferInstance, inferInstance, hk', σ₀.toRingHom, hσ',
        ⟨(eJC.trans eJ.symm).trans eDCQ.symm⟩⟩
    exact hx ▸ orderOf_dvd_natCard x
  obtain ⟨hcomp, huniq⟩ := glaPComponent_derived_of_simple hder' hs hnc h3
  exact ⟨J.subgroupOf C, hcomp, huniq, MovingAround.Claims126.isQuasisimple_of_simple hs hnc,
    isLieQuot_of_simple_mulEquiv hs hnc (d := ⟨.twistedE6 q₂, hv₂⟩) ⟨hq₂p, hq₂e⟩ e⟩

theorem e6Fixed : FourUFixed IsTwE6EightIndex FieldAutTwE6 Bal209TwoIndex := by
  intro X _ _ K a hK hLie ha ha3 hF
  obtain ⟨K', fK', hfin, σE, eC, η, γ, hK64, hσE, hη1, hηodd, hγ⟩ := fieldAutTwE6_model hF
  set φ : MulAut (↥K ⧸ Subgroup.center ↥K) := actHom K ⟨a, ha⟩ with hφ
  have hη3 : orderOf η = 3 := orderOf_eq_three_of_odd_ringAut hK64 hη1 hηodd
  obtain ⟨T, hT, hTu, hTq, hTL⟩ := e6_fix_unique_component hK64 σE hσE hη3
  let ε : (↥K ⧸ Subgroup.center ↥K) ≃* twistedE6RootGroup K' σE := eC.trans γ
  have hε : MulAut.congr ε φ = fieldActor σE η := by
    rw [← hγ]
    exact MulEquiv.ext fun x => rfl
  rw [← hε] at hT hTu
  obtain ⟨T', hT', hT'u, ⟨eT⟩⟩ := uniqComp_of_congr ε φ hT hTu
  have hT'q : CFSG.Open.IsQuasisimple ↥T' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eT.symm hTq
  obtain ⟨J₀, hJ₀, hJ₀u, hJ₀q, ⟨eJ⟩⟩ := uniqComp_lift hK.2.2 ha hT' hT'u hT'q
  refine ⟨J₀, hJ₀, hJ₀u, hJ₀q, ?_⟩
  obtain ⟨d, hd, ⟨ψ⟩⟩ := hTL
  exact ⟨d, hd, ⟨(eJ.trans (QuotientGroup.congr _ _ eT (Subgroup.map_center_eq eT))).trans ψ⟩⟩

end Certs

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end

module

public import CFSG.HardMathSupport.Dickson.Sec6.Residuals
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Main
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.AGLEmbedding CFSG.SectionRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.AGLEmbedding.ChevOuter CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3 CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

theorem is3D44_cases {x : TauCeti.LieTypeIndex} (h : CFSG.HardMathSupport.Solomon.Coordinator.Is3D44Index x) :
    ∃ q : TauCeti.PrimePower, x = .trialityD4 q ∧ q.p = 2 ∧ q.exponent = 2 := by
  cases x <;> first | exact ⟨_, rfl, h⟩ | exact h.elim

section Main


theorem exists_model_C44 {L : Type} [Group L] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hq : q.p = 2) (hq2 : q.exponent = 2) (hdq : d.1 = .trialityD4 q)
    (e : L ≃* CatGroup d) :
    CFSG.Blueprint.ChevalleyExceptionalModel L .trialityD4 2 2 ∧
      ∃ (kf : Type) (_ : Field kf) (_ : Finite kf) (σ : kf ≃+* kf), Nat.card kf = (2 ^ 2) ^ 3 ∧
        (∀ c, σ c = c ^ (2 ^ 2)) ∧
        Nonempty (L ≃* graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.trialityD4 q := hdq
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel
      (CatGroup ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide)
        (MulEquiv.refl _)⟩
  rw [hq, hq2] at hm
  have hmod := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hm
  refine ⟨hmod, ?_⟩
  exact exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two (by norm_num) hmod.2

theorem gen3D4_holds : Gen3D4Statement := by
  intro Y _ _ hq hcore hiso A hA
  obtain ⟨⟨x, hv⟩, hd, ⟨e⟩⟩ := hiso
  obtain ⟨q, rfl, hqp, hq2⟩ := is3D44_cases hd
  obtain ⟨hmod, kf, _, _, σ, hkf, hσ, ⟨eC⟩⟩ :=
    exists_model_C44 ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩ q hqp hq2 rfl e
  have : Group.IsPerfect Y := ⟨hq.1⟩
  have hZ3 : IsPGroup 3 (Subgroup.center Y) :=
    CFSG.LocalAnalysis.GLTheoremB.isPGroup_center Nat.prime_three hcore
  have hZodd : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center Y)).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ3
    rw [hn]
    exact Odd.pow (by decide)
  have hZY : Subgroup.center Y = ⊥ := by
    have := triality_even_perfect_odd_cover_trivial hmod (QuotientGroup.mk' (Subgroup.center Y))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hZodd
    rwa [QuotientGroup.ker_mk'] at this
  let eYL : Y ≃* Y ⧸ Subgroup.center Y :=
    ((QuotientGroup.quotientMulEquivOfEq hZY).trans QuotientGroup.quotientBot).symm
  let eY : Y ≃* graphFixedRootGroup TwistTag.D4 kf σ.toRingHom := eYL.trans eC
  have hsimpleL : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  have hsimple : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom) :=
    MulEquiv.isSimpleGroup eC.symm
  have hk : Nat.card kf = 4 ^ 3 := by rw [hkf]; norm_num
  have hσ4 : ∀ c, σ c = c ^ 4 := fun c => by simpa using hσ c
  have hK6 : Nat.card kf = 2 ^ (2 * 3) := by rw [hkf, ← pow_mul]
  haveI : CharP kf 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hK6
  haveI : Fintype kf := Fintype.ofFinite kf
  let e' : kf ≃+* GF64 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, GF64.card_eq]
    norm_num)
  have hC0 := graph_eq_map σ hk hσ4
  have hcardY : Nat.card Y = ordTrialityD4 (2 ^ q.exponent) := by
    rw [Nat.card_congr (eYL.trans e).toEquiv]
    exact card_catGroup_trialityD4_even hqp rfl
  have hv3 : (Nat.card ↥(graphFixedRootGroup TwistTag.D4 kf σ.toRingHom)).factorization 3 = 4 := by
    rw [Nat.card_congr eY.toEquiv.symm, hcardY, hq2]
    have h : ordTrialityD4 (2 ^ 2) = 3 ^ 4 * 837066057318400 := by norm_num [ordTrialityD4]
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hgenC := genBelow_C0 σ hk hσ4 e' hC0 hv3
  show GenBelow A
  exact genBelow_of_congr eY A (hgenC _ (isElemAbelian_map _ (MulAut.congr eY).injective hA))

end Main

end CFSG.HardMathSupport.Dickson.Sec6

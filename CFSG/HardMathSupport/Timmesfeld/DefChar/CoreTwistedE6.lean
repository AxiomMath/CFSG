module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreExcGeneric
public import CFSG.HardMathSupport.Timmesfeld.Balance.Basic
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LieType.Chevalley.EvenExceptionalActorCoverage
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Par
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.BorelTits CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem gLAPPrimeCoreOf_map_mulEquiv {M M' : Type} [Group M] [Group M'] (p : ℕ) (φ : M ≃* M')
    (B : Subgroup M) :
    GLAPPrimeCoreOf p (B.map φ.toMonoidHom) = (GLAPPrimeCoreOf p B).map φ.toMonoidHom := by
  let e : ↥B ≃* ↥(B.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective B φ.toMonoidHom φ.injective
  have h := CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_eq_map_of_mulEquiv p
    (φ.toMonoidHom.comp B.subtype) e (fun x => rfl)
  rw [h]
  unfold GLAPPrimeCoreOf
  rw [Subgroup.map_map]

theorem congr_conj_eq {S Y : Type} [Group S] [Group Y] (e : S ≃* Y) (g : S) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  refine MulEquiv.ext fun y => ?_
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem gLAPPrimeCoreOf_inf_centralizer_of_congr {S Y : Type} [Group S] [Group Y] (p : ℕ)
    (e : S ≃* Y) (H : Subgroup (MulAut S)) (x : MulAut S)
    (h : GLAPPrimeCoreOf p (H.map (MulAut.congr e).toMonoidHom ⊓
      Subgroup.centralizer ({MulAut.congr e x} : Set (MulAut Y))) = ⊥) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  set φ := MulAut.congr e with hφ
  have hmap : H.map φ.toMonoidHom ⊓ Subgroup.centralizer ({φ x} : Set (MulAut Y)) =
      (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))).map φ.toMonoidHom := by
    ext z
    obtain ⟨y, rfl⟩ := φ.surjective z
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨⟨y', hy', hyy'⟩, hc⟩
      have : y' = y := φ.injective hyy'
      subst this
      refine ⟨y', ⟨hy', ?_⟩, rfl⟩
      apply φ.injective
      simpa using hc
    · rintro ⟨y', ⟨hy', hc⟩, hyy'⟩
      have : y' = y := φ.injective hyy'
      subst this
      refine ⟨⟨y', hy', rfl⟩, ?_⟩
      have := congrArg φ hc
      simpa using this
  rw [hmap, gLAPPrimeCoreOf_map_mulEquiv] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h

theorem fixedDiagonalFieldActors_E6_eq_top_all {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ p ^ f) : fixedDiagonalFieldActors .E6 K σ = ⊤ := by
  obtain ⟨-, -, -, -, -, hΔ, hfa, hnf, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  refine eq_top_iff.mpr fun α _ => ?_
  obtain ⟨g, u, δ, rfl⟩ := hnf α
  refine (EvenExceptionalActorCoverage.mem_fixedDiagonalFieldActors_iff _).2 ⟨g, g.2,
    compatDiag TwistTag.E6 σ.toRingHom u, fun i => compatDiag_perm u i, δ,
    CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K δ σ, fun x => ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    hΔ, hfa, Subgroup.coe_inv]
  group

theorem defCharInnerCoreFreeFamTwistedE6 : DefCharInnerCoreFreeFam .twistedE6 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch x hx hxo H hH
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (2 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    change Nat.card (GaloisField q.p (2 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 2
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p hf K hKc
  subst hpq
  have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := hKc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcen, ⟨eC⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p hf K hK2 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  have hσ2 : σ ^ TwistTag.E6.order = 1 := by
    have h2 : TwistTag.E6.order = 2 := rfl
    rw [h2]
    ext c
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = (q.p ^ q.exponent) ^ 2 := by
      rw [← Nat.card_eq_fintype_card, hK2]
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, ← sq, ← hcard, FiniteField.pow_card]
  have hBT : Holds (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) q.p :=
    holds_of_twistedChevalleyModel (t := TwistTag.E6) hf
      ⟨K, inferInstance, inferInstance, hK2, σ.toRingHom, hσ, ⟨eC.symm⟩⟩
  have hAtop := fixedDiagonalFieldActors_E6_eq_top_all q.prime_p hf hK2 σ hσ
  have hpc := parCharP_of_data hcen (pCharData_fixed TwistTag.E6 K σ hσ2 q.p)
  have hS : (MulAut.congr e) x ∈ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range := by
    obtain ⟨g, rfl⟩ := hx
    exact ⟨e g, (congr_conj_eq e g).symm⟩
  refine gLAPPrimeCoreOf_inf_centralizer_of_congr q.p e H x ?_
  refine gLAPPrimeCoreOf_centralizer_eq_bot_of_parCharP hBT hcen hpc
    (A := fixedDiagonalFieldActors TwistTag.E6 K σ) (by rw [hAtop]; exact le_top) ?_ hS ?_
  · rintro _ ⟨g, rfl⟩
    exact ⟨MulAut.conj (e.symm g), hH ⟨e.symm g, rfl⟩, by
      show MulAut.congr e (MulAut.conj (e.symm g)) = _
      rw [congr_conj_eq, MulEquiv.apply_symm_apply]⟩
  · rw [MulEquiv.orderOf_eq]
    exact hxo

end CFSG.HardMathSupport.Timmesfeld.DefChar

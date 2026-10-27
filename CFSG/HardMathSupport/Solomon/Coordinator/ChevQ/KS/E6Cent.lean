module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentThree

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  OuterFourInAux
open scoped MatrixGroups Matrix

theorem e6IsThreeCentral_map {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] (φ : Q ≃* Q') {z : Q}
    (hz : IsThreeCentral Q z) : IsThreeCentral Q' (φ z) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨(orderOf_injective (φ : Q →* Q') φ.injective z).trans hz.1, ?_⟩
  obtain ⟨S, hS⟩ := hz.2
  refine ⟨Sylow.mapSurjective (f := (φ : Q →* Q')) φ.surjective S, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := Subgroup.mem_centralizer_singleton_iff.1 (hS hy)
  show φ y * φ z = φ z * φ y
  rw [← map_mul, ← map_mul, h]

theorem map_centralizer_mulEquiv_e6 {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (H : Subgroup Q) :
    (Subgroup.centralizer (H : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ((H.map e.toMonoidHom : Subgroup Q') : Set Q') := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h h' hh'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hh'
    have := congrArg e (h x hx)
    simpa using this
  · intro h x hx
    apply e.injective
    simpa using h (e x) (Subgroup.mem_map_of_mem _ hx)

theorem map_map_symm_e6 {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') (H : Subgroup Q) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id H
  ext x
  simp

section Small


theorem dV_smul_x0 {L : Type} [Field L] (ω : Lˣ) (c : ZMod 3) :
    dV ω (c • x0) = dV (ω ^ c.val) x0 := by
  unfold dV
  congr 1
  funext i
  by_cases hi : i = 3
  · subst hi
    simp only [torV, x0, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    rw [show ZMod.val (1 : ZMod 3) = 1 from rfl, pow_one]
  · simp [torV, x0, Pi.single_apply, hi]

end Small

section Model


theorem exists_twE6_model_eight {Q : Type} [Group Q]
    (hQ : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = 64 ∧
      (∀ c, σ c = c ^ 8) ∧ Nonempty (Q ≃* twistedE6RootGroup K σ) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hQ
  cases d with
  | twistedE6 q =>
    obtain ⟨K, fK, σ, hK, hσ, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    have hq : q.p ^ q.exponent = 8 := by rw [hd.1, hd.2]; norm_num
    haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    exact ⟨K, fK, inferInstance, σ, by rw [hK, hq]; norm_num, fun c => by rw [hσ, hq],
      ⟨e.trans eC⟩⟩
  | _ => exact hd.elim

theorem exists_model_at_z0 {Q : Type} [Group Q] [Finite Q]
    (hQ : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group))
    {z : Q} (hz : IsThreeCentral Q z) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2) (D : Std8 L) (ω : Lˣ)
      (hω : orderOf ω = 3) (κ : Q ≃* ↥D.S.Γ), κ z = D.z0 hω := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e1⟩⟩ := exists_twE6_model_eight hQ
  obtain ⟨L, _, _, _, D, ⟨e2⟩⟩ := exists_std8 hK σ hσ
  obtain ⟨ω, hω⟩ := TwE6InnerAbs.exists_orderOf_three (L := L)
  haveI := D.finite_Γ
  set φ : Q ≃* ↥D.S.Γ := e1.trans e2 with hφ
  obtain ⟨g, c, hc, hgc⟩ := D.exists_conj_dV_of_threeCentral hω (e6IsThreeCentral_map φ hz)
  have hcop : Nat.Coprime 3 c.val := by
    have h0 : c.val ≠ 0 := fun h => hc ((ZMod.val_eq_zero c).1 h)
    have h3 : c.val < 3 := ZMod.val_lt c
    obtain h | h : c.val = 1 ∨ c.val = 2 := by omega
    · rw [h]; decide
    · rw [h]; decide
  have hω' : orderOf (ω ^ c.val) = 3 := by
    rw [Nat.Coprime.orderOf_pow (by rwa [hω]), hω]
  refine ⟨L, inferInstance, inferInstance, inferInstance, D, ω ^ c.val, hω',
    φ.trans (MulAut.conj g), ?_⟩
  apply Subtype.ext
  change ((g * φ z * g⁻¹ : ↥D.S.Γ) : ModGL Tag.E6 L) = dV (ω ^ c.val) x0
  rw [hgc, dV_smul_x0]

theorem e6_threeCentral_shape_strong
    {Q : Type} [Group Q]
    [Finite Q]
    (hQ : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group))
    {z : Q} (hz : IsThreeCentral Q z) :
    ∃ T : Fin 3 → Subgroup Q, Function.Injective T ∧
      (∀ L : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({z} : Set Q)) L ↔ ∃ i, L = T i) ∧
      (∀ i, CFSG.Open.IsQuasisimple ↥(T i) ∧ IsLieQuot ↥(T i) IsU3EightIndex) ∧
      (∀ i j, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j, Commute u v) ∧ z ∈ ⨆ i, T i ∧
      IsPGroup 3 ↥(Subgroup.centralizer ((⨆ i, T i : Subgroup Q) : Set Q)) ∧
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({z} : Set Q)) = ⊥ := by
  obtain ⟨L, _, _, _, D, ω, hω, κ, hκ⟩ := exists_model_at_z0 hQ hz
  haveI := D.finite_Γ
  obtain ⟨T, hinj, hcomp, hqs, hcomm, hzT, hgrp, hcore⟩ := D.threeComponents hω
  have hzsymm : κ.symm (D.z0 hω) = z := by rw [← hκ]; exact κ.symm_apply_apply z
  have hcent : (Subgroup.centralizer ({z} : Set Q)).map κ.toMonoidHom =
      Subgroup.centralizer ({D.z0 hω} : Set ↥D.S.Γ) := by
    rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton, hκ]
  have hcent' : (Subgroup.centralizer ({D.z0 hω} : Set ↥D.S.Γ)).map κ.symm.toMonoidHom =
      Subgroup.centralizer ({z} : Set Q) := by
    rw [CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton, hzsymm]
  refine ⟨fun k => (T k).map κ.symm.toMonoidHom, ?_, fun J => ⟨fun hJ => ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact fun k l h => hinj (Subgroup.map_injective κ.symm.injective h)
  · have h := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three κ hJ
    rw [hcent] at h
    obtain ⟨k, hk⟩ := (hcomp _).1 h
    refine ⟨k, ?_⟩
    show J = (T k).map κ.symm.toMonoidHom
    rw [← hk, map_map_symm_e6]
  · rintro ⟨k, rfl⟩
    have h := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three κ.symm
      ((hcomp (T k)).2 ⟨k, rfl⟩)
    rw [hcent'] at h
    exact h
  · intro k
    have e : ↥((T k).map κ.symm.toMonoidHom) ≃* ↥(T k) :=
      ((T k).equivMapOfInjective κ.symm.toMonoidHom κ.symm.injective).symm
    exact ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e (hqs k).1,
      isLieQuot_of_mulEquiv_e6 e.symm (hqs k).2⟩
  · intro k l hkl u hu v hv
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 hv
    exact (hcomm k l hkl t ht t' ht').map κ.symm.toMonoidHom
  · have h : κ.symm (D.z0 hω) ∈ (⨆ k, T k).map κ.symm.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hzT
    rw [hzsymm, Subgroup.map_iSup] at h
    exact h
  · have hjoin : (⨆ k, (T k).map κ.symm.toMonoidHom) =
        (⨆ k, T k).map κ.symm.toMonoidHom := (Subgroup.map_iSup _ _).symm
    have hc : (Subgroup.centralizer ((⨆ k, T k : Subgroup ↥D.S.Γ) : Set ↥D.S.Γ)).map
        κ.symm.toMonoidHom = Subgroup.centralizer
          (((⨆ k, T k).map κ.symm.toMonoidHom : Subgroup Q) : Set Q) :=
      map_centralizer_mulEquiv_e6 κ.symm _
    have hg : IsPGroup 3 ↥((Subgroup.centralizer
        ((⨆ k, T k : Subgroup ↥D.S.Γ) : Set ↥D.S.Γ)).map κ.symm.toMonoidHom) :=
      hgrp.of_equiv (Subgroup.equivMapOfInjective _ κ.symm.toMonoidHom κ.symm.injective)
    rw [hc, ← hjoin] at hg
    exact hg
  · have h1 : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({D.z0 hω} : Set ↥D.S.Γ)) = ⊥ := by
      unfold GLAPPrimeCoreOf
      rw [hcore]
      exact Subgroup.map_bot _
    have h2 := CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_map_mulEquiv 3 κ
      (Subgroup.centralizer ({z} : Set Q))
    rw [hcent, h1] at h2
    exact (Subgroup.map_eq_bot_iff_of_injective _ κ.injective).1 h2.symm

theorem e6_threeCentral_shape
    {Q : Type} [Group Q]
    [Finite Q]
    (hQ : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group))
    {z : Q} (hz : IsThreeCentral Q z) :
    ∃ T : Fin 3 → Subgroup Q, Function.Injective T ∧
      (∀ L : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({z} : Set Q)) L ↔ ∃ i, L = T i) ∧
      (∀ i, CFSG.Open.IsQuasisimple ↥(T i) ∧ IsLieQuot ↥(T i) IsU3EightIndex) ∧
      (∀ i j, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j, Commute u v) ∧ z ∈ ⨆ i, T i := by
  obtain ⟨T, h1, h2, h3, h4, h5, -, -⟩ := e6_threeCentral_shape_strong hQ hz
  exact ⟨T, h1, h2, h3, h4, h5⟩

theorem e6_threeCentral_core
    {Q : Type} [Group Q]
    [Finite Q]
    (hQ : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group))
    {z : Q} (hz : IsThreeCentral Q z) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({z} : Set Q)) = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := e6_threeCentral_shape_strong hQ hz
  exact h

end Model

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

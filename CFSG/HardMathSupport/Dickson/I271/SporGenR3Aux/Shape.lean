module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Leaf
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMShape
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Yardstones.Md0ec50421ce4

@[expose] def CentShape (p : ℕ) (Good : ∀ (T : Type) [Group T], Prop) (Q : Type) [Group Q] :
    Prop :=
  ∀ k : Q, k ≠ 1 → k ^ p = 1 →
    PConstrainedShape p (Subgroup.centralizer ({k} : Set Q)) ∨
      ∃ J : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) J ∧
        (∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I → I = J) ∧
        Good (PSimple p J)

section Transport

variable {Q Q' : Type} [Group Q] [Group Q']

theorem map_centralizer_singleton (e : Q ≃* Q') (k : Q) :
    (Subgroup.centralizer ({k} : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ({e k} : Set Q') := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have := congrArg e hx
    simpa using this
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simpa using hy

theorem pConstrainedShape_map {p : ℕ} (e : Q ≃* Q') {C : Subgroup Q} (h : PConstrainedShape p C) :
    PConstrainedShape p (C.map e.toMonoidHom) := by
  obtain ⟨R, hRC, hRn, hRp, hRc⟩ := h
  refine ⟨R.map e.toMonoidHom, Subgroup.map_mono hRC, ?_, hRp.map _, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨r, hr, rfl⟩
    exact ⟨c * r * c⁻¹, hRn c hc r hr, by simp⟩
  · rintro y ⟨⟨c, hc, rfl⟩, hy⟩
    refine ⟨c, hRc ⟨hc, ?_⟩, rfl⟩
    show c ∈ Subgroup.centralizer (R : Set Q)
    have hy' : e.toMonoidHom c ∈ Subgroup.centralizer ((R.map e.toMonoidHom : Subgroup Q') : Set Q') :=
      hy
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := Subgroup.mem_centralizer_iff.1 hy' (e r) ⟨r, hr, rfl⟩
    apply e.injective
    simpa using h1

variable [Finite Q]

theorem glaPComponent_map_equiv {p : ℕ} (hp : p.Prime) (e : Q ≃* Q') {X K : Subgroup Q}
    (hK : GLAPComponent p X K) :
    GLAPComponent p (X.map e.toMonoidHom) (K.map e.toMonoidHom) :=
  glaPComponent_map hp e.toMonoidHom (coprime_ker_mulEquiv e X) hK

theorem CentShape.of_equiv {p : ℕ} (hp : p.Prime) {Good : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T') [Finite Q']
    (e : Q ≃* Q') (h : CentShape p Good Q) : CentShape p Good Q' := by
  intro k' hk1 hkp
  set k : Q := e.symm k' with hk
  have hk1' : k ≠ 1 := fun h1 => hk1 (by simpa [hk] using congrArg e h1)
  have hkp' : k ^ p = 1 := by
    apply e.injective
    simpa [hk] using hkp
  have hek : e k = k' := by simp [hk]
  have hmap : (Subgroup.centralizer ({k} : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ({k'} : Set Q') := by
    rw [map_centralizer_singleton e k, hek]
  rcases h k hk1' hkp' with hc | ⟨J, hJ, hu, hG⟩
  · left
    rw [← hmap]
    exact pConstrainedShape_map e hc
  · right
    refine ⟨J.map e.toMonoidHom, ?_, ?_, ?_⟩
    · rw [← hmap]
      exact glaPComponent_map_equiv hp e hJ
    · intro I' hI'
      have h1 := glaPComponent_map_equiv hp e.symm hI'
      have hmap' : (Subgroup.centralizer ({k'} : Set Q')).map e.symm.toMonoidHom =
          Subgroup.centralizer ({k} : Set Q) := by
        rw [map_centralizer_singleton e.symm k']
      rw [hmap'] at h1
      have h2 := hu _ h1
      rw [← h2, Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by ext; simp
      rw [this, Subgroup.map_id]
    · exact hGood _ _ (pSimpleEquiv p (e.subgroupMap J)) hG

end Transport

section Core

variable {X : Type} [Group X] [Finite X]

theorem subgroupOf_inf_centralizer_eq {K : Subgroup X} {a k : X} (hk : k ∈ K)
    (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) :
    (K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K =
      Subgroup.centralizer ({(⟨k, hk⟩ : ↥K)} : Set ↥K) := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  have hcy : (k⁻¹ * a) * (y : X) = (y : X) * (k⁻¹ * a) :=
    (Subgroup.mem_centralizer_iff.1 hc y y.2).symm
  constructor
  · rintro ⟨-, hy⟩
    apply Subtype.ext
    show (y : X) * k = k * (y : X)
    have h1 : (y : X) * k * (k⁻¹ * a) = k * (y : X) * (k⁻¹ * a) := by
      calc (y : X) * k * (k⁻¹ * a) = (y : X) * a := by group
        _ = a * (y : X) := hy
        _ = k * ((k⁻¹ * a) * (y : X)) := by group
        _ = k * ((y : X) * (k⁻¹ * a)) := by rw [hcy]
        _ = k * (y : X) * (k⁻¹ * a) := by group
    exact mul_right_cancel h1
  · intro hy
    refine ⟨y.2, ?_⟩
    have hky : (y : X) * k = k * (y : X) := congrArg Subtype.val hy
    calc (y : X) * a = ((y : X) * k) * (k⁻¹ * a) := by group
      _ = (k * (y : X)) * (k⁻¹ * a) := by rw [hky]
      _ = k * ((y : X) * (k⁻¹ * a)) := by group
      _ = k * ((k⁻¹ * a) * (y : X)) := by rw [hcy]
      _ = a * (y : X) := by group

end Core

section Mult

open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem card_center_dvd_multiplier (hSpM : SporadicMultipliers) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (s : TauCeti.SporadicName)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    Nat.card (Subgroup.center K) ∣ sporadicMultiplierOrder s := by
  have hq' : CFSG.IsQuasisimple K :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      K hq⟩
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq' e
  rw [hSpM.1 s] at hdvd
  exact hdvd

theorem center_eq_bot_of_mult (hSpM : SporadicMultipliers) {X : Type} [Group X] [Finite X]
    {p : ℕ} {K B : Subgroup X} {name : TauCeti.SporadicName} (hH : CompHyp p K B)
    (hS : I271SporType K name) (hm : ¬ p ∣ sporadicMultiplierOrder name) :
    Subgroup.center ↥K = ⊥ := by
  obtain ⟨e⟩ := hS
  have hp := hH.prime
  have hZ : IsPGroup p (Subgroup.center ↥K) :=
    i271h_center_isPGroup hp hH.primeCore
  have hd := card_center_dvd_multiplier hSpM hH.quasi name e
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ
  rw [hn] at hd
  apply Subgroup.eq_bot_of_card_eq
  rw [hn]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero]
  · exact absurd ((dvd_pow_self p hpos.ne').trans hd) hm

end Mult

end CFSG.HardMathSupport.Dickson.I271

module

public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.GroupTheory.PLayer.Transport
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReduction
public import CFSG.HardMathSupport.Lang.Proving.FixedOrderCongruence
public import CFSG.GroupTheory.QuasisimpleCenterDivisibility
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

@[expose] def OuterPLayerAt (p : ℕ) (S : Type) [Group S] [Finite S] : Prop :=
  ∀ b : MulAut S, b ^ p = 1 → b ∉ innAutDerived S → GLAPLayer p (fixSubgroup b) ≠ ⊥

@[expose] def outerPLayerExc (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A 1 q => p = 3 ∧ q.card = 8
  | .twistedA 2 q => p = 3 ∧ q.card = 8
  | .suzuki k => p = 5 ∧ k = 2
  | .trialityD4 _ => p = 3
  | _ => False

@[expose] def LieOuterPLayer (p : ℕ) (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.LieTypeIndex) (hd : d.Valid), P d → ¬ outerPLayerExc p d →
    ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨d, hd⟩).Group) →
      ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p S → p ∣ Nat.card S → OuterPLayerAt p S

@[expose] def isLinearIdx : TauCeti.LieTypeIndex → Prop
  | .A _ _ => True
  | _ => False

@[expose] def isUnitaryIdx : TauCeti.LieTypeIndex → Prop
  | .twistedA _ _ => True
  | _ => False

@[expose] def isClassicalBCDIdx : TauCeti.LieTypeIndex → Prop
  | .B _ _ => True
  | .C _ _ => True
  | .D _ _ => True
  | .twistedD _ _ => True
  | _ => False

@[expose] def isTrialityIdx : TauCeti.LieTypeIndex → Prop
  | .trialityD4 _ => True
  | _ => False

@[expose] def isExcUntwistedIdx : TauCeti.LieTypeIndex → Prop
  | .G2 _ => True
  | .F4 _ => True
  | .E6 _ => True
  | .E7 _ => True
  | .E8 _ => True
  | _ => False

@[expose] def isExcTwistedIdx : TauCeti.LieTypeIndex → Prop
  | .twistedE6 _ => True
  | .suzuki _ => True
  | .reeG2 _ => True
  | .reeF4 _ => True
  | .tits => True
  | _ => False

theorem lieOuterPLayer_of_families {p : ℕ}
    (h1 : LieOuterPLayer p isLinearIdx) (h2 : LieOuterPLayer p isUnitaryIdx)
    (h3 : LieOuterPLayer p isClassicalBCDIdx) (h4 : LieOuterPLayer p isTrialityIdx)
    (h5 : LieOuterPLayer p isExcUntwistedIdx) (h6 : LieOuterPLayer p isExcTwistedIdx) :
    LieOuterPLayer p fun _ => True := by
  intro d hd _ hnExc S hS hfin e hnot hpdvd
  cases d with
  | A n q => exact h1 _ hd trivial hnExc S e hnot hpdvd
  | twistedA n q => exact h2 _ hd trivial hnExc S e hnot hpdvd
  | B n q => exact h3 _ hd trivial hnExc S e hnot hpdvd
  | C n q => exact h3 _ hd trivial hnExc S e hnot hpdvd
  | D n q => exact h3 _ hd trivial hnExc S e hnot hpdvd
  | twistedD n q => exact h3 _ hd trivial hnExc S e hnot hpdvd
  | E6 q => exact h5 _ hd trivial hnExc S e hnot hpdvd
  | E7 q => exact h5 _ hd trivial hnExc S e hnot hpdvd
  | E8 q => exact h5 _ hd trivial hnExc S e hnot hpdvd
  | F4 q => exact h5 _ hd trivial hnExc S e hnot hpdvd
  | G2 q => exact h5 _ hd trivial hnExc S e hnot hpdvd
  | twistedE6 q => exact h6 _ hd trivial hnExc S e hnot hpdvd
  | trialityD4 q => exact h4 _ hd trivial hnExc S e hnot hpdvd
  | suzuki k => exact h6 _ hd trivial hnExc S e hnot hpdvd
  | reeG2 k => exact h6 _ hd trivial hnExc S e hnot hpdvd
  | reeF4 k => exact h6 _ hd trivial hnExc S e hnot hpdvd
  | tits => exact h6 _ hd trivial hnExc S e hnot hpdvd

theorem outerPLayerAt_congr {p : ℕ} (hp : p.Prime) {S S' : Type} [Group S] [Finite S]
    [Group S'] [Finite S'] (e : S ≃* S') (h : OuterPLayerAt p S) : OuterPLayerAt p S' := by
  intro b hbp hb
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαp : α ^ p = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconj]
    exact hbp
  have hαout : α ∉ innAutDerived S := by
    intro hαmem
    apply hb
    rw [← hconj, ← map_innAutDerived_congr e]
    exact Subgroup.mem_map_of_mem _ hαmem
  intro hbot
  apply h α hαp hαout
  rw [← hconj, CFSG.glaPLayer_fixSubgroup_congr hp e α] at hbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hbot

theorem glaPLayer_fixSubgroup_ne_bot_of_quasisimple {K : Type} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) {x : MulAut K} {T : Subgroup K} (hT : T ≤ fixSubgroup x)
    (hTn : ∀ f ∈ fixSubgroup x, ∀ t ∈ T, f * t * f⁻¹ ∈ T)
    (hTq : CFSG.IsQuasisimple T) (hTp : p ∣ Nat.card T) :
    GLAPLayer p (fixSubgroup x) ≠ ⊥ := by
  have hN : (T.subgroupOf (fixSubgroup x)).Normal := by
    refine ⟨fun t ht g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact hTn g.1 g.2 t.1 ht
  have hq : CFSG.Open.IsQuasisimple T := ⟨hTq.1.commutator_eq_top, hTq.2.1⟩
  have hdvd : p ∣ Nat.card (T ⧸ Subgroup.center T) :=
    dvd_card_quotient_center_of_quasisimple hTq hp hTp
  have hcomp : GLAPComponent p (fixSubgroup x) T :=
    CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp
      (CFSG.Open.IsSubnormal.step hT hN (CFSG.Open.IsSubnormal.refl _)) hq hdvd
  have hle : T ≤ GLAPLayer p (fixSubgroup x) := le_sSup hcomp
  intro hbot
  have hTbot : T = ⊥ := le_bot_iff.1 (hle.trans (le_of_eq hbot))
  haveI : Nontrivial T := CFSG.LocalCores.isQuasisimple_nontrivial hTq
  haveI : Subsingleton T := by rw [hTbot]; infer_instance
  exact not_subsingleton T inferInstance

theorem glaPLayer_fixSubgroup_ne_bot_of_fieldCoreAt {K : Type} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) {x : MulAut K} (h : FieldCoreAt p x) :
    GLAPLayer p (fixSubgroup x) ≠ ⊥ := by
  obtain ⟨T, hTF, hTn, hTq, hTp, -⟩ := h
  exact glaPLayer_fixSubgroup_ne_bot_of_quasisimple hp hTF hTn hTq
    ((Nat.Prime.dvd_iff_not_coprime hp).2 hTp)

theorem characteristic_ne_of_not_isChevSimple {p : ℕ} {d : TauCeti.LieTypeIndex}
    (hd : d.Valid) {S : Type} [Group S]
    (hS : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨d, hd⟩).Group))
    (h : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p S) : d.characteristic ≠ p := by
  intro hc
  apply h
  exact Or.inl ⟨TauCeti.CFSGIndex.lie ⟨d, hd⟩, hc, hS⟩

theorem exists_orderOf_eq_prime_mem_fixSubgroup {S : Type*} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) (x : MulAut S) (hx : x ^ p = 1) (hdvd : p ∣ Nat.card S) :
    ∃ y ∈ fixSubgroup x, orderOf y = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod := CFSG.HardMathSupport.Lang.Proving.card_modEq_card_fixedPoints_of_pow_prime x hx
  have hcard : Nat.card {y : S // x y = y} = Nat.card (fixSubgroup x) :=
    Nat.card_congr (Equiv.refl _)
  have hdvd' : p ∣ Nat.card (fixSubgroup x) := by
    rw [← hcard, Nat.dvd_iff_mod_eq_zero]
    rw [← hmod]
    exact Nat.dvd_iff_mod_eq_zero.1 hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := fixSubgroup x) p hdvd'
  refine ⟨y.1, y.2, ?_⟩
  rwa [Subgroup.orderOf_coe]

theorem outerPLayerAt_of_mulEquiv_of_glaPLayer {p : ℕ} (hp : p.Prime)
    {S : Type} [Group S] [Finite S] {M : Type} [Group M] [Finite M] (e : S ≃* M)
    (h : ∀ x : MulAut M, x ^ p = 1 → x ∉ innAutDerived M →
      GLAPLayer p (fixSubgroup x) ≠ ⊥) : OuterPLayerAt p S :=
  outerPLayerAt_congr hp e.symm h

theorem outerPLayerAt_of_mulEquiv_of_fieldCoreAt {p : ℕ} (hp : p.Prime)
    {S : Type} [Group S] [Finite S] {M : Type} [Group M] [Finite M] (e : S ≃* M)
    (hfc : ∀ x : MulAut M, x ^ p = 1 → x ∉ innAutDerived M → FieldCoreAt p x) :
    OuterPLayerAt p S :=
  outerPLayerAt_of_mulEquiv_of_glaPLayer hp e fun x hxp hxout =>
    glaPLayer_fixSubgroup_ne_bot_of_fieldCoreAt hp (hfc x hxp hxout)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

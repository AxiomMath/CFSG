module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def OuterIdxAt (p : ℕ) (d : TauCeti.LieTypeIndex) (S : Type) [Group S] : Prop :=
  ∀ β : MulAut S, β ^ p = 1 → β ∉ innAutDerived S →
    ∃ J : Subgroup S, GLAPComponent p (fixSubgroup β) J ∧ p ∣ Nat.card J ∧
      ∃ i : TauCeti.CFSGIndex, Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧ subRelC p d i

theorem outerIdxAt_of_mulEquiv {p : ℕ} (hp : p.Prime) {d : TauCeti.LieTypeIndex}
    {S S' : Type} [Group S] [Finite S] [Group S'] (e : S ≃* S')
    (h : OuterIdxAt p d S) : OuterIdxAt p d S' := by
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
  obtain ⟨J, hJcomp, hJp, i, ⟨φ⟩, hsub⟩ := h α hαp hαout
  haveI : Finite S' := Finite.of_injective (e.symm : S' → S) e.symm.injective
  refine ⟨J.map (e : S →* S'), ?_, ?_, i, ⟨?_, hsub⟩⟩
  · have hαβ : ∀ k : S, (e : S →* S') (α k) = b ((e : S →* S') k) := by
      intro k
      have h := congrArg (fun f : MulAut S' => f (e k)) hconj
      simpa [MulAut.congr_apply] using h
    have hker : (e : S →* S').ker ≤ Subgroup.center S := by
      rw [(MonoidHom.ker_eq_bot_iff (e : S →* S')).2 e.injective]
      exact bot_le
    exact glaPComponent_map_fixSubgroup (e : S →* S') hker α b hαβ e.surjective hp hJcomp
  · rwa [Subgroup.card_map_of_injective e.injective]
  · exact ⟨(QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥(J.map (e : S →* S')))
      (J.equivMapOfInjective (e : S →* S') e.injective)
      (Subgroup.map_center_eq (J.equivMapOfInjective (e : S →* S') e.injective))).symm.trans φ⟩

@[expose] def IdxCoreAt (p : ℕ) (d : TauCeti.LieTypeIndex) {S : Type} [Group S] (x : MulAut S) :
    Prop :=
  ∃ T : Subgroup S, T ≤ fixSubgroup x ∧ (∀ f ∈ fixSubgroup x, ∀ t ∈ T, f * t * f⁻¹ ∈ T) ∧
    CFSG.IsQuasisimple T ∧ p ∣ Nat.card T ∧
    ∃ i : TauCeti.CFSGIndex, Nonempty (↥T ⧸ Subgroup.center ↥T ≃* i.Group) ∧ subRelC p d i

theorem idxCoreAt_of_conj {p : ℕ} {d : TauCeti.LieTypeIndex} {S : Type} [Group S]
    {δ x : MulAut S} (h : IdxCoreAt p d δ) (δ' : MulAut S) (hδ : δ' * x * δ'⁻¹ = δ) :
    IdxCoreAt p d x := by
  obtain ⟨T, hTF, hTn, hTq, hTp, i, ⟨φ⟩, hsub⟩ := h
  have hx : δ'⁻¹ * δ * δ'⁻¹⁻¹ = x := by
    rw [← hδ, inv_inv]
    group
  have hfix : fixSubgroup x = (fixSubgroup δ).map ((δ'⁻¹ : MulAut S) : S →* S) := by
    rw [← hx]
    rw [show δ'⁻¹ * δ * δ'⁻¹⁻¹ = MulAut.congr (δ'⁻¹ : MulAut S) δ from by ext y; rfl]
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr _ _
  refine ⟨T.map ((δ'⁻¹ : MulAut S) : S →* S), ?_, ?_, ?_, ?_, i, ⟨?_, hsub⟩⟩
  · rw [hfix]
    exact Subgroup.map_mono hTF
  · rintro f hf _ ⟨t, ht, rfl⟩
    rw [hfix] at hf
    obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.1 hf
    exact ⟨f' * t * f'⁻¹, hTn f' hf' t ht, by simp⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (T.equivMapOfInjective ((δ'⁻¹ : MulAut S) : S →* S) (δ'⁻¹ : MulAut S).injective) hTq
  · rwa [Subgroup.card_map_of_injective (δ'⁻¹ : MulAut S).injective]
  · exact ⟨(QuotientGroup.congr (Subgroup.center ↥T)
      (Subgroup.center ↥(T.map ((δ'⁻¹ : MulAut S) : S →* S)))
      (T.equivMapOfInjective ((δ'⁻¹ : MulAut S) : S →* S) (δ'⁻¹ : MulAut S).injective)
      (Subgroup.map_center_eq
        (T.equivMapOfInjective ((δ'⁻¹ : MulAut S) : S →* S) (δ'⁻¹ : MulAut S).injective))).symm.trans φ⟩

theorem idxCoreAt_of_fixSubgroup_eq {p : ℕ} {d : TauCeti.LieTypeIndex} {S : Type} [Group S]
    {x y : MulAut S} (h : fixSubgroup x = fixSubgroup y) (hx : IdxCoreAt p d x) :
    IdxCoreAt p d y := by
  obtain ⟨T, hTF, hN, hq, hp, i, he, hr⟩ := hx
  exact ⟨T, h ▸ hTF, fun f hf => hN f (h.symm ▸ hf), hq, hp, i, he, hr⟩

theorem idxCoreAt_of_mulEquiv {P P' : Type} [Group P] [Finite P] [Group P']
    {p : ℕ} {d : TauCeti.LieTypeIndex} {a : MulAut P} {δ : MulAut P'} (Θ : P ≃* P')
    (hΘ : MulAut.congr Θ a = δ) {N J : Subgroup P'} (hN : ∀ t, δ t = t ↔ t ∈ N)
    (hJN : J ≤ N) (hJn : (J.subgroupOf N).Normal) (hJq : CFSG.IsQuasisimple J)
    (hpJ : p ∣ Nat.card J)
    (hi : ∃ i : TauCeti.CFSGIndex, Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧
      subRelC p d i) : IdxCoreAt p d a := by
  obtain ⟨i, ⟨eJ⟩, hsub⟩ := hi
  refine ⟨J.map (Θ.symm : P' →* P), ?_, ?_, ?_, ?_, i, ?_, hsub⟩
  · rintro _ ⟨j, hj, rfl⟩
    have hjN : j ∈ N := hJN hj
    have h1 : j ∈ fixSubgroup (MulAut.congr Θ a) :=
      (mem_fixSubgroup).2 (by rw [hΘ]; exact (hN j).2 hjN)
    show Θ.symm j ∈ fixSubgroup a
    rw [mem_fixSubgroup]
    have h1' : Θ (a (Θ.symm j)) = j := by
      rw [mem_fixSubgroup] at h1
      simpa [MulAut.congr_apply] using h1
    simpa using congrArg Θ.symm h1' 
  · intro f hf t ht
    rw [mem_fixSubgroup] at hf
    obtain ⟨j, hj, rfl⟩ := ht
    have hfN : Θ f ∈ N := by
      have h2 : (MulAut.congr Θ a) (Θ f) = Θ f := by
        have h1 : (MulAut.congr Θ a) (Θ f) = Θ (a f) := by
          simp [MulAut.congr_apply]
        rw [h1, hf]
      exact (hN (Θ f)).1 (hΘ ▸ h2)
    refine ⟨Θ f * j * (Θ f)⁻¹, ?_, ?_⟩
    · have hmem : (⟨j, hJN hj⟩ : ↥N) ∈ J.subgroupOf N := hj
      have hconj := hJn.conj_mem (⟨j, hJN hj⟩ : ↥N) hmem ⟨Θ f, hfN⟩
      show Θ f * j * (Θ f)⁻¹ ∈ J
      exact hconj
    · simp
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (J.equivMapOfInjective (Θ.symm : P' →* P) Θ.symm.injective) hJq
  · rw [Subgroup.card_map_of_injective Θ.symm.injective]
    exact hpJ
  · let eJT : ↥J ≃* ↥(J.map (Θ.symm : P' →* P)) :=
      J.equivMapOfInjective (Θ.symm : P' →* P) Θ.symm.injective
    exact ⟨(QuotientGroup.congr (Subgroup.center ↥J)
      (Subgroup.center ↥(J.map (Θ.symm : P' →* P))) eJT
      (Subgroup.map_center_eq eJT)).symm.trans eJ⟩

theorem outerIdxAt_of_idxCoreAt {p : ℕ} (hp : p.Prime) {d : TauCeti.LieTypeIndex} {S : Type}
    [Group S] [Finite S]
    (h : ∀ x : MulAut S, x ^ p = 1 → x ∉ innAutDerived S → IdxCoreAt p d x) :
    OuterIdxAt p d S := by
  intro x hxp hxout
  obtain ⟨T, hTF, hTn, hTq, hTp, i, hiso, hsub⟩ := h x hxp hxout
  have hN : (T.subgroupOf (fixSubgroup x)).Normal := by
    refine ⟨fun t ht g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact hTn g.1 g.2 t.1 ht
  have hq : CFSG.Open.IsQuasisimple ↥T := ⟨hTq.1.commutator_eq_top, hTq.2.1⟩
  have hdvd : p ∣ Nat.card (↥T ⧸ Subgroup.center ↥T) :=
    dvd_card_quotient_center_of_quasisimple hTq hp hTp
  have hcomp : GLAPComponent p (fixSubgroup x) T :=
    CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp
      (CFSG.Open.IsSubnormal.step hTF hN (CFSG.Open.IsSubnormal.refl _)) hq hdvd
  exact ⟨T, hcomp, hTp, i, hiso, hsub⟩

@[expose] def outerIdxExc (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  (p = 3 ∧
    ((∃ q : TauCeti.PrimePower, (d = .A 1 q ∨ d = .twistedA 2 q) ∧ q.card = 8) ∨
      (∃ q : TauCeti.PrimePower, d = .trialityD4 q))) ∨
  (p = 5 ∧ d = .suzuki 2)

@[expose] def LieOuterIdx (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic → P d.1 →
    p ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group → ¬ outerIdxExc p d.1 →
    OuterIdxAt p d.1 (TauCeti.CFSGIndex.lie d).Group

theorem kd264OuterIdx_of_families (h1 : LieOuterIdx isLinearIdx) (h2 : LieOuterIdx isUnitaryIdx)
    (h3 : LieOuterIdx isClassicalBCDIdx) (h4 : LieOuterIdx isTrialityIdx)
    (h5 : LieOuterIdx isExcUntwistedIdx) (h6 : LieOuterIdx isExcTwistedIdx) :
    KD264OuterIdx := by
  intro d p hp hp2 hpc hpdvd hexc1 hexc2 β hβp hβout
  have hexc : ¬ outerIdxExc p d.1 := fun h => h.elim hexc1 hexc2
  obtain ⟨e, hd⟩ := d
  cases e with
  | A n q => exact h1 ⟨.A n q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | twistedA n q => exact h2 ⟨.twistedA n q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | B n q => exact h3 ⟨.B n q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | C n q => exact h3 ⟨.C n q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | D n q => exact h3 ⟨.D n q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | twistedD n q => exact h3 ⟨.twistedD n q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | E6 q => exact h5 ⟨.E6 q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | E7 q => exact h5 ⟨.E7 q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | E8 q => exact h5 ⟨.E8 q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | F4 q => exact h5 ⟨.F4 q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | G2 q => exact h5 ⟨.G2 q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | twistedE6 q => exact h6 ⟨.twistedE6 q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | trialityD4 q => exact h4 ⟨.trialityD4 q, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | suzuki k => exact h6 ⟨.suzuki k, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | reeG2 k => exact h6 ⟨.reeG2 k, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | reeF4 k => exact h6 ⟨.reeF4 k, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout
  | tits => exact h6 ⟨.tits, hd⟩ p hp hp2 hpc trivial hpdvd hexc β hβp hβout

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

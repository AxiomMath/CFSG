module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.LocalAnalysis.GLTheoremA.PCompNoncomm
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphismsCongr
public import CFSG.Assembly.InCatalogConverse

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def CompIdxAt (p : ℕ) (d : TauCeti.LieTypeIndex) (S : Type) [Group S] : Prop :=
  ∀ β : MulAut S, β ∈ innAutDerived S → β ^ p = 1 → β ≠ 1 →
    ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) →
      ∃ i : TauCeti.CFSGIndex, Nonempty (↥K ⧸ Subgroup.center ↥K ≃* i.Group) ∧ compRelC d i

@[expose] def CompAlgAt (S : Type) [Group S] : Prop :=
  ∀ β : MulAut S, β ∈ innAutDerived S → β ^ 3 = 1 → β ≠ 1 →
    ∀ K : Subgroup S, IsComponentOf K (fixSubgroup β) →
      ∀ e : TauCeti.ValidLieTypeIndex,
        (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) →
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie e).Group) →
        ∀ x ∈ innAutDerived S, x ^ 3 = 1 → β * x = x * β →
          ∀ hx : x ∈ CFSG.GroupActions.subgroupStabAut K,
            centerQuotientHom ↥K (CFSG.GroupActions.subgroupStabRestrict K ⟨x, hx⟩) ∈
              innAutDerived (↥K ⧸ Subgroup.center ↥K)

theorem compIdxAt_of_mulEquiv {p : ℕ} {d : TauCeti.LieTypeIndex} {S S' : Type} [Group S]
    [Group S'] (e : S ≃* S') (h : CompIdxAt p d S) : CompIdxAt p d S' := by
  intro b hbmem hbp hb1 K' hK'
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ innAutDerived S := by
    rw [← mem_innAutDerived_congr e, hconj]
    exact hbmem
  have hαp : α ^ p = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconj]
    exact hbp
  have hα1 : α ≠ 1 := by
    intro h1
    apply hb1
    rw [← hconj, h1, map_one]
  set K : Subgroup S := K'.map (e.symm : S' →* S) with hK
  have hfix : (fixSubgroup b).map (e.symm : S' →* S) = fixSubgroup α := by
    rw [← hconj, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e α,
      Subgroup.map_map]
    simp
  have hKcomp : IsComponentOf K (fixSubgroup α) := by
    rw [← hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK'
  obtain ⟨i, ⟨φ⟩, hrel⟩ := h α hαmem hαp hα1 K hKcomp
  have hKmap : K.map (e : S →* S') = K' := by
    rw [hK, Subgroup.map_map]
    simp
  refine ⟨i, ⟨?_, hrel⟩⟩
  let ε : ↥K ≃* ↥K' :=
    (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
  exact ⟨(QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K') ε
    (Subgroup.map_center_eq ε)).symm.trans φ⟩

theorem compAlgAt_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : CompAlgAt S) : CompAlgAt S' := by
  intro b hbmem hb3 hb1 K' hK' idx hidx hK'iso x' hx'mem hx'3 hbx' hx'stab
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ innAutDerived S := by
    rw [← mem_innAutDerived_congr e, hconj]
    exact hbmem
  have hα3 : α ^ 3 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconj]
    exact hb3
  have hα1 : α ≠ 1 := by
    intro h1
    apply hb1
    rw [← hconj, h1, map_one]
  set K : Subgroup S := K'.map (e.symm : S' →* S) with hK
  have hfix : (fixSubgroup b).map (e.symm : S' →* S) = fixSubgroup α := by
    rw [← hconj, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e α,
      Subgroup.map_map]
    simp
  have hKcomp : IsComponentOf K (fixSubgroup α) := by
    rw [← hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK'
  have hKmap : K.map (e : S →* S') = K' := by
    rw [hK, Subgroup.map_map]
    simp
  let ε : ↥K ≃* ↥K' :=
    (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
  have hKiso : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie idx).Group) := by
    obtain ⟨φ⟩ := hK'iso
    exact ⟨(QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K') ε
      (Subgroup.map_center_eq ε)).trans φ⟩
  set ξ : MulAut S := MulAut.congr e.symm x' with hξ
  have hconjξ : MulAut.congr e ξ = x' := by
    rw [hξ]
    ext y
    simp [MulAut.congr_apply]
  have hξmem : ξ ∈ innAutDerived S := by
    rw [← mem_innAutDerived_congr e, hconjξ]
    exact hx'mem
  have hξ3 : ξ ^ 3 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconjξ]
    exact hx'3
  have hbξ : α * ξ = ξ * α := by
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul, hconj, hconjξ]
    exact hbx'
  have hξstab : ξ ∈ CFSG.GroupActions.subgroupStabAut K := by
    change K.map ξ.toMonoidHom = K
    rw [hK, Subgroup.map_map]
    have hcomp : ξ.toMonoidHom.comp (e.symm : S' →* S) =
        (e.symm : S' →* S).comp x'.toMonoidHom := by
      ext s'
      simp [hξ, MulAut.congr_apply]
    rw [hcomp, ← Subgroup.map_map, hx'stab]
  have hres := h α hαmem hα3 hα1 K hKcomp idx hidx hKiso ξ hξmem hξ3 hbξ hξstab
  have hα' : MulAut.congr ε (CFSG.GroupActions.subgroupStabRestrict K ⟨ξ, hξstab⟩) =
      CFSG.GroupActions.subgroupStabRestrict K' ⟨x', hx'stab⟩ := by
    ext k'
    obtain ⟨k, rfl⟩ : ∃ k, ε k = k' := ⟨ε.symm k', ε.apply_symm_apply k'⟩
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    simp [ε, Subgroup.coe_equivMapOfInjective_apply, MulEquiv.subgroupCongr_apply,
      CFSG.GroupActions.subgroupStabRestrict_apply, hξ, MulAut.congr_apply]
  have hnat := centerQuotientHom_congr ε (CFSG.GroupActions.subgroupStabRestrict K ⟨ξ, hξstab⟩)
  rw [hα'] at hnat
  rw [← hnat]
  exact (mem_innAutDerived_congr (QuotientGroup.congr (Subgroup.center ↥K)
    (Subgroup.center ↥K') ε (Subgroup.map_center_eq ε))).2 hres

@[expose] def LieCompIdx (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic → P d.1 →
    CompIdxAt p d.1 (TauCeti.CFSGIndex.lie d).Group

@[expose] def LieCompAlg (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → fieldSize d.1 = 8 →
    CompAlgAt (TauCeti.CFSGIndex.lie d).Group

private theorem kd264CompIdx_at
    {P : TauCeti.LieTypeIndex → Prop}
    (hL : LieSemisimpleCent) (hI : LieCompIdx P) (hA : LieCompAlg P)
    {d : TauCeti.ValidLieTypeIndex} (hd : P d.1) :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
      ∀ β : MulAut (TauCeti.CFSGIndex.lie d).Group,
        β ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group → β ^ p = 1 → β ≠ 1 →
        ∀ J : Subgroup (TauCeti.CFSGIndex.lie d).Group,
          GLAPComponent p (fixSubgroup β) J →
          ∃ i : TauCeti.CFSGIndex, Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧
            compRelC d.1 i ∧
            (p = 3 → ∀ e : TauCeti.ValidLieTypeIndex, i = .lie e →
              (∃ q : TauCeti.PrimePower, (e.1 = .A 1 q ∨ e.1 = .twistedA 2 q) ∧ q.card = 8) →
              fieldSize d.1 = 8 →
              ∀ x ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group, x ^ 3 = 1 → β * x = x * β →
                ∀ hx : x ∈ CFSG.GroupActions.subgroupStabAut J,
                  centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J ⟨x, hx⟩) ∈
                    innAutDerived (↥J ⧸ Subgroup.center ↥J)) := by
  intro p hp hp2 hpc β hβmem hβp hβ1 J hJ
  obtain ⟨hfin, hsimple⟩ := CFSG.Assembly.lie_finite_simple d
  haveI := hfin
  haveI := hsimple
  have hnc : ∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a :=
    exists_mul_ne_mul_of_glaPComponent hp hJ
  have hpil : PerfectInLayer β :=
    hL _ hsimple hnc d ⟨MulEquiv.refl _⟩ p hp hp2 hpc β hβp hβ1
  have hJle : J ≤ GLALayer (fixSubgroup β) :=
    hpil J hJ.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  have hJcomp : IsComponentOf J (fixSubgroup β) :=
    (glaPComponent_isComponent_of_le_layer hJ hJle).1
  obtain ⟨i, ⟨φ⟩, hrel⟩ := hI d p hp hp2 hpc hd β hβmem hβp hβ1 J hJcomp
  refine ⟨i, ⟨φ⟩, hrel, ?_⟩
  intro hp3 e hi he hfield x hxmem hx3 hβx hx
  subst hi
  have hβ3 : β ^ 3 = 1 := by rw [← hp3]; exact hβp
  exact hA d hd hfield β hβmem hβ3 hβ1 J hJcomp e he ⟨φ⟩ x hxmem hx3 hβx hx

theorem kd264CompIdx_of_families
    (hL : LieSemisimpleCent)
    (h1 : LieCompIdx isLinearIdx) (h2 : LieCompIdx isUnitaryIdx)
    (h3 : LieCompIdx isClassicalBCDIdx) (h4 : LieCompIdx isTrialityIdx)
    (h5 : LieCompIdx isExcUntwistedIdx) (h6 : LieCompIdx isExcTwistedIdx)
    (a1 : LieCompAlg isLinearIdx) (a2 : LieCompAlg isUnitaryIdx)
    (a3 : LieCompAlg isClassicalBCDIdx) (a4 : LieCompAlg isTrialityIdx)
    (a5 : LieCompAlg isExcUntwistedIdx) (a6 : LieCompAlg isExcTwistedIdx) :
    KD264CompIdx := by
  intro d p hp hp2 hpc β hβmem hβp hβ1 J hJ
  obtain ⟨e, hd⟩ := d
  cases e with
  | A n q =>
      exact kd264CompIdx_at (P := isLinearIdx) (d := ⟨.A n q, hd⟩)
        hL h1 a1 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | twistedA n q =>
      exact kd264CompIdx_at (P := isUnitaryIdx) (d := ⟨.twistedA n q, hd⟩)
        hL h2 a2 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | B n q =>
      exact kd264CompIdx_at (P := isClassicalBCDIdx) (d := ⟨.B n q, hd⟩)
        hL h3 a3 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | C n q =>
      exact kd264CompIdx_at (P := isClassicalBCDIdx) (d := ⟨.C n q, hd⟩)
        hL h3 a3 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | D n q =>
      exact kd264CompIdx_at (P := isClassicalBCDIdx) (d := ⟨.D n q, hd⟩)
        hL h3 a3 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | twistedD n q =>
      exact kd264CompIdx_at (P := isClassicalBCDIdx) (d := ⟨.twistedD n q, hd⟩)
        hL h3 a3 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | E6 q =>
      exact kd264CompIdx_at (P := isExcUntwistedIdx) (d := ⟨.E6 q, hd⟩)
        hL h5 a5 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | E7 q =>
      exact kd264CompIdx_at (P := isExcUntwistedIdx) (d := ⟨.E7 q, hd⟩)
        hL h5 a5 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | E8 q =>
      exact kd264CompIdx_at (P := isExcUntwistedIdx) (d := ⟨.E8 q, hd⟩)
        hL h5 a5 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | F4 q =>
      exact kd264CompIdx_at (P := isExcUntwistedIdx) (d := ⟨.F4 q, hd⟩)
        hL h5 a5 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | G2 q =>
      exact kd264CompIdx_at (P := isExcUntwistedIdx) (d := ⟨.G2 q, hd⟩)
        hL h5 a5 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | twistedE6 q =>
      exact kd264CompIdx_at (P := isExcTwistedIdx) (d := ⟨.twistedE6 q, hd⟩)
        hL h6 a6 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | trialityD4 q =>
      exact kd264CompIdx_at (P := isTrialityIdx) (d := ⟨.trialityD4 q, hd⟩)
        hL h4 a4 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | suzuki k =>
      exact kd264CompIdx_at (P := isExcTwistedIdx) (d := ⟨.suzuki k, hd⟩)
        hL h6 a6 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | reeG2 k =>
      exact kd264CompIdx_at (P := isExcTwistedIdx) (d := ⟨.reeG2 k, hd⟩)
        hL h6 a6 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | reeF4 k =>
      exact kd264CompIdx_at (P := isExcTwistedIdx) (d := ⟨.reeF4 k, hd⟩)
        hL h6 a6 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ
  | tits =>
      exact kd264CompIdx_at (P := isExcTwistedIdx) (d := ⟨.tits, hd⟩)
        hL h6 a6 trivial p hp hp2 hpc β hβmem hβp hβ1 J hJ

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

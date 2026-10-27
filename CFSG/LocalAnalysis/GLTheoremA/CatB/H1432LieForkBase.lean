module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {t : StatedLieTag} {n f : ℕ}

theorem outerLayerThree_congr {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : OuterLayerThree t n f X) : OuterLayerThree t n f X' := by
  rcases h with ⟨t', n', f', hs, hm⟩ | ⟨ht, hf, hc⟩
  · exact Or.inl ⟨t', n', f', hs, CFSG.Blueprint.LieModel.of_mulEquiv e hm⟩
  · exact Or.inr ⟨ht, hf, Nat.card_congr e.toEquiv ▸ hc⟩

theorem outerLayerThree_of_field {X : Type} [Group X] {f' : ℕ} (ht : t ≠ .trialityD4)
    (hf : 3 * f' = f) (hm : CFSG.Blueprint.LieModel X t n 3 f') : OuterLayerThree t n f X :=
  Or.inl ⟨t, n, f', Or.inl ⟨ht, rfl, rfl, hf⟩, hm⟩

theorem outerSubThree_of_mulEquiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    {D : Subgroup Y} {D' : Subgroup Y'} (e : ↥D ≃* ↥D') (h : OuterSubThree t n f D') :
    OuterSubThree t n f D := by
  intro A hA
  have h1 := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf Nat.prime_three (le_refl D) hA
  rw [Subgroup.subgroupOf_self] at h1
  have h2 := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_map_mulEquiv Nat.prime_three e h1
  rw [Subgroup.map_top_of_surjective _ e.surjective] at h2
  have h3 := CFSG.HardMathSupport.Solomon.Proving.lbUp_component_top_map Nat.prime_three D' h2
  let eA : ↥A ≃* ↥(((A.subgroupOf D).map e.toMonoidHom).map D'.subtype) :=
    (Subgroup.subgroupOfEquivOfLe hA.1).symm.trans
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (Subgroup.equivMapOfInjective _ D'.subtype D'.subtype_injective))
  exact outerLayerThree_congr (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3 eA).symm (h _ h3)

theorem outerSubThree_congr {P P' : Type} [Group P] [Finite P] [Group P'] (θ : P ≃* P')
    {ψ : MulAut P} (h : OuterSubThree t n f (fixSubgroup (MulAut.congr θ ψ))) :
    OuterSubThree t n f (fixSubgroup ψ) := by
  haveI : Finite P' := Finite.of_equiv P θ.toEquiv
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr θ ψ
  exact outerSubThree_of_mulEquiv
    ((Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)) h

theorem outerSubThree_conj {P : Type} [Group P] [Finite P] {ψ : MulAut P} (γ : MulAut P)
    (h : OuterSubThree t n f (fixSubgroup ψ)) :
    OuterSubThree t n f (fixSubgroup (γ * ψ * γ⁻¹)) := by
  refine outerSubThree_congr (show P ≃* P from γ⁻¹) (ψ := γ * ψ * γ⁻¹) ?_
  have : MulAut.congr (show P ≃* P from γ⁻¹) (γ * ψ * γ⁻¹) = ψ := by
    ext x
    simp [MulAut.congr_apply, MulAut.mul_apply]
  rwa [this]

theorem outerSubThree_of_conj {P : Type} [Group P] [Finite P] (γ ψ : MulAut P)
    (h : OuterSubThree t n f (fixSubgroup (γ * ψ * γ⁻¹))) :
    OuterSubThree t n f (fixSubgroup ψ) := by
  have h' := outerSubThree_conj γ⁻¹ h
  have e : γ⁻¹ * (γ * ψ * γ⁻¹) * (γ⁻¹)⁻¹ = ψ := by group
  rwa [e] at h'

theorem outerSubThree_inv_iff {P : Type} [Group P] (ψ : MulAut P) :
    OuterSubThree t n f (fixSubgroup ψ⁻¹) ↔ OuterSubThree t n f (fixSubgroup ψ) := by
  rw [CFSG.LocalAnalysis.GLTheoremA.I1431C2.fixSubgroup_inv_eq']

theorem outerSubThree_of_conj_pow {P : Type} [Group P] [Finite P] {β η δ : MulAut P} {r j : ℕ}
    (hrj : (β ^ r) ^ j = β) (hδ : δ * β ^ r * δ⁻¹ = η)
    (h : OuterSubThree t n f (fixSubgroup η)) : OuterSubThree t n f (fixSubgroup β) := by
  have h1 := outerSubThree_conj δ⁻¹ h
  have h2 : δ⁻¹ * η * δ⁻¹⁻¹ = β ^ r := by
    rw [← hδ]
    group
  rwa [h2, CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2.fixSubgroup_pow_eq_of_pow_pow_up34 hrj]
    at h1

theorem outerSubThree_of_simple_normal_comm {Y : Type} [Group Y] [Finite Y] {D S : Subgroup Y}
    (hSle : S ≤ D) (hcomm : ⁅D, D⁆ ≤ S) (hs : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hS : OuterLayerThree t n f ↥S) :
    OuterSubThree t n f D := by
  intro A hA
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I1431C2.psimple_equiv_of_simple_normal_comm hSle hcomm hs hnab
      hA
  exact outerLayerThree_congr e.symm hS

theorem outerSubThree_of_fixed_equiv {Y : Type} [Group Y] [Finite Y] (D : Subgroup Y) {X : Type}
    [Group X] (e : ↥D ≃* X) (hs : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a)
    (hX : OuterLayerThree t n f X) : OuterSubThree t n f D := by
  haveI : IsSimpleGroup ↥D := e.isSimpleGroup
  refine outerSubThree_of_simple_normal_comm (S := D) le_rfl ?_ inferInstance ?_
    (outerLayerThree_congr e.symm hX)
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩

theorem outerSubThree_of_solvable {Y : Type} [Group Y] [Finite Y] (D : Subgroup Y)
    (hD : Group.IsSolvable ↥D) : OuterSubThree t n f D := by
  intro A hA
  haveI : Group.IsSolvable ↥A :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hA.1)
  haveI : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr (glaPComponent_perfect hA)
  haveI : Nontrivial ↥A :=
    (Subgroup.nontrivial_iff_ne_bot A).mpr (Lemma510Ns.glaPComponent_ne_bot hA)
  exact (Group.IsPerfect.not_isSolvable ↥A inferInstance).elim

theorem outerSubThree_of_card_dvd {Y : Type} [Group Y] [Finite Y] (D : Subgroup Y)
    (hD : Nat.card ↥D ∣ 1512) : OuterSubThree .twistedG2 n 3 D := by
  intro A hA
  refine Or.inr ⟨rfl, rfl, ?_⟩
  have hc1 : Nat.card (PSimple 3 A) ∣ Nat.card (PQuot 3 A) := Subgroup.card_quotient_dvd_card _
  have hc2 : Nat.card (PQuot 3 A) ∣ Nat.card ↥A := Subgroup.card_quotient_dvd_card _
  exact hc1.trans (hc2.trans ((Subgroup.card_dvd_of_le hA.1).trans hD))

end CFSG.LocalAnalysis.GLTheoremA.H1420

end

module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def FixCompsEquiv {S : Type} [Group S] (β : MulAut S) (T : Type) [Group T] : Prop :=
  ∀ J : Subgroup S, IsComponentOf J (fixSubgroup β) → Nonempty (↥J ≃* T)

namespace FixCompsEquiv

variable {S S' T : Type} [Group S] [Group S'] [Group T]

theorem of_fixSubgroup_eq {α γ : MulAut S} (h : fixSubgroup α = fixSubgroup γ)
    (hα : FixCompsEquiv α T) : FixCompsEquiv γ T :=
  fun J hJ => hα J (h ▸ hJ)

theorem of_pow_pow {β : MulAut S} {r s : ℕ} (h : (β ^ r) ^ s = β)
    (hr : FixCompsEquiv (β ^ r) T) : FixCompsEquiv β T :=
  of_fixSubgroup_eq
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_pow_eq_of_pow_pow' h) hr

theorem of_congr (e : S ≃* S') {β : MulAut S} (h : FixCompsEquiv (MulAut.congr e β) T) :
    FixCompsEquiv β T := by
  intro J hJ
  have hJ' : IsComponentOf (J.map (e : S →* S')) (fixSubgroup (MulAut.congr e β)) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJ
  obtain ⟨f⟩ := h _ hJ'
  exact ⟨(J.equivMapOfInjective (e : S →* S') e.injective).trans f⟩

theorem of_conj (γ : MulAut S) {β : MulAut S} (h : FixCompsEquiv (γ * β * γ⁻¹) T) :
    FixCompsEquiv β T := by
  refine of_congr (γ : S ≃* S) ?_
  have hc : MulAut.congr (γ : S ≃* S) β = γ * β * γ⁻¹ := by
    ext x
    rfl
  rw [hc]
  exact h

theorem center_eq_bot {β : MulAut S} (h : FixCompsEquiv β T) (hT : Subgroup.center T = ⊥)
    {J : Subgroup S} (hJ : IsComponentOf J (fixSubgroup β)) : Subgroup.center ↥J = ⊥ := by
  obtain ⟨f⟩ := h J hJ
  have h1 : (Subgroup.center ↥J).map (f : ↥J →* T) = Subgroup.center T := Subgroup.map_center_eq f
  rw [hT] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective (f := (f : ↥J →* T)) _ f.injective).mp h1

end FixCompsEquiv

variable {S T : Type} [Group S] [Finite S] [Group T]

theorem fixCompsEquiv_of_normal_quasisimple {β : MulAut S} {N : Subgroup S}
    (hNC : N ≤ fixSubgroup β) [(N.subgroupOf (fixSubgroup β)).Normal]
    (hNq : CFSG.IsQuasisimple ↥N)
    (hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ N.subgroupOf (fixSubgroup β)))
    (e : ↥N ≃* T) : FixCompsEquiv β T := by
  have hNc : IsComponentOf N (fixSubgroup β) :=
    ⟨hNC, CFSG.Open.IsSubnormal.step hNC inferInstance (CFSG.Open.IsSubnormal.refl _),
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hNq⟩
  intro J hJ
  obtain rfl := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.eq_of_isComponentOf_of_perfect_le
    hNc (fun P hPC hP =>
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient hNC
        hsol hPC hP) hJ
  exact ⟨e⟩

theorem fixCompsEquiv_of_normal_simple {β : MulAut S} {N : Subgroup S}
    (hNC : N ≤ fixSubgroup β) [(N.subgroupOf (fixSubgroup β)).Normal] (hs : IsSimpleGroup ↥N)
    (hnc : ∃ a b : ↥N, a * b ≠ b * a)
    (hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ N.subgroupOf (fixSubgroup β)))
    (e : ↥N ≃* T) : FixCompsEquiv β T :=
  fixCompsEquiv_of_normal_quasisimple hNC
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc)
    hsol e

theorem fixCompsEquiv_of_derived_eq_simple {β : MulAut S} {N : Subgroup S}
    (hder : ⁅fixSubgroup β, fixSubgroup β⁆ = N) (hs : IsSimpleGroup ↥N)
    (hnc : ∃ a b : ↥N, a * b ≠ b * a) (e : ↥N ≃* T) : FixCompsEquiv β T := by
  have hNC : N ≤ fixSubgroup β := by
    rw [← hder]
    exact Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact (fixSubgroup β).mul_mem ((fixSubgroup β).mul_mem ((fixSubgroup β).mul_mem ha hb)
        ((fixSubgroup β).inv_mem ha)) ((fixSubgroup β).inv_mem hb)
  haveI hNn : (N.subgroupOf (fixSubgroup β)).Normal := by
    rw [← hder]
    have h := Subgroup.normal_subgroupOf_commutator_sup (fixSubgroup β) (fixSubgroup β)
    rwa [sup_idem] at h
  have hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ N.subgroupOf (fixSubgroup β)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      ← hder]
    have e' : (((x * y)⁻¹ * (y * x) : ↥(fixSubgroup β)) : S) =
        ⁅((y⁻¹ : ↥(fixSubgroup β)) : S), ((x⁻¹ : ↥(fixSubgroup β)) : S)⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [e']
    exact Subgroup.commutator_mem_commutator (y⁻¹).2 (x⁻¹).2
  exact fixCompsEquiv_of_normal_simple hNC hs hnc hsol e

end CFSG.LocalAnalysis.GLTheoremA.S2019

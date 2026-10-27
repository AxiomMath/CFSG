module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOnePerfect

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.ComponentClassification.M12Cover
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.TwoCo1.HypOne
open scoped commutatorElement

theorem mem_commutator_centralizer_of_isConj' {Y : Type*} [Group Y] {w r : Y} (h : IsConj w r)
    (hr : r ∈ ⁅centralizer ({r} : Set Y), centralizer ({r} : Set Y)⁆) :
    w ∈ ⁅centralizer ({w} : Set Y), centralizer ({w} : Set Y)⁆ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hw : w = c⁻¹ * r * c := by rw [← hc]; group
  set f : Y →* Y := (MulAut.conj c⁻¹).toMonoidHom with hf
  have hfr : f r = w := by
    show c⁻¹ * r * c⁻¹⁻¹ = w
    rw [hw]
    group
  have hmap : (centralizer ({r} : Set Y)).map f ≤ centralizer ({w} : Set Y) := by
    rintro _ ⟨y, hy, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have hy' : y * r = r * y := mem_centralizer_singleton_iff.1 hy
    show c⁻¹ * y * c⁻¹⁻¹ * w = w * (c⁻¹ * y * c⁻¹⁻¹)
    calc c⁻¹ * y * c⁻¹⁻¹ * w = c⁻¹ * (y * r) * c := by rw [hw]; group
      _ = c⁻¹ * (r * y) * c := by rw [hy']
      _ = w * (c⁻¹ * y * c⁻¹⁻¹) := by rw [hw]; group
  have h2 := mem_map_of_mem f hr
  rw [hfr, map_commutator] at h2
  exact commutator_mono hmap hmap h2

theorem PerfectInvolutions.transport {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : PerfectInvolutions X) : PerfectInvolutions Y := by
  intro w hw
  have hw' : orderOf (e.symm w) = 2 :=
    (orderOf_injective e.symm.toMonoidHom e.symm.injective w).trans hw
  have h1 := h (e.symm w) hw'
  have hmap : (centralizer ({e.symm w} : Set X)).map e.toMonoidHom ≤
      centralizer ({w} : Set Y) := by
    rintro _ ⟨y, hy, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have hy' : y * e.symm w = e.symm w * y := mem_centralizer_singleton_iff.1 hy
    have := congrArg e.toMonoidHom hy'
    simpa using this
  have h2 := mem_map_of_mem e.toMonoidHom h1
  rw [map_commutator] at h2
  have := commutator_mono hmap hmap h2
  simpa using this

theorem mem_commutator_centralizer_of_comm_pair {Y : Type*} [Group Y] {a x y : Y}
    (hx : x * a = a * x) (hy : y * a = a * y) (hxy : x * y = a * (y * x)) :
    a ∈ ⁅centralizer ({a} : Set Y), centralizer ({a} : Set Y)⁆ := by
  have h := commutator_mem_commutator (mem_centralizer_singleton_iff.2 hx)
    (mem_centralizer_singleton_iff.2 hy)
  have e : ⁅x, y⁆ = a := by
    rw [commutatorElement_def]
    calc x * y * x⁻¹ * y⁻¹ = a * (y * x) * x⁻¹ * y⁻¹ := by rw [hxy]
      _ = a := by group
  rwa [e] at h

theorem le_commutator_of_commutator_eq_top {Y : Type*} [Group Y] {H : Subgroup Y}
    (h : commutator H = ⊤) : H ≤ ⁅H, H⁆ := by
  intro x hx
  have h1 : (⟨x, hx⟩ : H) ∈ commutator H := by rw [h]; trivial
  have h2 := mem_map_of_mem H.subtype h1
  rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2

end CFSG.EvenSporadicStandard.Solomon78

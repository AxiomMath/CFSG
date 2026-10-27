module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinM22
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinOutC

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG FinGlue
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer inner_normal)

namespace FinOut

theorem noPerfLocal_mulAut {Y : Type} [Group Y] [Finite Y] (hc : center Y = ⊥)
    (h : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) (hY : NoPerfLocal Y) : NoPerfLocal (MulAut Y) := by
  intro p hp hp2 X I hX hX1 hI1 hI hIX
  have hInj := conj_injective_of_center' hc
  have : (inner Y).Normal := inner_normal Y
  have hfin : Finite (MulAut Y) :=
    Finite.of_injective (fun α : MulAut Y => (α : Y → Y)) DFunLike.coe_injective
  have hO := card_outer_le hc h
  let π : MulAut Y →* Outer Y := QuotientGroup.mk' (inner Y)
  have hker : ∀ φ : MulAut Y, π φ = 1 ↔ φ ∈ inner Y := fun φ => QuotientGroup.eq_one_iff φ
  have hcomm : ∀ a b : Outer Y, a * b = b * a := by
    have := FinM22.isCyclic_outer hc h
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Outer Y)
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    exact ((Commute.refl g).zpow_zpow i j).eq
  have hIinn : I ≤ inner Y := by
    rw [← hI, Subgroup.commutator_le]
    intro a _ b _
    rw [← hker, map_commutatorElement, commutatorElement_def, hcomm (π a) (π b)]
    group
  have hXinn : X ≤ inner Y := by
    intro x hx
    rw [← hker]
    obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
    have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf (π x) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxk, map_one])
    have h2 : orderOf (π x) ∣ Nat.card (Outer Y) := orderOf_dvd_natCard _
    have h3 : orderOf (π x) ≤ 2 := (Nat.le_of_dvd Nat.card_pos h2).trans hO
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 h1
    rcases j with _ | j
    · rw [pow_zero] at hj'
      exact orderOf_eq_one_iff.mp hj'
    · have : p ≤ p ^ (j + 1) := Nat.le_self_pow (by omega) p
      have := hp.two_le
      omega
  have hmapX : (X.comap (MulAut.conj : Y →* MulAut Y)).map MulAut.conj = X :=
    Subgroup.map_comap_eq_self hXinn
  have hmapI : (I.comap (MulAut.conj : Y →* MulAut Y)).map MulAut.conj = I :=
    Subgroup.map_comap_eq_self hIinn
  refine hY p hp hp2 (X.comap MulAut.conj) (I.comap MulAut.conj)
    (hX.comap_of_injective _ hInj) (fun hb => hX1 ?_) (fun hb => hI1 ?_) ?_ ?_
  · rw [← hmapX, hb, Subgroup.map_bot]
  · rw [← hmapI, hb, Subgroup.map_bot]
  · apply Subgroup.map_injective hInj
    rw [Subgroup.map_commutator, hmapI, hI]
  · intro g hg
    rw [mem_normalizer_iff]
    intro y
    have hgN := mem_normalizer_iff.mp (hIX hg) (MulAut.conj y)
    simp only [Subgroup.mem_comap, map_mul, map_inv]
    exact hgN

end FinOut

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

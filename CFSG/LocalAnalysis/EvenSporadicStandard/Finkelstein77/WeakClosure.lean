module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77

open Subgroup CFSG.Assembly.ComponentType CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type*} [Group G]

theorem normalizer_zpowers_le [Finite G] {L : Subgroup G} (hL : IsStandardSubgroup L) {x : G}
    (hxC : x ∈ centralizer (L : Set G)) (hx : Even (orderOf x)) :
    normalizer ((zpowers x : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨-, -, -, hNC, -⟩ := id hL
  intro n hn
  have hZC : zpowers x ≤ centralizer (L : Set G) := zpowers_le.mpr hxC
  have h1 : x ∈ (centralizer (L : Set G)).map (MulAut.conj (1 : G)).toMonoidHom := by
    rw [mem_conj_iff]
    simpa using hxC
  have h2 : x ∈ (centralizer (L : Set G)).map (MulAut.conj n).toMonoidHom := by
    rw [mem_conj_iff]
    have h := (mem_normalizer_iff.mp (inv_mem hn) x).mp (mem_zpowers x)
    simpa using hZC h
  have h3 := mem_normalizer_of_even_orderOf_mem hL hx h1 h2
  rw [hNC] at h3
  simpa using h3

theorem weaklyClosed_zpowers [Finite G] {L : Subgroup G} (hL : IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G))) (hS : IsCyclic S)
    (hall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
        IsPGroup 2 P → Nat.card P ≤ 2)
    {x : G} (hxC : x ∈ centralizer (L : Set G)) (hx : orderOf x = 4) :
    WeaklyClosedInNormalizer (zpowers x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hNC, -⟩ := id hL
  intro h hh
  set Z : Subgroup G := zpowers x with hZdef
  set Zh : Subgroup G := Z.map (MulAut.conj h).toMonoidHom with hZhdef
  have hZC : Z ≤ centralizer (L : Set G) := zpowers_le.mpr hxC
  have hZcard : Nat.card Z = 4 := by rw [hZdef, Nat.card_zpowers, hx]
  have hZp : IsPGroup 2 Z := IsPGroup.of_card (n := 2) (by rw [hZcard]; norm_num)
  have hZhcard : Nat.card Zh = 4 := (card_map_conj Z h).trans hZcard
  have hZhp : IsPGroup 2 Zh := hZp.map _
  have hZN : normalizer (Z : Set G) ≤ normalizer (L : Set G) :=
    normalizer_zpowers_le hL hxC (by rw [hx]; exact ⟨2, rfl⟩)
  have hhN : h ∈ normalizer (L : Set G) := by
    by_contra hhN
    have := hall h hhN Zh (le_inf (Subgroup.map_mono hZC) (hh.trans hZN)) hZhp
    omega
  have hCh : (centralizer (L : Set G)).map (MulAut.conj h).toMonoidHom = centralizer (L : Set G) :=
    map_conj_eq_of_mem_normalizer (by rw [hNC]; exact hhN)
  have hZhC : Zh ≤ centralizer (L : Set G) := (Subgroup.map_mono hZC).trans hCh.le
  have hPp : IsPGroup 2 (Z ⊔ Zh : Subgroup G) := hZp.to_sup_of_normal_left' hZhp hh
  have hPC : Z ⊔ Zh ≤ centralizer (L : Set G) := sup_le hZC hZhC
  have hcyc : IsCyclic (Z ⊔ Zh : Subgroup G) := (isCyclic_and_card_le_of_le S hS hPC hPp).1
  have hsub : Z.subgroupOf (Z ⊔ Zh) = Zh.subgroupOf (Z ⊔ Zh) := by
    apply IsCyclic.subgroup_eq_iff_card_eq.mpr
    rw [Nat.card_congr (subgroupOfEquivOfLe (le_sup_left : Z ≤ Z ⊔ Zh)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : Zh ≤ Z ⊔ Zh)).toEquiv, hZcard,
      hZhcard]
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr le_sup_left, inf_eq_left.mpr le_sup_right] at hsub
  exact hsub.symm

end CFSG.EvenSporadicStandard.Finkelstein77

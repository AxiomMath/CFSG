module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAEichSq
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.ZStabFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {ι : Elem2 6 →* G} {w u : V6} {x y k z : G}

private theorem v6_add_self (v : V6) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private lemma coordElt_injective (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

@[expose] def Cgrp (ι : Elem2 6 →* G) (w : V6) : Subgroup G where
  carrier := {x | ∃ v : V6, bil v w = 0 ∧ coordElt ι v = x}
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
    exact ⟨v + v', by rw [bil_add_left, hv, hv', add_zero], coordElt_add ι v v'⟩
  one_mem' := ⟨0, bil_zero_left w, coordElt_zero ι⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    have hmul : coordElt ι v * coordElt ι v = 1 := by
      rw [← coordElt_add, v6_add_self v, coordElt_zero]
    exact (inv_eq_of_mul_eq_one_right hmul).symm

theorem mem_Cgrp : x ∈ Cgrp ι w ↔ ∃ v : V6, bil v w = 0 ∧ coordElt ι v = x := Iff.rfl

theorem coordElt_mem_Cgrp (hι : Function.Injective ι) {v : V6} :
    coordElt ι v ∈ Cgrp ι w ↔ bil v w = 0 := by
  constructor
  · rintro ⟨v', hv', heq⟩
    rw [← coordElt_injective hι heq]
    exact hv'
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem Cgrp_le_range : Cgrp ι w ≤ ι.range := by
  rintro x ⟨v, -, rfl⟩
  exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd v, rfl⟩

theorem Cgrp_sq (hx : x ∈ Cgrp ι w) : x ^ 2 = 1 := by
  rcases hx with ⟨v, -, rfl⟩
  rw [pow_two, ← coordElt_add, v6_add_self v, coordElt_zero]

theorem Cgrp_mul_comm (hx : x ∈ Cgrp ι w) (hy : y ∈ Cgrp ι w) : x * y = y * x := by
  rcases hx with ⟨v, -, rfl⟩
  rcases hy with ⟨v', -, rfl⟩
  rw [← coordElt_add, ← coordElt_add, add_comm]

theorem card_Cgrp (hι : Function.Injective ι) (hw0 : w ≠ 0) : Nat.card (Cgrp ι w) = 32 := by
  classical
  let f : {v : V6 // bil v w = 0} → ↥(Cgrp ι w) :=
    fun v => ⟨coordElt ι v.1, ⟨v.1, v.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Subtype.ext (coordElt_injective hι (congrArg Subtype.val hab))
    · rintro ⟨x, hx⟩
      rcases hx with ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  calc Nat.card (Cgrp ι w) = Nat.card {v : V6 // bil v w = 0} :=
        (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = (Finset.univ.filter fun v : V6 => bil v w = 0).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = 32 := card_perp hw0

theorem Cgrp_conj {g : Equiv.Perm V6} (hk : Acts ι k g) (hg : g ∈ OrthMinus) (hgw : g w = w)
    (hx : x ∈ Cgrp ι w) : k * x * k⁻¹ ∈ Cgrp ι w := by
  rcases hx with ⟨v, hv, rfl⟩
  refine ⟨g v, ?_, (hk v).symm⟩
  have h := bil_apply_of_mem_orthOf isQF_qm hg v w
  rw [hgw, hv] at h
  exact h

@[expose] def IsRCand (ι : Elem2 6 →* G) (z : G) (w : V6) (x : G) (u : V6) : Prop :=
  EichActs ι w x u ∧ x ^ 2 ∈ zpowers z ∧ (x ∈ ι.range → x ∈ Cgrp ι w)

theorem IsRCand.one (z : G) (w : V6) : IsRCand ι z w (1 : G) 0 := by
  refine ⟨EichActs.one w, ?_, fun _ => one_mem _⟩
  rw [one_pow]
  exact one_mem _

theorem IsRCand.inv (hx : IsRCand ι z w x u) : IsRCand ι z w x⁻¹ u := by
  refine ⟨hx.1.inv, ?_, ?_⟩
  · rw [inv_pow]
    exact inv_mem hx.2.1
  · intro hxinv
    have hxr : x ∈ ι.range := by simpa using inv_mem hxinv
    exact inv_mem (hx.2.2 hxr)

theorem IsRCand.conj {g : Equiv.Perm V6} (hk : Acts ι k g) (hg : g ∈ OrthMinus) (hgw : g w = w)
    (hz : k * z * k⁻¹ = z) (hx : IsRCand ι z w x u) : IsRCand ι z w (k * x * k⁻¹) (g u) := by
  refine ⟨hx.1.conj hk hg hgw, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx.2.1
    have hsq : (k * x * k⁻¹) ^ 2 = k * x ^ 2 * k⁻¹ := by
      rw [pow_two, pow_two]
      group
    have hzk : k * z ^ m * k⁻¹ = z ^ m := by
      rw [← conj_zpow (a := k) (b := z) (i := m), hz]
    rw [hsq, ← hm, hzk]
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩
  · intro hin
    have hkn : k ∈ normalizer (ι.range : Set G) := hk.mem_normalizer
    rw [Subgroup.mem_set_normalizer_iff] at hkn
    have hxr : x ∈ ι.range := (hkn x).mpr hin
    exact Cgrp_conj hk hg hgw (hx.2.2 hxr)

end CFSG.EvenSporadicStandard.HNRecog.Harada

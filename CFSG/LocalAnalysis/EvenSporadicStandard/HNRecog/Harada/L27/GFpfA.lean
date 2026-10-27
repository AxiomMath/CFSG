module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GV6
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAComp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.Harada

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} {n : G}

private lemma coordElt_injective {G : Type*} [Group G] {ι : Elem2 6 →* G}
    (hι : Function.Injective ι) : Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

private theorem add_self_eq_zero_V6 (x : V6) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

theorem mem_zpowers_of_order_five (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) {f : G}
    (hf : f ∈ Fconj n F) (hf5 : orderOf f = 5) {x : G} (hxC : x ∈ Cgrp ι zv)
    (hfx : f * x * f⁻¹ * x⁻¹ ∈ zpowers z) : x ∈ zpowers z := by
  have hfK : f ∈ Kgrp ι z := Fconj_le_K h hn hnz hf
  obtain ⟨g, hgOm, hgz, hgActs⟩ := h.exists_acts_of_mem_K hfK
  have hg : IsAddPerm g := Acts.isAddPerm h.injective_ι hgActs
  have hpow : ∀ k : ℕ, Acts ι (f ^ k) (g ^ k) := by
    intro k
    induction k with
    | zero => simpa using (acts_one : Acts ι (1 : G) (1 : Equiv.Perm V6))
    | succ k ih => simpa [pow_succ] using ih.mul hgActs
  have hf5pow : f ^ 5 = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf5] at this
  have h5 : g ^ 5 = 1 := by
    have hAct5 : Acts ι (1 : G) (g ^ 5) := by
      have := hpow 5
      rwa [hf5pow] at this
    exact (Acts.unique h.injective_ι (n := 1) acts_one hAct5).symm
  have h1 : g ≠ 1 := by
    intro hg1
    have hActs1 : Acts ι f 1 := by rwa [hg1] at hgActs
    have hfrange : f ∈ ι.range := Acts.mem_range_of_one h.centralizer_le hActs1
    have hfinf : f ∈ Fconj n F ⊓ ι.range := ⟨hf, hfrange⟩
    rw [Fconj_inf_range h hn] at hfinf
    have hf1 : f = 1 := Subgroup.mem_bot.mp hfinf
    rw [hf1, orderOf_one] at hf5
    exact absurd hf5 (by norm_num)
  obtain ⟨av, hav⟩ := MonoidHom.mem_range.mp (conj_t_mem_range h hn)
  let vv : V6 := Multiplicative.toAdd av
  have hvv : coordElt ι vv = n * t * n⁻¹ := by
    simpa [coordElt, vv] using hav
  have hfv : f * (n * t * n⁻¹) * f⁻¹ = n * t * n⁻¹ := by
    rw [← conj_t_comm_Fconj h hf]
    group
  have hv : g vv = vv := by
    apply coordElt_injective h.injective_ι
    have hActvv : f * (n * t * n⁻¹) * f⁻¹ = coordElt ι (g vv) := by
      have := hgActs vv
      rwa [hvv] at this
    rw [← hActvv, hfv, hvv]
  have hzv : bil vv zv = 1 := by
    have hne : bil vv zv ≠ 0 := by
      intro h0
      apply conj_t_not_mem_Cgrp h hn hnz
      rw [← hvv]
      exact (coordElt_mem_Cgrp h.injective_ι).mpr h0
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h01 (bil vv zv) with hh | hh
    · exact absurd hh hne
    · exact hh
  obtain ⟨a, ha0, hax⟩ := mem_Cgrp.mp hxC
  have hsq : coordElt ι a * coordElt ι a = 1 := by
    rw [← coordElt_add, add_self_eq_zero_V6 a, coordElt_zero]
  have hinv : (coordElt ι a)⁻¹ = coordElt ι a := inv_eq_of_mul_eq_one_right hsq
  have hprod : f * x * f⁻¹ * x⁻¹ = coordElt ι (g a + a) := by
    rw [← hax, hgActs a, hinv, ← coordElt_add]
  have hmem : coordElt ι (g a + a) ∈ zpowers z := by
    rw [hprod] at hfx
    exact hfx
  have hgu : g a + a = 0 ∨ g a + a = zv := by
    have hord : orderOf z = 2 := orderOf_eq_prime h.z_sq h.z_ne_one
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← zpow_mod_orderOf z k, hord] at hk
    norm_num only [Nat.cast_ofNat] at hk
    rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
    · left
      apply coordElt_injective h.injective_ι
      rw [coordElt_zero, ← hk, hk2, zpow_zero]
    · right
      apply coordElt_injective h.injective_ι
      rw [h.coord_z, ← hk, hk2, zpow_one]
  have ha : a = 0 ∨ a = zv := V6_fixed_zv_perp hg h5 h1 hgz hv hzv ha0 hgu
  rcases ha with ha0' | hazv
  · rw [← hax, ha0', coordElt_zero]
    exact one_mem _
  · rw [← hax, hazv, h.coord_z]
    exact Subgroup.mem_zpowers z

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27

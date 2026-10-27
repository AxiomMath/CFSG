module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Defs
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017LyFive

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5

open CFSG.Open

variable {X : Type} [Group X]

private def omegaZ (R : Subgroup X) (S : Set X) : Subgroup X where
  carrier := {w | w ∈ R ∧ (∀ r ∈ R, Commute w r) ∧ w ^ 2 = 1 ∧ ∀ s ∈ S, Commute w s}
  mul_mem' := by
    rintro a b ⟨haR, haZ, ha2, haS⟩ ⟨hbR, hbZ, hb2, hbS⟩
    exact ⟨R.mul_mem haR hbR, fun r hr => (haZ r hr).mul_left (hbZ r hr),
      by rw [(haZ _ hbR).mul_pow, ha2, hb2, one_mul], fun s hs => (haS s hs).mul_left (hbS s hs)⟩
  one_mem' := ⟨R.one_mem, fun r _ => Commute.one_left r, one_pow 2, fun s _ => Commute.one_left s⟩
  inv_mem' := by
    rintro a ⟨haR, haZ, ha2, haS⟩
    exact ⟨R.inv_mem haR, fun r hr => (haZ r hr).inv_left, by rw [inv_pow, ha2, inv_one],
      fun s hs => (haS s hs).inv_left⟩

private theorem le_normalizer_omegaZ {R E : Subgroup X} {S : Set X}
    (hER : E ≤ Subgroup.normalizer (R : Set X)) (hES : ∀ e ∈ E, ∀ s ∈ S, Commute e s) :
    E ≤ Subgroup.normalizer (omegaZ R S : Set X) := by
  have key : ∀ e ∈ E, ∀ w ∈ omegaZ R S, e * w * e⁻¹ ∈ omegaZ R S := by
    rintro e he w ⟨hwR, hwZ, hw2, hwS⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hER he) w).1 hwR, fun r hr => ?_,
      by rw [conj_pow, hw2, mul_one, mul_inv_cancel],
      fun s hs => ((hES e he s hs).mul_left (hwS s hs)).mul_left (hES e he s hs).inv_left⟩
    have hr' : e⁻¹ * r * e ∈ R := by
      simpa using (Subgroup.mem_normalizer_iff.1 (hER (E.inv_mem he)) r).1 hr
    show e * w * e⁻¹ * r = r * (e * w * e⁻¹)
    calc e * w * e⁻¹ * r = e * (w * (e⁻¹ * r * e)) * e⁻¹ := by group
      _ = r * (e * w * e⁻¹) := by rw [(hwZ _ hr').eq]; group
  intro e he
  refine Subgroup.mem_normalizer_iff.2 fun w => ⟨key e he w, fun hw => ?_⟩
  simpa [mul_assoc] using key e⁻¹ (E.inv_mem he) _ hw

theorem twoLocalRankCriterion_holds : TwoLocalRankCriterion := by
  intro X _ _ p k m hp hp2 hm h1 h2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine glaTwoLocalRank_le_of_card_le hp fun R E hR hR2 hER hE => ?_
  by_contra hlt
  push Not at hlt
  have hEne : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hlt
    exact absurd hlt (not_lt.2 (Nat.one_le_pow _ _ hp.pos))
  have hW2 : ∀ S, IsPGroup 2 (omegaZ R S) := fun S => hR2.to_le fun _ hw => hw.1
  obtain ⟨t, htW, ht1⟩ : ∃ t ∈ omegaZ R ∅, t ≠ 1 := by
    haveI : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hR
    obtain ⟨n, hn0, hn⟩ :=
      (hR2.to_subgroup (Subgroup.center R)).nontrivial_iff_card.1 hR2.center_nontrivial
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R) 2
      (by rw [hn]; exact dvd_pow_self 2 hn0.ne')
    have hz2 : orderOf ((z : R) : X) = 2 := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    refine ⟨((z : R) : X), ⟨(z : R).2, fun r hr => ?_, by rw [← hz2, pow_orderOf_eq_one],
      fun s hs => absurd hs (Set.notMem_empty s)⟩, fun h => ?_⟩
    · exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨r, hr⟩)).symm
    · rw [h, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
  have hW₀p : ¬ p ∣ Nat.card (omegaZ R ∅) := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (hW2 ∅)
    rw [hj]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨B, hB, x, hxW₀, hx1, hBx⟩ := exists_hyperplane_fixed_p hp hE hEne hW₀p
    (fun h => ht1 ((Subgroup.mem_bot).1 (h ▸ htW)))
    (le_normalizer_omegaZ (S := ∅) hER fun _ _ s hs => absurd hs (Set.notMem_empty s))
  set F : Subgroup X := B.map E.subtype with hFdef
  have hFE : F ≤ E := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hFab : IsElemAbelian p F := hE.mono hFE
  have hxW : x ∈ omegaZ R F := ⟨hxW₀.1, hxW₀.2.1, hxW₀.2.2.1, by
    rintro _ ⟨b, hb, rfl⟩
    exact (hBx b hb).symm⟩
  have hFW : F ≤ Subgroup.centralizer (omegaZ R F : Set X) := fun f hf =>
    Subgroup.mem_centralizer_iff.2 fun w hw => (hw.2.2.2 f hf).eq
  have hFk : Nat.card F = p ^ k := by
    have hle := h1 x (orderOf_eq_prime hxW₀.2.2.1 hx1) F
      (hFW.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxW))) hFab
    have hFcard : Nat.card F * p = Nat.card E := by
      rw [hFdef, Subgroup.card_map_of_injective E.subtype_injective, ← hB]
      exact Subgroup.card_mul_index B
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1
      (show IsPGroup p F from fun g => ⟨1, Subtype.ext (by simpa using hFab.2 g g.2)⟩)
    rw [hj] at hle hFcard ⊢
    have hjk : j ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
    have hkj : k < j + 1 :=
      (Nat.pow_lt_pow_iff_right hp.one_lt).1 (by rw [pow_succ, hFcard]; exact hlt)
    rw [show j = k by omega]
  have hEW := le_normalizer_omegaZ (S := F) hER fun e he s hs =>
    congrArg Subtype.val (hE.1.1.comm ⟨e, he⟩ ⟨s, hFE hs⟩)
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer E (omegaZ R F) hEW
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  have hmod := hEp.card_modEq_card_fixedPoints (omegaZ R F)
  by_cases hfix : ∃ w : omegaZ R F, w ≠ 1 ∧ w ∈ MulAction.fixedPoints E (omegaZ R F)
  ·
    obtain ⟨w, hw1, hwfix⟩ := hfix
    refine absurd (h1 w (orderOf_eq_prime w.2.2.2.1 fun h => hw1 (Subtype.ext h)) E
      (fun e he => Subgroup.mem_centralizer_singleton_iff.2 ?_) hE) (not_le.2 hlt)
    have h := congrArg Subtype.val (hwfix ⟨e, he⟩)
    change e * (w : X) * e⁻¹ = w at h
    exact mul_inv_eq_iff_eq_mul.1 h
  ·
    push Not at hfix
    have hone : Nat.card (MulAction.fixedPoints E (omegaZ R F)) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨1, fun e => smul_one e⟩, fun ⟨w, hw⟩ => ?_⟩
      by_contra hne
      exact hfix w (fun h => hne (Subtype.ext h)) hw
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hW2 F)
    rw [hone, hn] at hmod
    have hn0 : 0 < n := Nat.pos_of_ne_zero fun h0 => hx1 (by
      rw [h0, pow_zero, Subgroup.card_eq_one] at hn
      exact (Subgroup.mem_bot).1 (hn ▸ hxW))
    have hnm : m ≤ n := not_lt.1 fun h => hm n hn0 h hmod
    exact h2 F (omegaZ R F) hFab hFk
      ⟨⟨⟨fun a b => Subtype.ext (a.2.2.1 b b.2.1).eq⟩⟩, fun w hw => hw.2.2.1⟩
      ((Nat.pow_le_pow_right two_pos hnm).trans hn.ge) hFW

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5

end

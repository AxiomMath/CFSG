module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.AltNatData
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NatFF
public import CFSG.Quasithin.Background.B3Q

public section

namespace CFSG.Quasithin.B69K

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Cooperstein.Coordinator

section Stmts

variable {S : Type} [CommGroup S] [Finite S] {G Lt : Subgroup (MulAut S)} {hLG : Lt ≤ G} {m : ℕ}

theorem offpm_isExp2 (D : AltNatData G Lt hLG m) {B : Subgroup (MulAut S)}
    (hB : IsElemAbelian2 B) : ∀ e ∈ (B.subgroupOf G).map D.θ, e * e = 1 := by
  intro e he
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 he
  have hgB : (g : MulAut S) ∈ B := Subgroup.mem_subgroupOf.1 hg
  have hg2 : g * g = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
    exact hB.2 _ hgB
  rw [← map_mul, hg2, map_one]

theorem offpm_card_image (D : AltNatData G Lt hLG m) {B : Subgroup (MulAut S)} (hBG : B ≤ G) :
    Nat.card ((B.subgroupOf G).map D.θ) = Nat.card B := by
  rw [Subgroup.card_map_of_injective D.inj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv

theorem offpm_mem_fixV_iff (D : AltNatData G Lt hLG m) {B : Subgroup (MulAut S)} (hBG : B ≤ G)
    (s : S) : s ∈ fixV B ↔
      (D.π.toEquiv.trans Multiplicative.toAdd) s ∈
        CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.altFix m ((B.subgroupOf G).map D.θ) := by
  rw [CFSG.Quasithin.mem_fixV,
    CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.mem_altFix_iff_altAct]
  constructor
  · intro h b hb
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hb
    have hgB : (g : MulAut S) ∈ B := Subgroup.mem_subgroupOf.1 hg
    show CFSG.HardMathSupport.Cooperstein.Coordinator.altAct (D.θ g)
        (Multiplicative.toAdd (D.π s)) = Multiplicative.toAdd (D.π s)
    rw [← D.equiv g s, h _ hgB]
  · intro h x hx
    have hgx : (⟨x, hBG hx⟩ : ↥G) ∈ B.subgroupOf G := Subgroup.mem_subgroupOf.2 hx
    have hb := h (D.θ ⟨x, hBG hx⟩) (Subgroup.mem_map_of_mem D.θ hgx)
    change CFSG.HardMathSupport.Cooperstein.Coordinator.altAct (D.θ ⟨x, hBG hx⟩)
        (Multiplicative.toAdd (D.π s)) = Multiplicative.toAdd (D.π s) at hb
    rw [← D.equiv ⟨x, hBG hx⟩ s] at hb
    exact D.π.injective (Multiplicative.toAdd.injective hb)

theorem offpm_card_fixV (D : AltNatData G Lt hLG m) {B : Subgroup (MulAut S)} (hBG : B ≤ G) :
    Nat.card (fixV B) =
      Nat.card (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.altFix m
        ((B.subgroupOf G).map D.θ)) :=
  Nat.card_congr (Equiv.subtypeEquiv (D.π.toEquiv.trans Multiplicative.toAdd)
    (offpm_mem_fixV_iff D hBG))

theorem offpm_card_S (D : AltNatData G Lt hLG m) : Nat.card S = Nat.card (altHeart m) :=
  Nat.card_congr (D.π.toEquiv.trans Multiplicative.toAdd)

theorem offpm_swap_mem (hm : 9 ≤ m) (hodd : Odd m) {E : Subgroup (Equiv.Perm (Fin m))}
    (hE : ∀ g ∈ E, g * g = 1)
    (hoffE : (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.altFix m E).index ≤ Nat.card E)
    {σ : Equiv.Perm (Fin m)} (hσE : σ ∈ E) (hσ1 : σ ≠ 1) : ∃ τ ∈ E, τ.IsSwap := by
  have hP : IsPGroup 2 E := fun g =>
    ⟨1, Subtype.ext (by rw [Subgroup.coe_pow, pow_one, pow_two, Subgroup.coe_one]; exact hE _ g.2)⟩
  have hfixp : ∃ p : Fin m, ∀ g ∈ E, g p = p := by
    by_contra hne
    push Not at hne
    have hempty : MulAction.fixedPoints E (Fin m) = ∅ := by
      ext q
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hq
      obtain ⟨e, he, heq⟩ := hne q
      exact heq (MulAction.mem_fixedPoints.1 hq ⟨e, he⟩)
    have hmod := hP.card_modEq_card_fixedPoints (Fin m)
    have h0 : Nat.card (MulAction.fixedPoints E (Fin m)) = 0 := by
      rw [hempty]
      simp
    have hfin : Nat.card (Fin m) = m := by simp
    unfold Nat.ModEq at hmod
    rw [hfin, h0] at hmod
    have hm2 := Nat.odd_iff.1 hodd
    omega
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (Equiv.ext hcon)
  have hj : σ i ∈ MulAction.orbit E i := MulAction.mem_orbit i (⟨σ, hσE⟩ : E)
  have hswap : Equiv.swap i (σ i) ∈
      CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender.orbitStab E := by
    rw [CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender.mem_orbitStab]
    intro x
    by_cases hxi : x = i
    · rw [hxi, Equiv.swap_apply_left]
      exact hj
    by_cases hxj : x = σ i
    · rw [hxj, Equiv.swap_apply_right]
      refine ⟨(⟨σ⁻¹, inv_mem hσE⟩ : E), ?_⟩
      show σ⁻¹ (σ i) = i
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
      exact MulAction.mem_orbit_self x
  have hA := CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.offender_shape_altHeart
    (n := m) (Or.inr hm) E hE hoffE
  obtain ⟨hA1, -⟩ := hA
  obtain ⟨-, hEo⟩ := hA1 hfixp
  rw [← hEo] at hswap
  exact ⟨Equiv.swap i (σ i), hswap, ⟨i, σ i, hi.symm, rfl⟩⟩

theorem card_mul_fixV_le (D : AltNatData G Lt hLG m) (hm : 9 ≤ m) (hodd : Odd m)
    {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB : IsElemAbelian2 B) (hB1 : B ≠ ⊥) :
    Nat.card B * Nat.card (fixV B) ≤ Nat.card S := by
  have hE := offpm_isExp2 D hB
  have hnot : ¬ CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.IsMatchingGroup
      ((B.subgroupOf G).map D.θ) := by
    intro h
    obtain ⟨⟨k, hk⟩, -⟩ :=
      (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.natFF (by omega) hE).1 h
    obtain ⟨j, hj⟩ := hodd
    omega
  have hk := (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.natFF (by omega) hE).2 hnot
  rw [← offpm_card_image D hBG, offpm_card_fixV D hBG, offpm_card_S D]
  exact hk

theorem exists_swap_of_offender (D : AltNatData G Lt hLG m) (hm : 9 ≤ m) (hodd : Odd m)
    {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB : IsElemAbelian2 B) (hB1 : B ≠ ⊥)
    (hoff : Nat.card S ≤ Nat.card B * Nat.card (fixV B)) :
    ∃ (b : MulAut S) (hb : b ∈ B), (D.θ ⟨b, hBG hb⟩).IsSwap := by
  have hE := offpm_isExp2 D hB
  have hoffE : (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.altFix m
      ((B.subgroupOf G).map D.θ)).index ≤ Nat.card ((B.subgroupOf G).map D.θ) := by
    have hpos : 0 < Nat.card (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.altFix m
        ((B.subgroupOf G).map D.θ)) := Nat.card_pos
    have hidx : (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.altFix m
        ((B.subgroupOf G).map D.θ)).index * Nat.card
          (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.altFix m
            ((B.subgroupOf G).map D.θ)) = Nat.card (altHeart m) :=
      AddSubgroup.index_mul_card _
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [hidx, ← offpm_card_S D, offpm_card_image D hBG, ← offpm_card_fixV D hBG]
    exact hoff
  obtain ⟨⟨t, htB⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
  have hgt : (⟨t, hBG htB⟩ : ↥G) ∈ B.subgroupOf G := Subgroup.mem_subgroupOf.2 htB
  have hσE : D.θ ⟨t, hBG htB⟩ ∈ (B.subgroupOf G).map D.θ :=
    Subgroup.mem_map_of_mem D.θ hgt
  have hσ1 : D.θ ⟨t, hBG htB⟩ ≠ 1 := by
    intro h
    have h1 : (⟨t, hBG htB⟩ : ↥G) = 1 := D.inj (h.trans (map_one D.θ).symm)
    have h1' : ((⟨t, hBG htB⟩ : ↥G) : MulAut S) = ((1 : ↥G) : MulAut S) := congrArg Subtype.val h1
    exact ht1 (Subtype.ext h1')
  obtain ⟨τ, hτE, hτsw⟩ := offpm_swap_mem hm hodd hE hoffE hσE hσ1
  obtain ⟨g', hg', hg'eq⟩ := Subgroup.mem_map.1 hτE
  refine ⟨(g' : MulAut S), Subgroup.mem_subgroupOf.1 hg', ?_⟩
  show (D.θ g').IsSwap
  rw [hg'eq]
  exact hτsw

theorem qOf_eq_one_of_offender (D : AltNatData G Lt hLG m) (hm : 9 ≤ m) (hodd : Odd m)
    (hS2 : ∀ s : S, s ^ 2 = 1) (hoff : ∃ B, IsFFStarOffender G B) :
    qOf G = ((1 : ℚ) : WithTop ℚ) := by
  obtain ⟨B₀, hB₀⟩ := hoff
  refine CFSG.Quasithin.qOf_eq_of_offenders hS2 le_rfl ?_ ⟨B₀, hB₀, ?_⟩
  · intro B hB
    have hc := card_mul_fixV_le D hm hodd hB.1 hB.2.2.1 hB.2.1
    have hnlt : ¬ CFSG.Quasithin.rAV B < 1 := by
      rw [CFSG.Quasithin.rAV_lt_one_iff hS2 hB.isA2]
      intro h
      exact absurd hc (not_le.2 h)
    exact not_lt.1 hnlt
  · have h := hB₀.2.2.2 ⊥ bot_le
    rw [Subgroup.card_bot, CFSG.Quasithin.B1.fixV_bot, Subgroup.card_top, one_mul] at h
    exact (CFSG.Quasithin.rAV_le_one_iff hS2 hB₀.isA2).2 h

end Stmts

end CFSG.Quasithin.B69K

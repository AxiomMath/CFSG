module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421ZNeA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Defs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace Lin2Hyp0

section ZNeB

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem false_of_ZLne1_B_end (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S) {a : G}
    (haT : a ∈ T) (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) {g u : G}
    (hu : u ∈ lin2Delta (thompsonJ S) (lin2Z L (thompsonJ S)) x) (hg : a = g⁻¹ * u * g) {w : G}
    (hwR : w ∈ centerOf (thompsonJ S)) (hwN : w ∈ conjR (thompsonJ S) g) (hw1 : w ≠ 1) :
    False := by
  set Z := lin2Z L (thompsonJ S) with hZdef
  have hZel := (E.Zbasic hcfg hZdef).1
  have hTIZ := E.ZTI hcfg hZdef
  have hnc := E.not_forall_commute_Z hcfg hc haT haR ha2
  obtain ⟨-, -, -, -, -, h6⟩ := (E.h20 G T M H S L D n hcfg Z hZdef hc).2 x hx hxS
  have haX : a ∈ conjR (centerOf (thompsonJ S)) g := mem_conjR_iff'.2 ⟨u, hu.1, hg⟩
  have hX : conjR (centerOf (thompsonJ S)) g ≤ Subgroup.centralizer ({w} : Set G) :=
    conjR_centerOf_le_centralizer hwN
  have hXeq := E.conjR_centerOf_eq_sup hcfg hc hx hxS g
  have hA : conjR Z g ≤ conjR (centerOf (thompsonJ S)) g := hXeq ▸ le_sup_left
  have hB : conjR Z (x * g) ≤ conjR (centerOf (thompsonJ S)) g := hXeq ▸ le_sup_right
  by_cases hwZ : w ∈ Z
  · have hKL1 := commute_of_centralizes_TI tiAbelianTwoGroupCommute hZel hTIZ hwZ hw1
      (hA.trans hX)
    have hKL2 := commute_of_centralizes_TI tiAbelianTwoGroupCommute hZel hTIZ hwZ hw1
      (g := x * g) (hB.trans hX)
    have hXC : conjR (centerOf (thompsonJ S)) g ≤ Subgroup.centralizer (Z : Set G) := by
      rw [hXeq]
      exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKL1)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKL2)
    apply hnc
    intro y hy
    exact (Subgroup.mem_centralizer_iff.1 (hXC haX) y hy).symm
  · by_cases hwZx : w ∈ conjR Z x
    · have hTIx : fusionIsTI (conjR Z x) := fusionIsTI_conjR hTIZ x
      have hZxel : IsElemAbelian 2 (conjR Z x) := (isElemAbelian_conjR_iff Z x).2 hZel
      have hle1 : conjR (conjR Z x) (x⁻¹ * g) ≤ Subgroup.centralizer ({w} : Set G) := by
        rw [conjR_conjR, mul_inv_cancel_left]; exact hA.trans hX
      have hle2 : conjR (conjR Z x) g ≤ Subgroup.centralizer ({w} : Set G) := by
        rw [conjR_conjR]; exact hB.trans hX
      have hKL1 := commute_of_centralizes_TI tiAbelianTwoGroupCommute hZxel hTIx hwZx hw1 hle1
      have hKL2 := commute_of_centralizes_TI tiAbelianTwoGroupCommute hZxel hTIx hwZx hw1 hle2
      have hXC : conjR (centerOf (thompsonJ S)) g ≤ Subgroup.centralizer (conjR Z x : Set G) := by
        rw [hXeq]
        refine sup_le ?_ ?_
        · have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKL1
          rwa [conjR_conjR, mul_inv_cancel_left] at this
        · have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKL2
          rwa [conjR_conjR] at this
      have hcen : ∀ y ∈ conjR Z x, a * y = y * a := fun y hy =>
        (Subgroup.mem_centralizer_iff.1 (hXC haX) y hy).symm
      have hcen' := conj_commute_of_commute_conjR hcen
      have hnc' := E.not_forall_commute_Z hcfg hc (T.mul_mem (T.mul_mem hx haT) (T.inv_mem hx))
        (fun h => haR ((Subgroup.mem_normalizer_iff.1 (E.TnR hcfg hx) a).2 h))
        (by
          have : (x * a * x⁻¹) ^ 2 = x * a ^ 2 * x⁻¹ := by simp only [pow_two]; group
          rw [this, ha2]; group)
      exact hnc' hcen'
    · have hΔ : w ∈ lin2Delta (thompsonJ S) Z x := ⟨hwR, hwZ, hwZx⟩
      have hXle := h6 w hΔ _ hX (isPGroup_conjR_centerOf hcfg g)
        (E.conjR_centerOf_eq_weakClosure hcfg hc hx hxS g)
      exact haR (hXle haX)


theorem false_of_ZLne1_B (hB2 : Lemma2421B2) (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T)
    (hxS : x ∉ S) {a : G} (haT : a ∈ T) (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) {g u : G}
    (hu : u ∈ lin2Delta (thompsonJ S) (lin2Z L (thompsonJ S)) x) (hg : a = g⁻¹ * u * g) :
    False := by
  by_cases hn : n = 2
  · exact hB2 G T M H S L D n hcfg hc hn x hx hxS a haT haR ha2 g u hu hg
  have hn3 : 3 ≤ n := by have := hcfg.one_lt; omega
  set Z := lin2Z L (thompsonJ S) with hZdef
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  obtain ⟨h2, -, h4, -, -, -⟩ := (E.h20 G T M H S L D n hcfg Z hZdef hc).2 x hx hxS
  set Ea := centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({a} : Set G) with hEa
  have hEael : IsElemAbelian 2 Ea :=
    IsElemAbelian.mono inf_le_left (E.centerOf_R_isElemAbelian hcfg)
  have hnorm : ∀ v ∈ centerOf (thompsonJ S), a * v * a⁻¹ ∈ centerOf (thompsonJ S) := by
    intro v hv
    have h1 := centerOf_normalized (E.TnR hcfg haT)
    have : v ∈ conjR (centerOf (thompsonJ S)) a := by rw [h1]; exact hv
    exact mem_conjR.1 this
  have hcardEa : 2 ^ n ≤ Nat.card Ea := by
    have h1 := card_le_sq_card_centralizer (E.centerOf_R_isElemAbelian hcfg) hnorm ha2
    rw [E.card_centerOf_R_of_ne_bot hcfg hc hx hxS,
      show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm]] at h1
    exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 h1
  have hn4 : 4 < Nat.card Ea := by
    have : 2 ^ 2 < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hEa2 : IsPGroup 2 ↥Ea :=
    hcfg.sylowT.isPGroup.to_le (inf_le_left.trans (inf_le_left.trans hRT))
  have hEaM : Ea ≤ conjR M g := by
    intro y hy
    rw [mem_conjR]
    apply (h2 u hu).2.1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.1 hy.2
    rw [hg] at hya
    calc g * y * g⁻¹ * u = g * (y * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * y) * g⁻¹ := by rw [hya]
      _ = u * (g * y * g⁻¹) := by group
  have hP0 : conjR Ea g⁻¹ ≤ M := by rw [conjR_le_iff, inv_inv]; exact hEaM
  obtain ⟨m, hmM, hmT⟩ := exists_le_conjR_of_isSylowTwoOf hcfg.cs.setting.isSylowTwoOf_M hP0
    ((isPGroup_conjR_iff 2).2 hEa2)
  have hEaT : Ea ≤ conjR T (m * g) := by
    have := conjR_mono hmT g
    rwa [conjR_inv_conjR, conjR_conjR] at this
  have hRmg : conjR (thompsonJ S) (m * g) = conjR (thompsonJ S) g := by
    rw [← conjR_conjR, conjR_eq_of_mem_normalizer (h4 hmM)]
  have hidx : (conjR S (m * g)).relIndex (conjR T (m * g)) = 2 := by
    rw [relIndex_conjR hcfg.S_le_T, E.idxTS hcfg]
  obtain ⟨s₀, -, hS⟩ := E.exists_zpowers_S hcfg
  have hNS : conjR (thompsonJ S) g ≤ conjR S (m * g) := by
    rw [← hRmg]; exact conjR_mono (thompsonJ_le_self S) _
  have hSN : conjR S (m * g) ≤ Subgroup.normalizer (conjR (thompsonJ S) g : Set G) := by
    rw [← hRmg, conjR_normalizer]
    exact conjR_mono (hcfg.S_le_T.trans (E.TnR hcfg)) _
  have hSeq : conjR S (m * g) =
      conjR (thompsonJ S) g ⊔ Subgroup.zpowers ((m * g)⁻¹ * s₀ * (m * g)) := by
    conv_lhs => rw [hS]
    rw [conjR_sup, conjR_zpowers, hRmg]
  have hne := inf_ne_bot_of_cyclic_quotient_index_two hEaT hidx hNS hSN hSeq hEael hn4
  obtain ⟨⟨w, hw⟩, hw1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hw1 : w ≠ 1 := fun h => hw1' (Subtype.ext h)
  have hwR : w ∈ centerOf (thompsonJ S) := hw.1.1
  exact E.false_of_ZLne1_B_end hcfg hc hx hxS haT haR ha2 hu hg hwR hw.2 hw1

theorem false_of_ZLne1 (hB2 : Lemma2421B2) (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T)
    (hxS : x ∉ S) {a : G} (haT : a ∈ T) (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) {g w : G}
    (hw : w ∈ centerOf (thompsonJ S)) (hg : a = g⁻¹ * w * g) : False := by
  by_cases hwZ : w ∈ lin2Z L (thompsonJ S)
  · exact E.false_of_ZLne1_A hcfg hc hx hxS haT haR ha2 hwZ hg
  · by_cases hwZx : w ∈ conjR (lin2Z L (thompsonJ S)) x
    · have hz : x * w * x⁻¹ ∈ lin2Z L (thompsonJ S) := mem_conjR.1 hwZx
      refine E.false_of_ZLne1_A hcfg hc hx hxS haT haR ha2 hz (g := x * g) ?_
      rw [hg]; group
    · exact E.false_of_ZLne1_B hcfg hB2 hc hx hxS haT haR ha2 ⟨hw, hwZ, hwZx⟩ hg

end ZNeB

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2

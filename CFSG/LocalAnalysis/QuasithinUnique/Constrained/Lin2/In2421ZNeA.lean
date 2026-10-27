module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421ZNeSupp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg3

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem conj_commute_of_commute_conjR {Z : Subgroup G} {a x : G}
    (h : ∀ y ∈ conjR Z x, a * y = y * a) : ∀ y ∈ Z, (x * a * x⁻¹) * y = y * (x * a * x⁻¹) := by
  intro y hy
  have hy' : x⁻¹ * y * x ∈ conjR Z x := by
    rw [mem_conjR, show x * (x⁻¹ * y * x) * x⁻¹ = y by group]; exact hy
  have := h _ hy'
  calc x * a * x⁻¹ * y = x * (a * (x⁻¹ * y * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * y * x) * a) * x⁻¹ := by rw [this]
    _ = y * (x * a * x⁻¹) := by group

end Generic

namespace Lin2Hyp0

section ZNeA

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem false_of_ZLne1_A (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S) {a : G}
    (haT : a ∈ T) (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) {g z : G}
    (hz : z ∈ lin2Z L (thompsonJ S)) (hg : a = g⁻¹ * z * g) : False := by
  set Z := lin2Z L (thompsonJ S) with hZdef
  have ha1 : a ≠ 1 := fun h => haR (by rw [h]; exact one_mem _)
  have haZg : a ∈ conjR Z g := mem_conjR_iff'.2 ⟨z, hz, hg⟩
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hZR : Z ≤ centerOf (thompsonJ S) := lin2Z_le_centerOf E.h16 hcfg hZdef
  have hZel := (E.Zbasic hcfg hZdef).1
  have hTIZ := E.ZTI hcfg hZdef
  have hnc := E.not_forall_commute_Z hcfg hc haT haR ha2
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
  have hn4 : 2 < Nat.card Ea :=
    lt_of_lt_of_le (by have := hcfg.four_le_two_pow; omega) hcardEa
  have hEa2 : IsPGroup 2 ↥Ea :=
    hcfg.sylowT.isPGroup.to_le (inf_le_left.trans (inf_le_left.trans hRT))
  obtain ⟨g', hZg', hEaS⟩ :=
    E.exists_le_conjR_S_of_le_centralizer hcfg hc haZg ha1 inf_le_right hEa2
  obtain ⟨s₀, -, hS⟩ := E.exists_zpowers_S hcfg
  set N := conjR (thompsonJ S) g' with hN
  have hNS : N ≤ conjR S g' := conjR_mono (thompsonJ_le_self S) g'
  have hSN : conjR S g' ≤ Subgroup.normalizer (N : Set G) := by
    rw [hN, conjR_normalizer]
    exact conjR_mono (hcfg.S_le_T.trans (E.TnR hcfg)) g'
  have hSeq : conjR S g' = N ⊔ Subgroup.zpowers (g'⁻¹ * s₀ * g') := by
    conv_lhs => rw [hS]
    rw [conjR_sup, conjR_zpowers]
  have hne := inf_ne_bot_of_cyclic_quotient hEaS hNS hSN hSeq hEael hn4
  obtain ⟨⟨w, hw⟩, hw1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hw1 : w ≠ 1 := fun h => hw1' (Subtype.ext h)
  have hwR : w ∈ centerOf (thompsonJ S) := hw.1.1
  have hX : conjR (centerOf (thompsonJ S)) g' ≤ Subgroup.centralizer ({w} : Set G) :=
    conjR_centerOf_le_centralizer hw.2
  have hZ'X : conjR Z g ≤ conjR (centerOf (thompsonJ S)) g' := by
    rw [← hZg']; exact conjR_mono hZR g'
  by_cases hwZ : w ∈ Z
  · have hle : conjR Z g ≤ Subgroup.centralizer ({w} : Set G) := hZ'X.trans hX
    have hcomm := commute_of_centralizes_TI tiAbelianTwoGroupCommute hZel hTIZ hwZ hw1 hle
    apply hnc
    intro y hy
    have h1 := Subgroup.commutator_mem_commutator haZg hy
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  · by_cases hwZx : w ∈ conjR Z x
    · have hTIx : fusionIsTI (conjR Z x) := fusionIsTI_conjR hTIZ x
      have hZxel : IsElemAbelian 2 (conjR Z x) := (isElemAbelian_conjR_iff Z x).2 hZel
      have hle : conjR (conjR Z x) (x⁻¹ * g) ≤ Subgroup.centralizer ({w} : Set G) := by
        rw [conjR_conjR, mul_inv_cancel_left]; exact hZ'X.trans hX
      have hcomm := commute_of_centralizes_TI tiAbelianTwoGroupCommute hZxel hTIx hwZx hw1 hle
      have haZx : a ∈ conjR (conjR Z x) (x⁻¹ * g) := by
        rw [conjR_conjR, mul_inv_cancel_left]; exact haZg
      have hcen : ∀ y ∈ conjR Z x, a * y = y * a := by
        intro y hy
        have h1 := Subgroup.commutator_mem_commutator haZx hy
        rw [hcomm, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.1 h1
      have hcen' := conj_commute_of_commute_conjR hcen
      have hnc' := E.not_forall_commute_Z hcfg hc (T.mul_mem (T.mul_mem hx haT) (T.inv_mem hx))
        (fun h => haR ((Subgroup.mem_normalizer_iff.1 (E.TnR hcfg hx) a).2 h))
        (by
          have : (x * a * x⁻¹) ^ 2 = x * a ^ 2 * x⁻¹ := by simp only [pow_two]; group
          rw [this, ha2]; group)
      exact hnc' hcen'
    · have hΔ : w ∈ lin2Delta (thompsonJ S) Z x := ⟨hwR, hwZ, hwZx⟩
      obtain ⟨-, -, -, -, -, h6⟩ := (E.h20 G T M H S L D n hcfg Z hZdef hc).2 x hx hxS
      have hXle := h6 w hΔ _ hX (isPGroup_conjR_centerOf hcfg g')
        (E.conjR_centerOf_eq_weakClosure hcfg hc hx hxS g')
      exact haR (hXle (hZ'X haZg))

end ZNeA

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.FusionLocalFour

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS

theorem eq_two_of_card_cases_aux {k : Fin 4} {n : ℕ}
    (h : n = babyCentOrder k ∨ n = 2 * babyCentOrder k)
    (h2 : n = babyCentOrder 2 ∨ n = 2 * babyCentOrder 2) : k = 2 := by
  have key : ∀ k : Fin 4, (babyCentOrder k = babyCentOrder 2 ∨
      babyCentOrder k = 2 * babyCentOrder 2 ∨ 2 * babyCentOrder k = babyCentOrder 2 ∨
      2 * babyCentOrder k = 2 * babyCentOrder 2) → k = 2 := by decide
  exact key k (by omega)

theorem map_center_centralizer {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (w : X) :
    ((center ↥(centralizer ({w} : Set X))).map
        (centralizer ({w} : Set X)).subtype).map e.toMonoidHom =
      (center ↥(centralizer ({e w} : Set Y))).map (centralizer ({e w} : Set Y)).subtype := by
  have hc := RankThree.PartOne.Torsion37.center_map_mulEquiv (centralizerEquiv e w)
  rw [Subgroup.map_map, ← hc, Subgroup.map_map]
  rfl

theorem center_centralizer_eq_conj {X : Type} [Group X] {t w : X} (ht : t ∈ center X)
    (hct : center X ≤ zpowers t) (g : X) {c : X} (hc : c ∈ center X)
    (hZ : (center ↥(centralizer ({w} : Set X))).map (centralizer ({w} : Set X)).subtype =
      zpowers w ⊔ zpowers t) :
    (center ↥(centralizer ({g * w * g⁻¹ * c} : Set X))).map
      (centralizer ({g * w * g⁻¹ * c} : Set X)).subtype =
        zpowers (g * w * g⁻¹ * c) ⊔ zpowers t := by
  have hcz : c ∈ zpowers t := hct hc
  have hew : (MulAut.conj g) w = g * w * g⁻¹ := MulAut.conj_apply g w
  have het : (MulAut.conj g) t = t := by
    rw [MulAut.conj_apply]
    exact mul_inv_eq_iff_eq_mul.2 (mem_center_iff.1 ht g)
  have hCeq : centralizer ({g * w * g⁻¹ * c} : Set X) = centralizer ({g * w * g⁻¹} : Set X) := by
    generalize g * w * g⁻¹ = a
    ext x
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    have hcx : c * x = x * c := (mem_center_iff.1 hc x).symm
    constructor
    · intro h
      have h' : x * a * c = a * x * c :=
        calc x * a * c = x * (a * c) := mul_assoc x a c
          _ = a * c * x := h
          _ = a * (c * x) := mul_assoc a c x
          _ = a * (x * c) := by rw [hcx]
          _ = a * x * c := (mul_assoc a x c).symm
      exact mul_right_cancel h'
    · intro h
      calc x * (a * c) = x * a * c := (mul_assoc x a c).symm
        _ = a * x * c := by rw [h]
        _ = a * (x * c) := mul_assoc a x c
        _ = a * (c * x) := by rw [hcx]
        _ = a * c * x := (mul_assoc a c x).symm
  rw [hCeq, ← hew, ← map_center_centralizer (MulAut.conj g) w, hZ, Subgroup.map_sup,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have h1 : (MulEquiv.toMonoidHom (MulAut.conj g)) w = g * w * g⁻¹ := hew
  have h2 : (MulEquiv.toMonoidHom (MulAut.conj g)) t = t := het
  rw [h1, h2, hew]
  generalize g * w * g⁻¹ = a
  apply le_antisymm
  · refine sup_le (zpowers_le.2 ?_) le_sup_right
    have h3 : (a * c) * c⁻¹ ∈ zpowers (a * c) ⊔ zpowers t :=
      mul_mem (mem_sup_left (mem_zpowers _)) (inv_mem (mem_sup_right hcz))
    rwa [mul_inv_cancel_right] at h3
  · exact sup_le (zpowers_le.2 (mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right hcz)))
      le_sup_right

@[expose] def TwoBLocalFourW3Rep : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsTwoBCover L → ∀ t : L, t ∈ center L → orderOf t = 2 →
    ∃ w : L, orderOf w = 2 ∧ w ∉ center L ∧
      (Nat.card ↥(centralizer ({w} : Set L)) = babyCentOrder 2 ∨
        Nat.card ↥(centralizer ({w} : Set L)) = 2 * babyCentOrder 2) ∧
      (center ↥(centralizer ({w} : Set L))).map (centralizer ({w} : Set L)).subtype =
        zpowers w ⊔ zpowers t

theorem twoBLocalFourW3_of_rep (hT3 : BabyTableIII) (h : TwoBLocalFourW3Rep) :
    TwoBLocalFourW3 := by
  intro L _ _ hcov t ht ht2 w' hw'2 hw'c hcard' _
  obtain ⟨w, hw2, hwc, hcard, hZ⟩ := h L hcov t ht ht2
  obtain ⟨-, hc, ⟨φ⟩⟩ := hcov
  obtain ⟨k, hk, hkc⟩ := exists_babyInv_card_cases hT3 hc φ hw2 hwc
  obtain ⟨k', hk', hkc'⟩ := exists_babyInv_card_cases hT3 hc φ hw'2 hw'c
  obtain rfl := eq_two_of_card_cases_aux hkc hcard
  obtain rfl := eq_two_of_card_cases_aux hkc' hcard'
  obtain ⟨y, hy⟩ : ∃ y : Carrier .B, y * φ (QuotientGroup.mk w) * y⁻¹ =
      φ (QuotientGroup.mk w') := isConj_iff.1 (hT3.2 2 _ _ hk hk')
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (φ.symm y)
  have hyg : y = φ (QuotientGroup.mk g) := by rw [hg, MulEquiv.apply_symm_apply]
  have hmk : (QuotientGroup.mk (g * w * g⁻¹) : L ⧸ center L) = QuotientGroup.mk w' := by
    apply φ.injective
    rw [← hy, hyg]
    simp
  have hcen : (g * w * g⁻¹)⁻¹ * w' ∈ center L := QuotientGroup.eq.1 hmk
  have hcz : center L ≤ zpowers t := by
    have hle : zpowers t ≤ center L := zpowers_le.2 ht
    have hz2 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht2]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hz2])).symm.le
  have key := center_centralizer_eq_conj ht hcz g hcen hZ
  have hw'eq : g * w * g⁻¹ * ((g * w * g⁻¹)⁻¹ * w') = w' := by group
  rwa [hw'eq] at key

end CFSG.EvenSporadicStandard.TwoB

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Theta
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Sq
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Shape

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

namespace PullHyp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T : Subgroup G}
  {EY : Subgroup (MulAut (↥L ⧸ center ↥L))} (h : PullHyp G L z t T EY)

omit [Finite G] in
include h in
theorem conj_mem_sup {k : G} (hk : k ∈ centralizer ({z} : Set G)) {n : G}
    (hn : n ∈ L ⊔ zpowers z) : k * n * k⁻¹ ∈ L ⊔ zpowers z := by
  obtain ⟨l, hl, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 h.cfg.z_cent) hn
  have hkw : k * w * k⁻¹ = w := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
    have := (Commute.zpow_right (show Commute k z from mem_centralizer_singleton_iff.1 hk) j).eq
    rw [this]
    group
  have hkl : k * l * k⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h.cfg.cent_le hk) l).1 hl
  have : k * (l * w) * k⁻¹ = (k * l * k⁻¹) * (k * w * k⁻¹) := by group
  rw [this, hkw]
  exact mul_mem (mem_sup_left hkl) (mem_sup_right hw)

include h in
theorem exists_outer_involution (hsurj : Function.Surjective (thetaH h.cfg.cent_le))
    (hsq : ∀ y ∈ centralizer ({z} : Set G), y * y ∈ L)
    (hF1 : ∃ r : MulAut (↥L ⧸ center ↥L), r * r = 1 ∧ ¬ IsInnerAut r) :
    ∃ σ ∈ T, σ * σ = 1 ∧ σ ∉ L ⊔ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr1, hrinn⟩ := hF1
  obtain ⟨⟨g, hg⟩, hgr⟩ := hsurj r
  have hth : h.th g hg = r := hgr
  have hgN : g ∉ L ⊔ zpowers z := fun hgN => hrinn (hth ▸ h.isInnerAut_th_of_mem hg hgN)
  have hgg : g * g = 1 := by
    have hggH : g * g ∈ centralizer ({z} : Set G) := mul_mem hg hg
    have h1 : h.th (g * g) hggH = 1 := by rw [h.th_mul hg hg, hth, hr1]
    have h2 : g * g ∈ zpowers z := (h.th_eq_one_iff hggH).1 h1
    have h3 : g * g ∈ L ⊓ zpowers z := ⟨hsq g hg, h2⟩
    rw [h.cfg.disjoint.eq_bot, mem_bot] at h3
    exact h3
  have hX : IsPGroup 2 (zpowers g) := by
    have hg2 : orderOf g = 2 := by
      refine orderOf_eq_prime (by rw [pow_two]; exact hgg) fun hg1 => hgN ?_
      rw [hg1]
      exact one_mem _
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg2]; norm_num)
  obtain ⟨k, hk, hkT⟩ := h.cfg.exists_conj_into_T hX (zpowers_le.2 hg)
  refine ⟨k⁻¹ * g * k, hkT g (mem_zpowers g), ?_, fun hσ => hgN ?_⟩
  · calc k⁻¹ * g * k * (k⁻¹ * g * k) = k⁻¹ * (g * g) * k := by group
      _ = 1 := by rw [hgg]; group
  · have := h.conj_mem_sup hk hσ
    have e : k * (k⁻¹ * g * k) * k⁻¹ = g := by group
    rwa [e] at this

omit [Finite G] in
include h in
theorem not_mem_L_of_conj (hsurj : Function.Surjective (thetaH h.cfg.cent_le))
    (hsq : ∀ y ∈ centralizer ({z} : Set G), y * y ∈ L)
    (hF2 : ∀ a : ↥L ⧸ center ↥L, a * a = 1 → ∃ r : MulAut (↥L ⧸ center ↥L), r * r = MulAut.conj a)
    (g : G) : g * z * g⁻¹ ∉ L := by
  intro hgL
  set a : G := g * z * g⁻¹ with ha
  have ha2 : a * a = 1 := by
    calc a * a = g * (z * z) * g⁻¹ := by rw [ha]; group
      _ = 1 := by rw [h.cfg.z_sq]; group
  let ā : ↥L ⧸ center ↥L := QuotientGroup.mk (⟨a, hgL⟩ : ↥L)
  have hā : ā * ā = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨a, hgL⟩ : ↥L) * ⟨a, hgL⟩ = 1 := Subtype.ext ha2
    rw [this, QuotientGroup.mk_one]
  obtain ⟨r, hr⟩ := hF2 ā hā
  obtain ⟨⟨y, hy⟩, hyr⟩ := hsurj r
  have hth : h.th y hy = r := hyr
  have hyyH : y * y ∈ centralizer ({z} : Set G) := mul_mem hy hy
  have h1 : h.th (y * y) hyyH = h.th a (h.L_le_H hgL) := by
    rw [h.th_mul hy hy, hth, hr, h.th_L hgL, nuL_apply]
  have h2 : (y * y)⁻¹ * a ∈ zpowers z := (h.th_eq_iff hyyH (h.L_le_H hgL)).1 h1
  have h3 : (y * y)⁻¹ * a ∈ L ⊓ zpowers z :=
    ⟨L.mul_mem (L.inv_mem (hsq y hy)) hgL, h2⟩
  rw [h.cfg.disjoint.eq_bot, mem_bot, inv_mul_eq_one] at h3
  apply h.cfg.z_not_square hsq
  refine ⟨g⁻¹ * y * g, ?_⟩
  calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
    _ = z := by rw [h3, ha]; group

end PullHyp

end CFSG.EvenSporadicStandard.Fin76b

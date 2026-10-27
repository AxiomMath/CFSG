module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.IsoOn

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

private theorem invCover_conj_self {k : G} (hk : k ∈ Gx a) : k * a * k⁻¹ = a := by
  rw [← mem_Gx.mp hk, mul_assoc, mul_inv_cancel, mul_one]

private theorem invCover_mul_conj {k x : G} (hk : k ∈ Gx a) :
    a * (k * x * k⁻¹) = k * (a * x) * k⁻¹ :=
  calc a * (k * x * k⁻¹) = (k * a * k⁻¹) * (k * x * k⁻¹) := by rw [invCover_conj_self hk]
    _ = k * (a * x) * k⁻¹ := by group

private theorem invCover_exists_conj {r s : ↥(Gx a)} (h : IsConj r s) :
    ∃ k ∈ Gx a, k * (r : G) * k⁻¹ = (s : G) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine ⟨(c : G), c.2, ?_⟩
  have h' := congrArg (Subtype.val) hc
  simpa using h'

private theorem invCover_isConj {x y k : G} (h : k * x * k⁻¹ = y) : IsConj x y :=
  isConj_iff.mpr ⟨k, h⟩

theorem inv_cover (h : F5Std a z) {t : G} (ht : t ∈ InvIn (Gx a)) :
    t = a ∨ t ∈ orb2A a a ∨ t ∈ orb2B a z a ∨ t ∈ orb2AB a z a ∨ t ∈ orb2BB a z a := by
  obtain ⟨z₀, b, u, hF, hz₀, haz₀, -, -, -, -⟩ := h.loc.fusion1.self.rep_z
  have hbu := h.loc.fusion2.self.reps_bu z₀ b u hF hz₀
  have hbA : IsConj a (b : G) := hbu.1.1
  have hbaA : IsConj a (a * (b : G)) := hbu.1.2.1
  have huB : IsConj z (u : G) := hbu.2.1
  have hauB : IsConj z (a * (u : G)) := hbu.2.2.1
  have ha2 : a * a = 1 := by
    have h2 : a ^ 2 = 1 := by rw [← h.typ.orderOf_a]; exact pow_orderOf_eq_one a
    simpa [pow_two] using h2
  have hord : orderOf (⟨t, ht.1⟩ : ↥(Gx a)) = 2 := by
    rw [Subgroup.orderOf_mk, ht.2]
  obtain ⟨i, hi⟩ := hF.involution_cover ⟨t, ht.1⟩ hord
  fin_cases i
  ·
    change IsConj (GxSelf a) (⟨t, ht.1⟩ : ↥(Gx a)) at hi
    obtain ⟨k, hk, hkt⟩ := invCover_exists_conj hi
    have hkt : k * (GxSelf a : G) * k⁻¹ = t := hkt
    left
    rw [← hkt]
    simpa [GxSelf] using invCover_conj_self (a := a) hk
  ·
    change IsConj z₀ (⟨t, ht.1⟩ : ↥(Gx a)) at hi
    obtain ⟨k, hk, hkt⟩ := invCover_exists_conj hi
    have hkt : k * (z₀ : G) * k⁻¹ = t := hkt
    right; right; right; left
    refine ⟨hz₀.trans (invCover_isConj hkt), ?_⟩
    have hat : a * t = k * (a * (z₀ : G)) * k⁻¹ := by
      rw [← hkt]
      exact invCover_mul_conj (a := a) (x := (z₀ : G)) hk
    rw [hat]
    exact haz₀.trans (invCover_isConj rfl)
  ·
    change IsConj (GxSelf a * z₀) (⟨t, ht.1⟩ : ↥(Gx a)) at hi
    obtain ⟨k, hk, hkt⟩ := invCover_exists_conj hi
    have hkt : k * ((GxSelf a * z₀ : ↥(Gx a)) : G) * k⁻¹ = t := hkt
    have hrep : ((GxSelf a * z₀ : ↥(Gx a)) : G) = a * (z₀ : G) := by simp [GxSelf]
    rw [hrep] at hkt
    right; right; left
    have haz : a * (a * (z₀ : G)) = (z₀ : G) := by rw [← mul_assoc, ha2, one_mul]
    have hat : a * t = k * (z₀ : G) * k⁻¹ := by
      rw [← hkt]
      calc a * (k * (a * (z₀ : G)) * k⁻¹) = k * (a * (a * (z₀ : G))) * k⁻¹ :=
            invCover_mul_conj (a := a) (x := a * (z₀ : G)) hk
        _ = k * (z₀ : G) * k⁻¹ := by rw [haz]
    refine ⟨haz₀.trans (invCover_isConj hkt), ?_⟩
    rw [hat]
    exact hz₀.trans (invCover_isConj rfl)
  ·
    change IsConj b (⟨t, ht.1⟩ : ↥(Gx a)) at hi
    obtain ⟨k, hk, hkt⟩ := invCover_exists_conj hi
    have hkt : k * (b : G) * k⁻¹ = t := hkt
    right; left
    refine ⟨hbA.trans (invCover_isConj hkt), ?_⟩
    have hat : a * t = k * (a * (b : G)) * k⁻¹ := by
      rw [← hkt]
      exact invCover_mul_conj (a := a) (x := (b : G)) hk
    rw [hat]
    exact hbaA.trans (invCover_isConj rfl)
  ·
    change IsConj u (⟨t, ht.1⟩ : ↥(Gx a)) at hi
    obtain ⟨k, hk, hkt⟩ := invCover_exists_conj hi
    have hkt : k * (u : G) * k⁻¹ = t := hkt
    right; right; right; right
    refine ⟨huB.trans (invCover_isConj hkt), ?_⟩
    have hat : a * t = k * (a * (u : G)) * k⁻¹ := by
      rw [← hkt]
      exact invCover_mul_conj (a := a) (x := (u : G)) hk
    rw [hat]
    exact hauB.trans (invCover_isConj rfl)

theorem eq_one_or_eq_of_central (h : F5Std a z) {g : G} (hg : g ∈ Gx a)
    (hc : ∀ x ∈ Gx a, g * x = x * g) : g = 1 ∨ g = a := by
  obtain ⟨z₀, b, u, hF, hz₀, haz₀, -, -, -, -⟩ := h.loc.fusion1.self.rep_z
  have hcenter : (⟨g, hg⟩ : ↥(Gx a)) ∈ Subgroup.center ↥(Gx a) := by
    rw [Subgroup.mem_center_iff]
    intro y
    refine Subtype.ext ?_
    simpa using (hc (y : G) y.2).symm
  have hmem : (⟨g, hg⟩ : ↥(Gx a)) ∈ Subgroup.zpowers (GxSelf a) := by
    rw [← hF.center_eq]
    exact hcenter
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hgk : g = a ^ k := by
    have h' := congrArg (Subtype.val) hk
    simp only [Subgroup.coe_zpow, GxSelf] at h'
    exact h'.symm
  have ha2z : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, ← h.typ.orderOf_a]
    exact pow_orderOf_eq_one a
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    simp only [hgk, hm, zpow_mul, ha2z, one_zpow]
  · right
    simp only [hgk, hm, zpow_add_one, zpow_mul, ha2z, one_zpow, one_mul]

theorem iso_apply_self (h : F5Std a z) (h' : F5Std a' z') {φ : G → G'}
    (hφ : IsIsoOn (Gx a) (Gx a') φ) : φ a = a' := by
  have ha : a ∈ Gx a := self_mem_Gx a
  have hc : ∀ y ∈ Gx a', φ a * y = y * φ a := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hφ.surjOn y hy
    rw [← hφ.map_mul _ ha _ hx, ← hφ.map_mul _ hx _ ha, mem_Gx.mp hx]
  rcases eq_one_or_eq_of_central h' (hφ.mem a ha) hc with h1 | h1
  · exfalso
    have h2 := hφ.orderOf_eq ha
    rw [h1, orderOf_one, h.typ.orderOf_a] at h2
    omega
  · exact h1

end CFSG.EvenSporadicStandard.HNRecog.Section4

module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG.Open CFSG.LargeEvenClassification.Helpers CFSG.ProperTwoGeneratedCore

variable {G : Type} [Group G] [Finite G]

theorem t2_omega1_extend {A : Subgroup G} (hA : IsElemAbelian 2 A) {k : ℕ}
    (hAk : Nat.card A = 2 ^ k) {y : G} (hy2 : y * y = 1) (hyA : y ∉ A)
    (hyc : ∀ a ∈ A, a * y = y * a) :
    ∃ E : Subgroup G, A ≤ E ∧ y ∈ E ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (k + 1) ∧
      E ≤ A ⊔ zpowers y := by
  have hy1 : y ≠ 1 := fun h => hyA (h ▸ A.one_mem)
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  have hcomm : A ≤ centralizer (zpowers y : Set G) :=
    le_centralizer_iff.mpr (zpowers_le.mpr (mem_centralizer_iff.mpr hyc))
  obtain ⟨E, hAE, hyE, hE, hEcard, hEle⟩ :=
    commuting_disjoint_elementary_product (firstRank := k) (secondRank := 1) A (zpowers y) hA
      (involution_zpowers_elementary y hyo) hAk (by rw [Nat.card_zpowers, hyo, pow_one]) hcomm
      (involution_zpowers_disjoint A y hyo hyA)
  exact ⟨E, hAE, hyE (mem_zpowers y), hE, hEcard, hEle⟩

theorem t2_omega1_mem_of_card_four {E : Subgroup G} (hE : Nat.card E = 4) {a b c d : G}
    (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E) (hd : d ∈ E) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∀ x ∈ E, x = a ∨ x = b ∨ x = c ∨ x = d := by
  classical
  intro x hx
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hxa, hxb, hxc, hxd⟩ := hne
  let T : Finset E := {⟨x, hx⟩, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩}
  have hT : T.card = 5 := by
    simp [T, Finset.card_insert_of_notMem, Subtype.ext_iff, hxa, hxb, hxc, hxd, hab, hac, had, hbc,
      hbd, hcd]
  have hle : T.card ≤ Nat.card E := by
    have := Fintype.ofFinite E
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ T
  omega

theorem t2_omega1_le (hr : CFSG.pRank 2 G = 3) {H U : Subgroup G} {w₀ : G}
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hUH : U ≤ H) (hU4 : Nat.card ↥U = 4)
    (hUe : ∀ x ∈ U, x * x = 1) (hw₀2 : w₀ * w₀ = 1) (hw₀H : w₀ ∉ H)
    (hw₀inv : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹) :
    ∀ x ∈ H, x * x = 1 → x ∈ U := by
  intro x hxH hx2
  by_contra hxU
  have hUel : IsElemAbelian 2 U :=
    ⟨⟨⟨fun a b => Subtype.ext (hHc a (hUH a.2) b (hUH b.2))⟩⟩,
      fun y hy => by rw [sq]; exact hUe y hy⟩
  obtain ⟨E₁, -, -, hE₁, hE₁card, hE₁le⟩ :=
    t2_omega1_extend hUel (k := 2) (by rw [hU4]; norm_num) hx2 hxU
      (fun a ha => hHc a (hUH ha) x hxH)
  have hE₁H : E₁ ≤ H := hE₁le.trans (sup_le hUH (zpowers_le.mpr hxH))
  have hw₀E₁ : w₀ ∉ E₁ := fun h => hw₀H (hE₁H h)
  have hcomm : ∀ e ∈ E₁, e * w₀ = w₀ * e := by
    intro e he
    have he2 : e * e = 1 := by rw [← sq]; exact hE₁.2 e he
    have h := hw₀inv e (hE₁H he)
    rw [inv_eq_of_mul_eq_one_right he2] at h
    calc e * w₀ = (w₀ * e * w₀⁻¹) * w₀ := by rw [h]
      _ = w₀ * e := by group
  obtain ⟨E₂, -, -, hE₂, hE₂card, -⟩ := t2_omega1_extend hE₁ (k := 3) hE₁card hw₀2 hw₀E₁ hcomm
  have h4 : 4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) :=
    CFSG.SectionRank.le_pRank one_lt_two le_top hE₂ hE₂card
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, hr] at h4
  omega

theorem t2_omega1_zu (hr : CFSG.pRank 2 G = 3) {H : Subgroup G} {z u w₀ : G}
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hzH : z ∈ H) (huH : u ∈ H)
    (hz2 : z * z = 1) (hu2 : u * u = 1) (hz1 : z ≠ 1) (hu1 : u ≠ 1) (hzu : z ≠ u)
    (hw₀2 : w₀ * w₀ = 1) (hw₀H : w₀ ∉ H) (hw₀inv : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹) :
    ∀ x ∈ H, x * x = 1 → x = 1 ∨ x = z ∨ x = u ∨ x = z * u := by
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hzH' : zpowers z ≤ H := zpowers_le.mpr hzH
  have huz : u ∉ zpowers z := by
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hzo, Finset.mem_image]
    rintro ⟨k, hk, hku⟩
    rw [Finset.mem_range] at hk
    interval_cases k
    · rw [pow_zero] at hku
      exact hu1 hku.symm
    · rw [pow_one] at hku
      exact hzu hku
  obtain ⟨U, hzU, huU, hUel, hU4, hUle⟩ := t2_omega1_extend (A := zpowers z) (k := 1)
    (involution_zpowers_elementary z hzo) (by rw [Nat.card_zpowers, hzo, pow_one]) hu2 huz
    (fun a ha => hHc a (hzH' ha) u huH)
  have hUH : U ≤ H := hUle.trans (sup_le hzH' (zpowers_le.mpr huH))
  have hU4' : Nat.card U = 4 := by rw [hU4]; norm_num
  have hUe : ∀ x ∈ U, x * x = 1 := fun x hx => by rw [← sq]; exact hUel.2 x hx
  intro x hxH hx2
  have hxU := t2_omega1_le hr hHc hUH hU4' hUe hw₀2 hw₀H hw₀inv x hxH hx2
  refine t2_omega1_mem_of_card_four hU4' U.one_mem (hzU (mem_zpowers z)) huU
    (U.mul_mem (hzU (mem_zpowers z)) huU) hz1.symm hu1.symm ?_ hzu ?_ ?_ x hxU
  · intro h
    have h1 : z = u⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    exact hzu (h1.trans (inv_eq_of_mul_eq_one_right hu2))
  · intro h
    exact hu1 (by simpa using h)
  · intro h
    exact hz1 (by simpa using h)

end CFSG.GH74.GLS.Stage4.Rest

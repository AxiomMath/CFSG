module

public import CFSG.GH74.Generic.BProg.B3.S3T3Inv
public import CFSG.GH74.Generic.BProg.B3.S3Sec29H

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools Subgroup

namespace S3T3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem e8_of_triple {p q r : G} (hp : p * p = 1) (hp1 : p ≠ 1) (hq : q * q = 1)
    (hr : r * r = 1) (hpq : p * q = q * p) (hpr : p * r = r * p) (hqr : q * r = r * q)
    (hq' : q ∉ zpowers p) (hr' : r ∉ zpowers p ⊔ zpowers q) :
    CFSG.IsElementaryAbelian 2 ↥(zpowers p ⊔ zpowers q ⊔ zpowers r) ∧
      Nat.card ↥(zpowers p ⊔ zpowers q ⊔ zpowers r) = 8 := by
  have hpo : orderOf p = 2 := orderOf_eq_prime (by rw [pow_two]; exact hp) hp1
  have hcq : ∀ h ∈ zpowers p, h * q = q * h := by
    intro h hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute p q from hpq) i).eq
  have hle : zpowers p ⊔ zpowers q ≤ centralizer ({r} : Set G) :=
    sup_le (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hpr))
      (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hqr))
  have hcr : ∀ h ∈ zpowers p ⊔ zpowers q, h * r = r * h := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  have he2 := S3Sec29H.isElementaryAbelian_sup_zpowers (S3Sec29H.isElementaryAbelian_zpowers hp)
    hq hcq
  refine ⟨S3Sec29H.isElementaryAbelian_sup_zpowers he2 hr hcr, ?_⟩
  rw [S3Sec29H.card_sup_zpowers hr hr' hcr, S3Sec29H.card_sup_zpowers hq hq' hcq,
    Nat.card_zpowers, hpo]

theorem exists_E8 {J Λ : Subgroup G} (hJ : IsA7Bar J) (hΛJ : Λ ≤ J) (hperf : ⁅Λ, Λ⁆ = Λ)
    (hne : Λ ≠ ⊥) {u x : G} (hu2 : u * u = 1) (hu1 : u ≠ 1) (huΛ : ∀ l ∈ Λ, l * u = u * l)
    (hx2 : x * x = 1) (hxN : x ∈ normalizer (Λ : Set G)) (hux : u * x = x * u) :
    ∃ S : Subgroup G, S ≤ centralizer ({x} : Set G) ∧
      S ≤ zpowers u ⊔ zpowers x ⊔ (Λ ⊓ centralizer ({x} : Set G)) ∧
      CFSG.IsElementaryAbelian 2 ↥S ∧ Nat.card ↥S = 8 := by
  have huL : u ∉ Λ := fun h =>
    S3Sec29I1.no_perfect_centralizing_invol hJ hΛJ hperf h hu2 hu1 huΛ
  have hmemC : ∀ {g : G}, g * x = x * g → g ∈ centralizer ({x} : Set G) := fun h =>
    Subgroup.mem_centralizer_singleton_iff.2 h
  have hsupl : ∀ {g : G}, g ∈ Λ → g * x = x * g →
      g ∈ zpowers u ⊔ zpowers x ⊔ (Λ ⊓ centralizer ({x} : Set G)) := fun hg hgx =>
    Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hg, hmemC hgx⟩)
  have hsupu : u ∈ zpowers u ⊔ zpowers x ⊔ (Λ ⊓ centralizer ({x} : Set G)) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_zpowers u))
  have hsupx : x ∈ zpowers u ⊔ zpowers x ⊔ (Λ ⊓ centralizer ({x} : Set G)) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers x))
  by_cases hxL : x ∈ Λ ⊔ zpowers u
  · obtain ⟨l, hl, hxl⟩ := S3Sec29H.mem_sup_zpowers hu2 huΛ hxL
    have hlx : ∀ g ∈ Λ, g * l = l * g → g * x = x * g := by
      intro g hg hgl
      rcases hxl with rfl | rfl
      · exact hgl
      · calc g * (l * u) = (g * l) * u := by group
          _ = (l * g) * u := by rw [hgl]
          _ = l * (g * u) := by group
          _ = l * (u * g) := by rw [huΛ g hg]
          _ = l * u * g := by group
    have hl2 : l * l = 1 := by
      rcases hxl with rfl | rfl
      · exact hx2
      · have h1 : (l * u) * (l * u) = l * l * (u * u) := by
          calc (l * u) * (l * u) = l * (u * l) * u := by group
            _ = l * (l * u) * u := by rw [huΛ l hl]
            _ = l * l * (u * u) := by group
        rw [hu2, mul_one] at h1
        rw [← h1]
        exact hx2
    obtain ⟨a, haΛ, ha2, ha1, b, hbΛ, hb2, hb1, hba, hab, hal, hbl⟩ :
        ∃ a ∈ Λ, a * a = 1 ∧ a ≠ 1 ∧ ∃ b ∈ Λ, b * b = 1 ∧ b ≠ 1 ∧ b ≠ a ∧ a * b = b * a ∧
          a * l = l * a ∧ b * l = l * b := by
      by_cases hl1 : l = 1
      · obtain ⟨a, haΛ, ha2, ha1⟩ := exists_invol hperf hne
        obtain ⟨b, hbΛ, hb2, hb1, hba, hab⟩ := exists_invol_comm hJ hΛJ hperf hne haΛ ha2 ha1
        exact ⟨a, haΛ, ha2, ha1, b, hbΛ, hb2, hb1, hba, hab.symm, by simp [hl1], by simp [hl1]⟩
      · obtain ⟨b, hbΛ, hb2, hb1, hbl', hbl⟩ := exists_invol_comm hJ hΛJ hperf hne hl hl2 hl1
        exact ⟨l, hl, hl2, hl1, b, hbΛ, hb2, hb1, hbl', hbl.symm, rfl, hbl⟩
    have hb' : b ∉ zpowers a := fun h => by
      rcases eq_one_or_eq_of_mem_zpowers ha2 h with h1 | h1
      · exact hb1 h1
      · exact hba h1
    have hu' : u ∉ zpowers a ⊔ zpowers b := fun h =>
      huL ((sup_le (zpowers_le.2 haΛ) (zpowers_le.2 hbΛ)) h)
    obtain ⟨hel, hcard⟩ :=
      e8_of_triple ha2 ha1 hb2 hu2 hab (huΛ a haΛ) (huΛ b hbΛ) hb' hu'
    have hax := hlx a haΛ hal
    have hbx := hlx b hbΛ hbl
    exact ⟨_, sup_le (sup_le (zpowers_le.2 (hmemC hax)) (zpowers_le.2 (hmemC hbx)))
      (zpowers_le.2 (hmemC hux)), sup_le (sup_le (zpowers_le.2 (hsupl haΛ hax))
        (zpowers_le.2 (hsupl hbΛ hbx))) (zpowers_le.2 hsupu), hel, hcard⟩
  · have : Nontrivial ↥Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hne
    have heven : 2 ∣ Nat.card ↥Λ :=
      S3Sec29I.even_card_of_perfect (Subgroup.isPerfect_iff.mpr hperf)
    obtain ⟨w, hwΛ, hw2, hw1, hwx⟩ := exists_invol_centralizer heven hxN hx2
    have hu' : u ∉ zpowers w := fun h => huL (zpowers_le.2 hwΛ h)
    have hx' : x ∉ zpowers w ⊔ zpowers u := fun h =>
      hxL ((sup_le ((zpowers_le.2 hwΛ).trans le_sup_left) le_sup_right) h)
    obtain ⟨hel, hcard⟩ := e8_of_triple hw2 hw1 hu2 hx2 (huΛ w hwΛ) hwx hux hu' hx'
    exact ⟨_, sup_le (sup_le (zpowers_le.2 (hmemC hwx)) (zpowers_le.2 (hmemC hux)))
      (zpowers_le.2 (hmemC rfl)), sup_le (sup_le (zpowers_le.2 (hsupl hwΛ hwx))
        (zpowers_le.2 hsupu)) (zpowers_le.2 hsupx), hel, hcard⟩

end S3T3

end CFSG.GH74.Generic.BProg.B3

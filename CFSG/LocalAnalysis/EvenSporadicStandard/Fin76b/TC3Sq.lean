module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

namespace OuterConfig

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {T : Subgroup G}
  (h : OuterConfig G L z t T)

include h in
theorem sq_mem_L {c : G} (hc : c ∈ centralizer ({z} : Set G)) (hcL : c ∉ L ⊔ zpowers z)
    (hcc : c * c ∈ L) {y : G} (hy : y ∈ centralizer ({z} : Set G)) : y * y ∈ L := by
  have hidx : ((L ⊔ zpowers z).subgroupOf (centralizer ({z} : Set G))).index = 2 := h.index_two
  have hzsq := h.z_sq
  have hLz : ∀ k ∈ L ⊔ zpowers z, k * k ∈ L := by
    intro k hk
    obtain ⟨l, hl, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (zpowers_le.2 h.z_cent) hk
    have hwc : ∀ g ∈ L, g * w = w * g := by
      intro g hg
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
      exact (Commute.zpow_right (show Commute g z from h.z_comm_of_mem_A hg) j).eq
    rcases mem_zpowers_sq_eq_one hzsq hw with hw1 | hw1
    · rw [hw1]
      simpa using mul_mem hl hl
    · rw [hw1]
      have : l * z * (l * z) = l * l := by
        calc l * z * (l * z) = l * (z * l) * z := by group
          _ = l * (l * z) * z := by rw [h.z_comm_of_mem_A hl]
          _ = l * l * (z * z) := by group
          _ = l * l := by rw [hzsq, mul_one]
      rw [this]
      exact mul_mem hl hl
  by_cases hyN : y ∈ L ⊔ zpowers z
  · exact hLz y hyN
  ·
    have hyc : y * c⁻¹ ∈ L ⊔ zpowers z := by
      have key := Subgroup.mul_mem_iff_of_index_two hidx
        (a := (⟨y, hy⟩ : ↥(centralizer ({z} : Set G)))) (b := ⟨c⁻¹, inv_mem hc⟩)
      have hcN : (⟨c⁻¹, inv_mem hc⟩ : ↥(centralizer ({z} : Set G))) ∉
          (L ⊔ zpowers z).subgroupOf (centralizer ({z} : Set G)) := fun hh =>
        hcL (by simpa using inv_mem (mem_subgroupOf.1 hh))
      have hyN' : (⟨y, hy⟩ : ↥(centralizer ({z} : Set G))) ∉
          (L ⊔ zpowers z).subgroupOf (centralizer ({z} : Set G)) := fun hh =>
        hyN (mem_subgroupOf.1 hh)
      exact mem_subgroupOf.1 (key.2 ⟨fun h1 => absurd h1 hyN', fun h2 => absurd h2 hcN⟩)
    obtain ⟨l, hl, w, hw, hlw⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (zpowers_le.2 h.z_cent) hyc
    have hwc : ∀ g ∈ centralizer ({z} : Set G), g * w = w * g := by
      intro g hg
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
      exact (Commute.zpow_right (show Commute g z from mem_centralizer_singleton_iff.1 hg) j).eq
    have hy' : y = (l * c) * w := by
      have : y = (y * c⁻¹) * c := by group
      rw [this, hlw]
      calc l * w * c = l * (w * c) := by group
        _ = l * (c * w) := by rw [← hwc c hc]
        _ = l * c * w := by group
    have hlcH : l * c ∈ centralizer ({z} : Set G) :=
      mul_mem (mem_centralizer_singleton_iff.2 (h.z_comm_of_mem_A hl)) hc
    have hsq : y * y = (l * c) * (l * c) := by
      have hwH : w ∈ centralizer ({z} : Set G) := by
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
        exact zpow_mem (mem_centralizer_singleton_iff.2 rfl) j
      have hww : w * w = 1 := by
        rcases mem_zpowers_sq_eq_one hzsq hw with hw1 | hw1
        · rw [hw1]; simp
        · rw [hw1]; exact hzsq
      calc y * y = ((l * c) * w) * ((l * c) * w) := by rw [← hy']
        _ = (l * c) * (w * (l * c)) * w := by group
        _ = (l * c) * ((l * c) * w) * w := by rw [← hwc _ hlcH]
        _ = (l * c) * (l * c) * (w * w) := by group
        _ = (l * c) * (l * c) := by rw [hww, mul_one]
    rw [hsq]
    have hnorm : c * l * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h.cent_le hc) l).1 hl
    have : (l * c) * (l * c) = l * (c * l * c⁻¹) * (c * c) := by group
    rw [this]
    exact mul_mem (mul_mem hl hnorm) hcc

include h in
theorem z_not_square (hsq : ∀ y ∈ centralizer ({z} : Set G), y * y ∈ L) :
    ¬ ∃ g : G, g * g = z := by
  rintro ⟨g, hg⟩
  have hgz : g ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g * z = g * (g * g) := by rw [hg]
      _ = (g * g) * g := by group
      _ = z * g := by rw [hg]
  exact h.z_not_mem_A (hg ▸ hsq g hgz)

end OuterConfig

end CFSG.EvenSporadicStandard.Fin76b

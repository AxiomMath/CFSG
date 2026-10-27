module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ExcQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.CoverOut

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup

theorem not_dvd_card_of_isPGroup_two {Z : Type} [Group Z] [Finite Z] (hZ : IsPGroup 2 Z) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card Z := by
  intro h
  obtain ⟨n, hn⟩ := hZ.exists_card_eq
  rw [hn] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem false_of_fus_inner {X : Type} [Group X] [Finite X] (L : Subgroup X) [L.Normal]
    (hZ : IsPGroup 2 (center ↥L)) (hQ : ExcQuot (↥L ⧸ center ↥L)) {w : X} (hw : w * w = 1)
    {k : X} (hk : k ∈ L) (hact : ∀ l ∈ L, w * l * w⁻¹ = k * l * k⁻¹)
    (hD : CentFacts ↥(centralizer ({w} : Set X))) : False := by
  let D : Subgroup X := centralizer ({w} : Set X)
  let kL : ↥L := ⟨k, hk⟩
  let Ck : Subgroup ↥L := centralizer ({kL} : Set ↥L)
  let C : Subgroup X := L ⊓ D
  have hww : w⁻¹ * w⁻¹ = 1 := by rw [← mul_inv_rev, hw, inv_one]
  have hwk : w * k * w⁻¹ = k := by
    have h := hact k hk
    have hk3 : k * k * k⁻¹ = k := by group
    rwa [hk3] at h
  have hk_sq_comm : ∀ l ∈ L, (k * k) * l = l * (k * k) := by
    intro l hl
    have hlk : k * l * k⁻¹ ∈ L := L.mul_mem (L.mul_mem hk hl) (L.inv_mem hk)
    have h2 : w * (k * l * k⁻¹) * w⁻¹ = k * (k * l * k⁻¹) * k⁻¹ := by
      calc w * (k * l * k⁻¹) * w⁻¹
          = (w * k * w⁻¹) * (w * l * w⁻¹) * (w * k * w⁻¹)⁻¹ := by group
        _ = k * (k * l * k⁻¹) * k⁻¹ := by rw [hwk, hact l hl]
    have h1 : w * (w * l * w⁻¹) * w⁻¹ = l := by
      calc w * (w * l * w⁻¹) * w⁻¹
          = (w * w) * l * (w⁻¹ * w⁻¹) := by group
        _ = l := by rw [hw, hww, one_mul, mul_one]
    rw [hact l hl] at h1
    have h3 : k * (k * l * k⁻¹) * k⁻¹ = l := by
      rw [← h2]; exact h1
    have h4 : l = k * (k * l * k⁻¹) * k⁻¹ := h3.symm
    conv_rhs => rw [h4]
    group
  have hkL_sq_center : kL * kL ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((hk_sq_comm (g : X) g.2).symm)
  by_cases hk_cent : kL ∈ center ↥L
  ·
    have hLD : L ≤ D := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hkx : x * k = k * x := by
        have h := (Subgroup.mem_center_iff.mp hk_cent) (⟨x, hx⟩ : ↥L)
        exact congrArg (fun g : ↥L => (g : X)) h
      have hkx_conj : k * x * k⁻¹ = x := by rw [← hkx]; group
      have hconj : w * x * w⁻¹ = x := by rw [hact x hx, hkx_conj]
      exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
    have hcard_dvd : Nat.card ↥L ∣ Nat.card ↥D := Subgroup.card_dvd_of_le hLD
    have h2 : 2 ^ 12 ∣ Nat.card ↥L := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)]
      exact hQ.two_pow_dvd.mul_right _
    exact hD.not_dvd (h2.trans hcard_dvd)
  ·
    have hmem : ∀ x (hx : x ∈ L), x ∈ D ↔ (⟨x, hx⟩ : ↥L) ∈ Ck := by
      intro x hx
      have hconj : w * x * w⁻¹ = k * x * k⁻¹ := hact x hx
      have hiff : (w * x * w⁻¹ = x) ↔ (k * x * k⁻¹ = x) := by rw [hconj]
      have hwiff : (w * x * w⁻¹ = x) ↔ x * w = w * x := by
        rw [mul_inv_eq_iff_eq_mul]; exact eq_comm
      have hkiff : (k * x * k⁻¹ = x) ↔ x * k = k * x := by
        rw [mul_inv_eq_iff_eq_mul]; exact eq_comm
      have hxCk : (⟨x, hx⟩ : ↥L) ∈ Ck ↔ x * k = k * x := by
        change (⟨x, hx⟩ : ↥L) ∈ centralizer ({kL} : Set ↥L) ↔ x * k = k * x
        rw [Subgroup.mem_centralizer_singleton_iff]
        constructor
        · intro h; simpa using congrArg Subtype.val h
        · intro h; exact Subtype.ext h
      change x ∈ centralizer ({w} : Set X) ↔ (⟨x, hx⟩ : ↥L) ∈ Ck
      rw [Subgroup.mem_centralizer_singleton_iff, hxCk]
      exact (hwiff.symm.trans hiff).trans hkiff
    have hCD : C = Ck.map L.subtype := by
      ext x
      constructor
      · intro hx
        change x ∈ L ⊓ D at hx
        rw [Subgroup.mem_inf] at hx
        exact ⟨⟨x, hx.1⟩, (hmem x hx.1).mp hx.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        change (y : X) ∈ L ⊓ D
        rw [Subgroup.mem_inf]
        exact ⟨y.2, (hmem y.1 y.2).mpr hy⟩
    have hcardC : Nat.card C = Nat.card Ck := by
      rw [hCD]
      exact Subgroup.card_map_of_injective L.subtype_injective
    let M : Subgroup ↥D := C.subgroupOf D
    have hMcard : Nat.card M = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show C ≤ D from inf_le_right)).toEquiv
    have hMcard' : Nat.card M = Nat.card Ck := hMcard.trans hcardC
    have hMnormal : M.Normal := by
      change (C.subgroupOf D).Normal
      rw [Subgroup.normal_subgroupOf_iff (show C ≤ D from inf_le_right)]
      intro h k hh hk
      change h ∈ L ⊓ D at hh
      rw [Subgroup.mem_inf] at hh
      rw [Subgroup.mem_inf]
      exact ⟨(inferInstance : L.Normal).conj_mem h hh.1 k,
        D.mul_mem (D.mul_mem hk hh.2) (D.inv_mem hk)⟩
    have hg2 : (kL : ↥L ⧸ center ↥L) * (kL : ↥L ⧸ center ↥L) = 1 := by
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq_one_iff (kL * kL)).mpr hkL_sq_center
    have hg1 : (kL : ↥L ⧸ center ↥L) ≠ 1 := fun h =>
      hk_cent ((QuotientGroup.eq_one_iff kL).mp h)
    have hCQ : Nat.card (centralizer ({(kL : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L))) ∣
        Nat.card Ck := card_centralizer_quotient_dvd kL
    have hCkpos : 0 < Nat.card Ck := Nat.card_pos
    rcases hQ.involution_centralizer _ hg2 hg1 with h12 | ⟨h4, h7, h11⟩
    ·
      have hMD : Nat.card M ∣ Nat.card ↥D := Subgroup.card_subgroup_dvd_card M
      have hCkD : Nat.card Ck ∣ Nat.card ↥D := by rw [← hMcard']; exact hMD
      exact hD.not_dvd (h12.trans (hCQ.trans hCkD))
    · have h4Ck : 4 < Nat.card Ck := lt_of_lt_of_le h4 (Nat.le_of_dvd hCkpos hCQ)
      have hMgt : 4 < Nat.card M := by rw [hMcard']; exact h4Ck
      obtain ⟨N, _hNnormal, _hNhom, _hNexists, hN7or11, hNbig⟩ := hD.core
      have hNM : N ≤ M := hNbig M hMnormal hMgt
      have hN_dvd_M : Nat.card N ∣ Nat.card M := Subgroup.card_dvd_of_le hNM
      have hN_dvd_Ck : Nat.card N ∣ Nat.card Ck := by
        rw [← hMcard']; exact hN_dvd_M
      rcases hN7or11 with h | h
      · exact h7 (dvd_card_centralizer_quotient (K := ↥L) (p := 7) (by norm_num)
          (not_dvd_card_of_isPGroup_two hZ (by norm_num) (by norm_num)) kL (h.trans hN_dvd_Ck))
      · exact h11 (dvd_card_centralizer_quotient (K := ↥L) (p := 11) (by norm_num)
          (not_dvd_card_of_isPGroup_two hZ (by norm_num) (by norm_num)) kL (h.trans hN_dvd_Ck))

end CFSG.EvenSporadicStandard.Co3Std.CentT

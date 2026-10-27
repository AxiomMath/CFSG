module

public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

section Standard

variable {F : Type*} [Group F]

theorem mem_centralizer_of_commutator_le {L M : Subgroup F} (hL : ⁅L, L⁆ = L)
    (hLM : M ≤ centralizer (L : Set F)) {g : F} (hg : ⁅L, zpowers g⁆ ≤ M) :
    g ∈ centralizer (L : Set F) := by
  have hML : ⁅M, L⁆ = ⊥ := (commutator_eq_bot_iff_le_centralizer).mpr hLM
  have h1 : ⁅⁅L, zpowers g⁆, L⁆ = ⊥ := le_bot_iff.mp (hML ▸ commutator_mono hg le_rfl)
  have h2 : ⁅⁅zpowers g, L⁆, L⁆ = ⊥ := by rw [commutator_comm (zpowers g) L]; exact h1
  have h3 : ⁅⁅L, L⁆, zpowers g⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hL, commutator_eq_bot_iff_le_centralizer] at h3
  rw [mem_centralizer_iff]
  intro l hl
  exact ((mem_centralizer_iff.mp (h3 hl)) g (mem_zpowers g)).symm

theorem commutator_eq_bot_of_le {L L' M : Subgroup F} (hL : ⁅L, L⁆ = L)
    (hLM : M ≤ centralizer (L : Set F)) (hL'M : M ≤ centralizer (L' : Set F))
    (hle : ⁅L, L'⁆ ≤ M) : ⁅L, L'⁆ = ⊥ := by
  have hML : ⁅M, L⁆ = ⊥ := (commutator_eq_bot_iff_le_centralizer).mpr hLM
  have hML' : ⁅M, L'⁆ = ⊥ := (commutator_eq_bot_iff_le_centralizer).mpr hL'M
  have h1 : ⁅⁅L, L'⁆, L⁆ = ⊥ := le_bot_iff.mp (hML ▸ commutator_mono hle le_rfl)
  have h2 : ⁅⁅L', L⁆, L⁆ = ⊥ := by rw [commutator_comm L' L]; exact h1
  have h3 : ⁅⁅L, L⁆, L'⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [hL] at h3

theorem map_conjugate {F' : Type*} [Group F'] (π : F →* F') (H : Subgroup F) (g : F) :
    (conjugate H g).map π = conjugate (H.map π) (π g) := by
  rw [conjugate, conjugate, map_map, map_map]
  congr 1
  ext x
  simp

theorem le_conjugate_of_normal {M C : Subgroup F} [M.Normal] (hMC : M ≤ C) (g : F) :
    M ≤ conjugate C g := by
  intro m hm
  exact ⟨g * m * g⁻¹, hMC (‹M.Normal›.conj_mem m hm g), by simp [mul_assoc]⟩

theorem map_inf_of_ker_le {F' : Type*} [Group F'] (π : F →* F') {C D : Subgroup F}
    (hC : π.ker ≤ C) : (C ⊓ D).map π = C.map π ⊓ D.map π := by
  apply le_antisymm (map_inf_le _ _ _)
  rintro _ ⟨⟨c, hc, rfl⟩, ⟨d, hd, hdc⟩⟩
  have hk : c⁻¹ * d ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdc, inv_mul_cancel]
  refine ⟨d, mem_inf.mpr ⟨?_, hd⟩, hdc⟩
  have := mul_mem hc (hC hk)
  rwa [mul_inv_cancel_left] at this

theorem mem_normalizer_centralizer {L : Subgroup F} {g : F} (hg : g ∈ normalizer (L : Set F)) :
    g ∈ normalizer ((centralizer (L : Set F) : Subgroup F) : Set F) := by
  rw [mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    simp only [SetLike.mem_coe, mem_centralizer_iff] at hc ⊢
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (mem_normalizer_iff.mp (inv_mem hg) l).mp hl
      rwa [inv_inv] at this
    have h1 := hc _ hl'
    calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * l := by group
  · intro hc
    simp only [SetLike.mem_coe, mem_centralizer_iff] at hc ⊢
    intro l hl
    have hl' : g * l * g⁻¹ ∈ L := (mem_normalizer_iff.mp hg l).mp hl
    have h1 := hc _ hl'
    calc l * c = g⁻¹ * ((g * l * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * l * g⁻¹)) * g := by rw [h1]
      _ = c * l := by group

variable [Finite F]

theorem isStandardSubgroup_map_of_surjective {F' : Type*} [Group F'] {L : Subgroup F}
    (π : F →* F') (hπ : Function.Surjective π) (hL : IsStandardSubgroup L)
    (hM : Odd (Nat.card π.ker)) (hLM : π.ker ≤ centralizer (L : Set F)) :
    IsStandardSubgroup (L.map π) := by
  obtain ⟨hq, heven, htight, hnorm, hcomm⟩ := hL
  have hLL : ⁅L, L⁆ = L := (Subgroup.isPerfect_iff (H := L)).mp hq.1
  set C := centralizer (L : Set F) with hC
  have hcen : centralizer ((L.map π : Subgroup F') : Set F') = C.map π := by
    apply le_antisymm
    · intro y hy
      obtain ⟨g, rfl⟩ := hπ y
      refine ⟨g, mem_centralizer_of_commutator_le hLL hLM ?_, rfl⟩
      have h1 : (⁅L, zpowers g⁆).map π = ⊥ := by
        rw [map_commutator, MonoidHom.map_zpowers, commutator_comm]
        exact (commutator_eq_bot_iff_le_centralizer).mpr (zpowers_le.mpr hy)
      exact (Subgroup.map_eq_bot_iff _).mp h1
    · rintro _ ⟨g, hg, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨l, hl, rfl⟩
      rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hg) l hl]
  have hcomap : (C.map π).comap π = C := by
    rw [comap_map_eq, sup_eq_left.mpr hLM]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    refine LieType.CurtisTits.isQuasisimple_of_surjective (φ := π.subgroupMap L) hq
      (π.subgroupMap_surjective L) ?_
    by_contra hall
    push Not at hall
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hxM : (x : F) ∈ π.ker := congrArg Subtype.val (hall x)
    have hxy : x * y = y * x := Subtype.ext ((mem_centralizer_iff.mp (hLM hxM)) y y.2).symm
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]
  ·
    rw [hcen]
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.mp heven)
    have htM : (t : F) ∉ π.ker := by
      intro htM
      have h1 : orderOf (⟨t, htM⟩ : π.ker) ∣ Nat.card π.ker := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, ht] at h1
      exact (Nat.not_even_iff_odd.mpr hM) (even_iff_two_dvd.mpr h1)
    have hord : orderOf (π t) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ htM
      rw [← map_pow, ← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one, map_one]
    have h2 := Subgroup.orderOf_dvd_natCard (C.map π) (mem_map_of_mem π t.2)
    rw [hord] at h2
    exact even_iff_two_dvd.mpr h2
  ·
    rw [hcen]
    intro y hy
    obtain ⟨g, rfl⟩ := hπ y
    have hgN : g ∉ normalizer (C : Set F) := by
      intro hg
      apply hy
      exact le_normalizer_map π (mem_map_of_mem π hg)
    have h1 := htight g hgN
    rw [← map_conjugate, ← map_inf_of_ker_le π hLM]
    exact Odd.of_dvd_nat h1 (Subgroup.card_map_dvd _ _)
  ·
    rw [hcen]
    apply le_antisymm
    · intro y hy
      obtain ⟨g, rfl⟩ := hπ y
      have hg : g ∈ normalizer (C : Set F) := by
        have h1 := le_normalizer_comap (H := C.map π) π hy
        rwa [hcomap] at h1
      rw [hnorm] at hg
      exact le_normalizer_map π (mem_map_of_mem π hg)
    · intro y hy
      have := mem_normalizer_centralizer hy
      rwa [hcen] at this
  ·
    intro y
    obtain ⟨g, rfl⟩ := hπ y
    intro hbot
    rw [← map_conjugate, ← map_commutator, Subgroup.map_eq_bot_iff] at hbot
    have hLgM : π.ker ≤ centralizer ((conjugate L g : Subgroup F) : Set F) := by
      intro m hm
      rw [mem_centralizer_iff]
      rintro _ ⟨l, hl, rfl⟩
      have hm' : g * m * g⁻¹ ∈ π.ker := π.normal_ker.conj_mem m hm g
      have h1 := (mem_centralizer_iff.mp (hLM hm')) l hl
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * l * g * m = g⁻¹ * (l * (g * m * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * m * g⁻¹) * l) * g := by rw [h1]
        _ = m * (g⁻¹ * l * g) := by group
    exact hcomm g (commutator_eq_bot_of_le hLL hLM hLgM hbot)

theorem isStandardSubgroup_map_mk' {L M : Subgroup F} [M.Normal] (hL : IsStandardSubgroup L)
    (hM : Odd (Nat.card M)) (hLM : M ≤ centralizer (L : Set F)) :
    IsStandardSubgroup (L.map (QuotientGroup.mk' M)) :=
  isStandardSubgroup_map_of_surjective _ (QuotientGroup.mk'_surjective M) hL
    (by rw [QuotientGroup.ker_mk']; exact hM) (by rw [QuotientGroup.ker_mk']; exact hLM)

end Standard

end CFSG.ComponentClassification.GSThmB

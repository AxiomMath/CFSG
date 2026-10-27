module

public import CFSG.GH74.Uniqueness.SU.SU13TB0Orbit
public import CFSG.GH74.Uniqueness.SU.SU13TB1Conj
public import CFSG.GH74.Uniqueness.SU.SU13TB1Core
public import CFSG.GH74.Uniqueness.SU.SU4Quot
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

section Alg

variable {G : Type} [Group G]

theorem conj_trivial_of_square {z y₀ : G} (hz : z * z = 1) (hy₀81 : y₀ ^ 81 = 1)
    (S : Set G) (hS : ∀ y ∈ S, y₀⁻¹ * y * y₀ ∈ S) (hzS : ∀ y ∈ S, z * y * z⁻¹ = y₀⁻¹ * y * y₀) :
    ∀ y ∈ S, z * y * z⁻¹ = y := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h2 : ∀ y ∈ S, y₀⁻¹ * (y₀⁻¹ * y * y₀) * y₀ = y := by
    intro y hy
    have h1 := hzS y hy
    have h3 := hzS _ (hS y hy)
    have h4 : z * (y₀⁻¹ * y * y₀) * z⁻¹ = y := by
      rw [← h1, hzi]
      calc z * (z * y * z) * z = (z * z) * y * (z * z) := by group
        _ = y := by rw [hz]; group
    exact h3.symm.trans h4
  have hcomm2 : ∀ y ∈ S, y₀ ^ 2 * y = y * y₀ ^ 2 := by
    intro y hy
    have := h2 y hy
    calc y₀ ^ 2 * y = y₀ ^ 2 * (y₀⁻¹ * (y₀⁻¹ * y * y₀) * y₀) := by rw [this]
      _ = y * y₀ ^ 2 := by simp only [pow_two]; group
  have hy₀ : (y₀ ^ 2) ^ 41 = y₀ := by
    rw [← pow_mul, show 2 * 41 = 81 + 1 by norm_num, pow_succ, hy₀81, one_mul]
  intro y hy
  rw [hzS y hy]
  have hc : Commute (y₀ ^ 2) y := hcomm2 y hy
  have hy' : y₀ * y = y * y₀ := by
    have := (hc.pow_left 41).eq
    rw [hy₀] at this
    exact this
  calc y₀⁻¹ * y * y₀ = y₀⁻¹ * (y * y₀) := by group
    _ = y₀⁻¹ * (y₀ * y) := by rw [hy']
    _ = y := by group

end Alg

variable {G : Type} [Group G] [Finite G]

theorem false_of_simple_quotient {C : Subgroup G} {z s : G} (hz : orderOf z = 2) (hzC : z ∈ C)
    (hCs : ∀ c ∈ C, c * s = s * c) (hs3 : orderOf s = 3) (hsY : s ∈ oc C)
    {q : ℕ} (hq : q.Prime) (hq3 : ¬ q ∣ 3) (hqk : ∀ k : ℕ, 0 < k → k ≤ 3 → ¬ q ∣ 3 ^ k - 1)
    (hs : IsSimpleGroup (Mbar C)) (hqc : q ∣ Nat.card (Mbar C))
    (hY : Nat.card (oc C) = 81)
    (hYz : Nat.card (oc C ⊓ centralizer ({z} : Set G) : Subgroup G) < 81) : False := by
  have : Fact q.Prime := ⟨hq⟩
  have hY81 : Nat.card (pPrimeCore 2 ↥C) = 81 := by
    have : Nat.card (oc C) = Nat.card (pPrimeCore 2 ↥C) :=
      Subgroup.card_map_of_injective C.subtype_injective
    rw [← this]; exact hY
  obtain ⟨fb, hfb⟩ := exists_prime_orderOf_dvd_card' (G := Mbar C) q hqc
  obtain ⟨c, rfl⟩ := proj_surjective C fb
  have hcq : c ^ q ∈ pPrimeCore 2 ↥C := by
    rw [← ker_proj C, MonoidHom.mem_ker, map_pow, ← hfb]
    exact pow_orderOf_eq_one _
  have hc81 : (c ^ q) ^ 81 = 1 := by
    have h1 := pow_card_eq_one' (G := pPrimeCore 2 ↥C) (x := ⟨c ^ q, hcq⟩)
    rw [hY81] at h1
    exact congrArg Subtype.val h1
  have hc'q : (c ^ 81) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; exact hc81
  have hc'ne : c ^ 81 ≠ 1 := by
    intro h
    have h1 : (proj C c) ^ 81 = 1 := by rw [← map_pow, h, map_one]
    have h2 : q ∣ 81 := hfb ▸ orderOf_dvd_of_pow_eq_one h1
    have h3 : q ∣ 3 ^ 4 := by norm_num; exact h2
    exact hq3 (hq.dvd_of_dvd_pow h3)
  set f : G := ((c ^ 81 : ↥C) : G) with hf
  have hfC : f ∈ C := (c ^ 81).2
  have hfq : orderOf f = q := by
    refine orderOf_eq_prime ?_ ?_
    · have := congrArg Subtype.val hc'q
      simpa [hf] using this
    · intro h
      exact hc'ne (Subtype.ext (by simpa [hf] using h))
  have hfN : f ∈ normalizer ((oc C : Subgroup G) : Set G) := le_normalizer_oc C hfC
  have hsf : zpowers s ≤ oc C ⊓ centralizer ({f} : Set G) := by
    rw [zpowers_le]
    refine mem_inf.mpr ⟨hsY, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact (hCs f hfC).symm
  have hr : 3 ∣ Nat.card (oc C ⊓ centralizer ({f} : Set G) : Subgroup G) := by
    have := Subgroup.card_dvd_of_le hsf
    rwa [Nat.card_zpowers, hs3] at this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYf : oc C ≤ centralizer ({f} : Set G) :=
    le_centralizer_of_card (p := 3) (q := q) (r := 3) (m := 3) hfq hfN (by rw [hY]; norm_num) hq3 hq3 hr hqk
  let D : Subgroup ↥C := (centralizer ((oc C : Subgroup G) : Set G)).comap C.subtype
  have hmemD : ∀ d : ↥C, d ∈ D ↔ ∀ y ∈ oc C, (d : G) * y = y * (d : G) := by
    intro d
    rw [Subgroup.mem_comap, mem_centralizer_iff]
    exact ⟨fun h y hy => (h y hy).symm, fun h y hy => (h y hy).symm⟩
  have hDn : D.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hmemD] at hn ⊢
    intro y hy
    have hy' : (g : G)⁻¹ * y * g ∈ oc C := by
      have := conj_mem_oc (X := C) (g := (g : G)⁻¹) (C.inv_mem g.2) hy
      simpa using this
    have h1 := hn _ hy'
    change (g : G) * n * (g : G)⁻¹ * y = y * ((g : G) * n * (g : G)⁻¹)
    calc (g : G) * n * (g : G)⁻¹ * y = (g : G) * (n * ((g : G)⁻¹ * y * g)) * (g : G)⁻¹ := by group
      _ = (g : G) * (((g : G)⁻¹ * y * g) * n) * (g : G)⁻¹ := by rw [h1]
      _ = y * ((g : G) * n * (g : G)⁻¹) := by group
  have hKn : (D.map (proj C)).Normal := hDn.map (proj C) (proj_surjective C)
  have hc'D : c ^ 81 ∈ D := by
    rw [hmemD]
    intro y hy
    have := mem_centralizer_singleton_iff.mp (hYf hy)
    exact this.symm
  have hKne : D.map (proj C) ≠ ⊥ := by
    intro h
    have h1 : proj C (c ^ 81) ∈ D.map (proj C) := Subgroup.mem_map_of_mem _ hc'D
    rw [h, mem_bot, map_pow] at h1
    have h2 : q ∣ 81 := hfb ▸ orderOf_dvd_of_pow_eq_one h1
    have h3 : q ∣ 3 ^ 4 := by norm_num; exact h2
    exact hq3 (hq.dvd_of_dvd_pow h3)
  have hKtop : D.map (proj C) = ⊤ := by
    have := hKn
    rcases hs.eq_bot_or_eq_top_of_normal (D.map (proj C)) with h | h
    · exact absurd h hKne
    · exact h
  let zc : ↥C := ⟨z, hzC⟩
  have hzK : proj C zc ∈ D.map (proj C) := by rw [hKtop]; exact mem_top _
  obtain ⟨d, hdD, hdz⟩ := Subgroup.mem_map.mp hzK
  have hy₀C : zc⁻¹ * d ∈ pPrimeCore 2 ↥C := by
    rw [← ker_proj C, MonoidHom.mem_ker, map_mul, map_inv, hdz]
    exact inv_mul_cancel _
  have hy₀ : z⁻¹ * (d : G) ∈ oc C := mem_oc.mpr ⟨(zc⁻¹ * d).2, hy₀C⟩
  set y₀ : G := z⁻¹ * (d : G) with hy₀def
  have hy₀81 : y₀ ^ 81 = 1 := by
    have h1 := pow_card_eq_one' (G := oc C) (x := ⟨y₀, hy₀⟩)
    rw [hY] at h1
    exact congrArg Subtype.val h1
  have hdc : ∀ w ∈ oc C, (d : G) * w = w * d := (hmemD d).mp hdD
  have hz_eq : z = (d : G) * y₀⁻¹ := by rw [hy₀def]; group
  have hz2 : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have hS : ∀ y ∈ (oc C : Set G), y₀⁻¹ * y * y₀ ∈ (oc C : Set G) := by
    intro y hy
    have hy₀C' : y₀ ∈ C := oc_le C hy₀
    have := conj_mem_oc (X := C) (g := y₀⁻¹) (C.inv_mem hy₀C') hy
    simpa using this
  have hzS : ∀ y ∈ (oc C : Set G), z * y * z⁻¹ = y₀⁻¹ * y * y₀ := by
    intro y hy
    have hw := hdc _ (hS y hy)
    calc z * y * z⁻¹ = ((d : G) * y₀⁻¹) * y * ((d : G) * y₀⁻¹)⁻¹ := by rw [← hz_eq]
      _ = (d : G) * (y₀⁻¹ * y * y₀) * (d : G)⁻¹ := by group
      _ = y₀⁻¹ * y * y₀ := by rw [hw]; group
  have hcen := conj_trivial_of_square hz2 hy₀81 (oc C : Set G) hS hzS
  have hle : oc C ≤ centralizer ({z} : Set G) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    have := hcen y hy
    calc y * z = (z * y * z⁻¹) * z := by rw [this]
      _ = z * y := by group
  have hcard : Nat.card (oc C ⊓ centralizer ({z} : Set G) : Subgroup G) = 81 := by
    rw [inf_eq_left.mpr hle]; exact hY
  omega

end CFSG.GH74.Uniqueness.SU.SU13

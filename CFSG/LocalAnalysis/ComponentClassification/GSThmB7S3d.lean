module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecJ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Steps

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

theorem map_inf_centralizer_of_isPGroup {H : Type*} [Group H] [Finite H] {A : Subgroup H}
    (hA : IsPGroup 2 A) {e : H} (he : e ∈ A) :
    (A ⊓ centralizer ({e} : Set H)).map (QuotientGroup.mk' (pPrimeCore 2 H)) =
      A.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊓
        centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) e} : Set (H ⧸ pPrimeCore 2 H)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxA, hxe⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨mem_map_of_mem _ hxA, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hxe]
  · rintro _ ⟨⟨x, hxA, rfl⟩, hxe⟩
    refine mem_map_of_mem _ (mem_inf.mpr ⟨hxA, mem_centralizer_singleton_iff.mpr ?_⟩)
    have h1 := mem_centralizer_singleton_iff.mp hxe
    rw [← map_mul, ← map_mul] at h1
    exact OddQuot.injOn_of_isPGroup hA (mul_mem hxA he) (mul_mem he hxA) h1

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

@[expose] def B2 (h : Hyp52 X) (y : X) (g : ↥(h.secG0 y)) : Subgroup X :=
  ((zpowers (h.secMk y g)).comap (h.secMk y)).map (h.secG0 y).subtype

theorem mem_B2 {g : ↥(h.secG0 y)} {x : X} :
    x ∈ B2 h y g ↔ ∃ hx : x ∈ h.secG0 y, h.secMk y ⟨x, hx⟩ ∈ zpowers (h.secMk y g) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨⟨x, hx⟩, hx', rfl⟩

theorem B2_le_G0 (g : ↥(h.secG0 y)) : B2 h y g ≤ h.secG0 y := map_subtype_le _

theorem secB0_le_B2 (g : ↥(h.secG0 y)) : h.secB0 y ≤ B2 h y g := by
  intro b hb
  refine mem_B2.mpr ⟨h.secB0_le_G0 y hb, ?_⟩
  have h1 : h.secMk y ⟨b, h.secB0_le_G0 y hb⟩ = 1 := by
    rw [← MonoidHom.mem_ker, Hyp52.ker_secMk]
    exact hb
  rw [h1]
  exact one_mem _

theorem mem_B2_self (g : ↥(h.secG0 y)) : (g : X) ∈ B2 h y g :=
  mem_B2.mpr ⟨g.2, mem_zpowers _⟩

theorem subgroupOf_B2 (g : ↥(h.secG0 y)) :
    (B2 h y g).subgroupOf (h.secG0 y) = (zpowers (h.secMk y g)).comap (h.secMk y) :=
  comap_map_eq_self_of_injective (h.secG0 y).subtype_injective _

theorem secImage_B2 (g : ↥(h.secG0 y)) : h.secImage y (B2 h y g) = zpowers (h.secMk y g) := by
  show ((B2 h y g).subgroupOf (h.secG0 y)).map (h.secMk y) = _
  rw [subgroupOf_B2, map_comap_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
    top_inf_eq]

theorem card_B2 {g : ↥(h.secG0 y)} (hg : orderOf (h.secMk y g) = 2) :
    Nat.card (B2 h y g) = 2 * Nat.card (h.secB0 y) := by
  have h1 := Hyp52.card_secImage (h := h) (y := y) (secB0_le_B2 g) (B2_le_G0 g)
  rw [secImage_B2, Nat.card_zpowers, hg] at h1
  exact h1.symm

theorem B2_le_P {g : ↥(h.secG0 y)} (hgP : (g : X) ∈ h.P)
    (hg2 : h.secMk y g * h.secMk y g = 1) : B2 h y g ≤ h.P := by
  intro x hx
  obtain ⟨hxG, hx'⟩ := mem_B2.mp hx
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx'
  have hgg : h.secMk y g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg2
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h1 : h.secMk y ⟨x, hxG⟩ = 1 := by
      rw [← hk, ← two_mul, zpow_mul, hgg, one_zpow]
    rw [← MonoidHom.mem_ker, Hyp52.ker_secMk] at h1
    exact h.secB0_le_P h1
  · have h1 : h.secMk y (⟨x, hxG⟩ * g⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hk, zpow_add, zpow_mul, hgg, one_zpow, one_mul,
        zpow_one, mul_inv_cancel]
    rw [← MonoidHom.mem_ker, Hyp52.ker_secMk] at h1
    have h2 := mul_mem (h.secB0_le_P h1) hgP
    simpa using h2

theorem mem_normalizer_B2_iff {g : ↥(h.secG0 y)} (hg1 : h.secMk y g ≠ 1)
    (hg2 : h.secMk y g * h.secMk y g = 1) (w : ↥(h.secG0 y)) :
    (w : X) ∈ normalizer (B2 h y g : Set X) ↔
      h.secMk y w * h.secMk y g = h.secMk y g * h.secMk y w := by
  constructor
  · intro hw
    have h1 : (w : X) * g * (w : X)⁻¹ ∈ B2 h y g :=
      (mem_normalizer_iff.mp hw g).mp (mem_B2_self g)
    obtain ⟨hG, h2⟩ := mem_B2.mp h1
    have h3 : (⟨(w : X) * g * (w : X)⁻¹, hG⟩ : ↥(h.secG0 y)) = w * g * w⁻¹ := rfl
    rw [h3, map_mul, map_mul, map_inv] at h2
    have hord : orderOf (h.secMk y g) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
    rcases eq_one_or_of_mem_zpowers hord h2 with h4 | h4
    · exfalso
      apply hg1
      calc h.secMk y g = (h.secMk y w)⁻¹ * (h.secMk y w * h.secMk y g * (h.secMk y w)⁻¹) *
            h.secMk y w := by group
        _ = 1 := by rw [h4]; group
    · calc h.secMk y w * h.secMk y g =
            (h.secMk y w * h.secMk y g * (h.secMk y w)⁻¹) * h.secMk y w := by group
        _ = h.secMk y g * h.secMk y w := by rw [h4]
  · intro hcomm
    have key : ∀ e ∈ zpowers (h.secMk y g), h.secMk y w * e * (h.secMk y w)⁻¹ = e := by
      intro e he
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
      rw [((Commute.zpow_right (show Commute (h.secMk y w) (h.secMk y g) from hcomm) k)).eq,
        mul_inv_cancel_right]
    rw [mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      obtain ⟨hnG, hn'⟩ := mem_B2.mp hn
      refine mem_B2.mpr ⟨mul_mem (mul_mem w.2 hnG) (inv_mem w.2), ?_⟩
      have h1 : (⟨(w : X) * n * (w : X)⁻¹, mul_mem (mul_mem w.2 hnG) (inv_mem w.2)⟩ :
          ↥(h.secG0 y)) = w * ⟨n, hnG⟩ * w⁻¹ := rfl
      rw [h1, map_mul, map_mul, map_inv, key _ hn']
      exact hn'
    · intro hn
      obtain ⟨hnG, hn'⟩ := mem_B2.mp hn
      have hnG' : n ∈ h.secG0 y := by
        have := mul_mem (mul_mem (inv_mem w.2) hnG) w.2
        rwa [show (w : X)⁻¹ * ((w : X) * n * (w : X)⁻¹) * w = n by group] at this
      refine mem_B2.mpr ⟨hnG', ?_⟩
      have h1 : (⟨n, hnG'⟩ : ↥(h.secG0 y)) =
          w⁻¹ * ⟨(w : X) * n * (w : X)⁻¹, hnG⟩ * w := Subtype.ext (by simp; group)
      have h2 := key _ hn'
      rw [h1, map_mul, map_mul, map_inv]
      have h3 : (h.secMk y w)⁻¹ * h.secMk y ⟨(w : X) * n * (w : X)⁻¹, hnG⟩ * h.secMk y w =
          h.secMk y ⟨(w : X) * n * (w : X)⁻¹, hnG⟩ := by
        calc (h.secMk y w)⁻¹ * h.secMk y ⟨(w : X) * n * (w : X)⁻¹, hnG⟩ * h.secMk y w
            = (h.secMk y w)⁻¹ * (h.secMk y w * h.secMk y ⟨(w : X) * n * (w : X)⁻¹, hnG⟩ *
              (h.secMk y w)⁻¹) * h.secMk y w := by rw [h2]
          _ = h.secMk y ⟨(w : X) * n * (w : X)⁻¹, hnG⟩ := by group
      rw [h3]
      exact hn'

end Seven

end CFSG.ComponentClassification.GSThmB

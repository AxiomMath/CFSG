module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem mem_zpowers_sup_zpowers_of_mem_sup {L : Subgroup G} {t u : G}
    (ht : t ∈ centralizer (L : Set G)) (hu : u ∈ L)
    (hZ : ∀ l ∈ L, l * u = u * l → (∀ b ∈ centralizer ({u} : Set G) ⊓ L, l * b = b * l) →
      l = 1 ∨ l = u)
    {x : G} (hxu : x * u = u * x) (hxB : ∀ b ∈ centralizer ({u} : Set G) ⊓ L, x * b = b * x)
    (hx : x ∈ L ⊔ zpowers t) : x ∈ zpowers t ⊔ zpowers u := by
  have hcomm : zpowers t ≤ centralizer (L : Set G) := zpowers_le.2 ht
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcomm hx
  have htu : t * u = u * t := (mem_centralizer_iff.1 ht u hu).symm
  have hcu : c * u = u * c := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    exact ((Commute.zpow_left (show Commute t u from htu) k)).eq
  have hcB : ∀ b ∈ centralizer ({u} : Set G) ⊓ L, c * b = b * c := by
    intro b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    have : Commute t b := (mem_centralizer_iff.1 ht b hb.2).symm
    exact (this.zpow_left k).eq
  have hau : a * u = u * a := by
    have h1 : a * c * u = u * (a * c) := hxu
    calc a * u = a * (c * u) * c⁻¹ := by rw [hcu]; group
      _ = (a * c * u) * c⁻¹ := by group
      _ = u * (a * c) * c⁻¹ := by rw [h1]
      _ = u * a := by group
  have haB : ∀ b ∈ centralizer ({u} : Set G) ⊓ L, a * b = b * a := by
    intro b hb
    have h1 := hxB b hb
    have h2 := hcB b hb
    calc a * b = a * (c * b) * c⁻¹ := by rw [h2]; group
      _ = (a * c * b) * c⁻¹ := by group
      _ = (b * (a * c)) * c⁻¹ := by rw [h1]
      _ = b * a := by group
  rcases hZ a ha hau haB with rfl | rfl
  · rw [one_mul]
    exact mem_sup_left hc
  · exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hc)

theorem commute_of_relIndex_dvd_two {L : Subgroup G} {t u : G}
    (ht : t ∈ centralizer (L : Set G)) (hu : u ∈ L)
    (hZ : ∀ l ∈ L, l * u = u * l → (∀ b ∈ centralizer ({u} : Set G) ⊓ L, l * b = b * l) →
      l = 1 ∨ l = u)
    (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣ 2) :
    ∀ x y : G, x ∈ centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) →
      y ∈ centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) →
      (∀ b ∈ centralizer ({u} : Set G) ⊓ L, x * b = b * x) →
      (∀ b ∈ centralizer ({u} : Set G) ⊓ L, y * b = b * y) → x * y = y * x := by
  intro x y hx hy hxB hyB
  have htu : t * u = u * t := (mem_centralizer_iff.1 ht u hu).symm
  set N : Subgroup G := L ⊔ zpowers t with hN
  have hE : ∀ z ∈ zpowers t ⊔ zpowers u, ∀ w : G, w * t = t * w → w * u = u * w →
      z * w = w * z := by
    intro z hz w hwt hwu
    have hle : zpowers t ⊔ zpowers u ≤ centralizer ({w} : Set G) :=
      sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hwt.symm))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 hwu.symm))
    exact mem_centralizer_singleton_iff.1 (hle hz)
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 hx.1
  have hxu : x * u = u * x := mem_centralizer_singleton_iff.1 hx.2
  have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 hy.1
  have hyu : y * u = u * y := mem_centralizer_singleton_iff.1 hy.2
  by_cases hxN : x ∈ N
  · have hxE := mem_zpowers_sup_zpowers_of_mem_sup ht hu hZ hxu hxB hxN
    exact hE x hxE y hyt hyu
  by_cases hyN : y ∈ N
  · have hyE := mem_zpowers_sup_zpowers_of_mem_sup ht hu hZ hyu hyB hyN
    exact (hE y hyE x hxt hxu).symm
  set M : Subgroup G := centralizer ({t} : Set G) with hM
  have hxM : x ∈ M := hx.1
  have hyM : y ∈ M := hy.1
  have hmem : x * y⁻¹ ∈ N := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
    · exfalso
      apply hxN
      have h1' : N.subgroupOf M = ⊤ :=
        Subgroup.index_eq_one.1 (by rw [Subgroup.relIndex] at h1; exact h1)
      have : (⟨x, hxM⟩ : M) ∈ N.subgroupOf M := by rw [h1']; exact mem_top _
      exact this
    · have h2' : (N.subgroupOf M).index = 2 := by rw [Subgroup.relIndex] at h2; exact h2
      have hx' : (⟨x, hxM⟩ : M) ∉ N.subgroupOf M := hxN
      have hy' : (⟨y, hyM⟩ : M) ∉ N.subgroupOf M := hyN
      have := (Subgroup.mul_mem_iff_of_index_two h2').2
        (iff_of_false hx' (fun h => hy' ((Subgroup.inv_mem_iff _).1 h)))
      · exact this
  have hxyu : x * y⁻¹ * u = u * (x * y⁻¹) := by
    calc x * y⁻¹ * u = x * (y⁻¹ * u) := by rw [mul_assoc]
      _ = x * (u * y⁻¹) := by
        congr 1
        have : y * u = u * y := hyu
        calc y⁻¹ * u = y⁻¹ * (u * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * u) * y⁻¹ := by rw [this]
          _ = u * y⁻¹ := by group
      _ = (x * u) * y⁻¹ := by rw [← mul_assoc]
      _ = (u * x) * y⁻¹ := by rw [hxu]
      _ = u * (x * y⁻¹) := by rw [mul_assoc]
  have hxyB : ∀ b ∈ centralizer ({u} : Set G) ⊓ L, x * y⁻¹ * b = b * (x * y⁻¹) := by
    intro b hb
    have h1 := hxB b hb
    have h2 : y⁻¹ * b = b * y⁻¹ := by
      have := hyB b hb
      calc y⁻¹ * b = y⁻¹ * (b * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * b) * y⁻¹ := by rw [this]
        _ = b * y⁻¹ := by group
    calc x * y⁻¹ * b = x * (y⁻¹ * b) := by rw [mul_assoc]
      _ = x * (b * y⁻¹) := by rw [h2]
      _ = (x * b) * y⁻¹ := by rw [← mul_assoc]
      _ = (b * x) * y⁻¹ := by rw [h1]
      _ = b * (x * y⁻¹) := by rw [mul_assoc]
  have hE' := mem_zpowers_sup_zpowers_of_mem_sup ht hu hZ hxyu hxyB hmem
  have hcy : x * y⁻¹ * y = y * (x * y⁻¹) := hE _ hE' y hyt hyu
  have h3 : x = y * x * y⁻¹ := by
    calc x = x * y⁻¹ * y := by group
      _ = y * (x * y⁻¹) := hcy
      _ = y * x * y⁻¹ := by group
  calc x * y = (y * x * y⁻¹) * y := by rw [← h3]
    _ = y * x := by group

theorem eq_one_or_eq_of_isDoubleCoverOfAlt {B : Type} [Group B] {n : ℕ}
    (hB : IsDoubleCoverOfAlt B n) {u : B} (hu : u ∈ center B) (hu1 : u ≠ 1) {z : B}
    (hz : z ∈ center B) : z = 1 ∨ z = u := by
  have hc : Nat.card (center B) = 2 := hB.2.1
  by_contra hcon
  push Not at hcon
  obtain ⟨hz1, hzu⟩ := hcon
  have hfin : Finite (center B) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : center B)).1 hc
  have h1 : (⟨u, hu⟩ : center B) = y := hy _ (fun h => hu1 (congrArg Subtype.val h))
  have h2 : (⟨z, hz⟩ : center B) = y := hy _ (fun h => hz1 (congrArg Subtype.val h))
  exact hzu (congrArg Subtype.val (h2.trans h1.symm))

end CFSG.EvenSporadicStandard.McLStd

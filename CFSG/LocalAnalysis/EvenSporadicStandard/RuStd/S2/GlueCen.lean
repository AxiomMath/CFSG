module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Interfaces

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup

section Gen

variable {G : Type} [Group G]

abbrev CenG (a : G) : Type := ↥(centralizer ({a} : Set G))

theorem card_cen_eq {K : Subgroup G} (v : K) :
    Nat.card (centralizer ({v} : Set K)) =
      Nat.card (K ⊓ centralizer ({(v : G)} : Set G) : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨((x : K) : G), Subgroup.mem_inf.2 ⟨(x : K).2,
        mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2))⟩⟩
      invFun := fun y => ⟨⟨y, (Subgroup.mem_inf.1 y.2).1⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_cen_dvd (a : G) (x : CenG a) :
    Nat.card (centralizer ({x} : Set (CenG a))) ∣ Nat.card (centralizer ({(x : G)} : Set G)) := by
  rw [card_cen_eq]
  exact Subgroup.card_dvd_of_le inf_le_right

@[expose] noncomputable def oddCoreCen (r : G) : Subgroup G :=
  (CFSG.oddCore (CenG r)).map (centralizer ({r} : Set G)).subtype

theorem mem_oddCoreCen_iff {r : G} (x : CenG r) :
    (x : G) ∈ oddCoreCen r ↔ x ∈ CFSG.oddCore (CenG r) := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem oddCoreCen_le (r : G) : oddCoreCen r ≤ centralizer ({r} : Set G) := by
  rintro _ ⟨y, _, rfl⟩
  exact y.2

theorem oddCoreCen_norm (r : G) {y : G} (hy : y ∈ centralizer ({r} : Set G)) {n : G}
    (hn : n ∈ oddCoreCen r) : y * n * y⁻¹ ∈ oddCoreCen r := by
  obtain ⟨n', hn', rfl⟩ := hn
  exact ⟨⟨y, hy⟩ * n' * ⟨y, hy⟩⁻¹,
    (inferInstance : (CFSG.oddCore (CenG r)).Normal).conj_mem n' hn' ⟨y, hy⟩, rfl⟩

theorem odd_card_oddCoreCen [Finite G] (r : G) : Odd (Nat.card (oddCoreCen r)) := by
  rw [oddCoreCen, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact odd_card_oddCore _

theorem le_oddCoreCen {r : G} {N : Subgroup G} (hN : N ≤ centralizer ({r} : Set G))
    (hnorm : ∀ y ∈ centralizer ({r} : Set G), ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N ≤ oddCoreCen r := by
  have hnormal : (N.subgroupOf (centralizer ({r} : Set G))).Normal :=
    ⟨fun n hn g => hnorm g g.2 n hn⟩
  have hcard : Nat.card (N.subgroupOf (centralizer ({r} : Set G))) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
  have hle := le_oddCore hnormal (hcard ▸ hodd)
  intro n hn
  exact ⟨⟨n, hN hn⟩, hle hn, rfl⟩

theorem zpowers_le_oddCoreCen {r : G} (hr3 : orderOf r = 3) : zpowers r ≤ oddCoreCen r := by
  refine le_oddCoreCen (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) ?_ ?_
  · intro y hy n hn
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have h : y * r = r * y := mem_centralizer_singleton_iff.1 hy
    rw [(Commute.zpow_right (show Commute y r from h) k).eq]
    simp
  · rw [Nat.card_zpowers, hr3]
    decide

end Gen

section KL

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

theorem comm_zpowers (hc : Config G L t) {l : G} (hl : l ∈ L) {z : G}
    (hz : z ∈ zpowers t) : l * z = z * l := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  exact (Commute.zpow_right (show Commute l t from hc.comm l hl) k).eq

theorem mem_of_odd_orderOf (hc : Config G L t) {x : G} (hxt : x * t = t * x)
    (hodd : Odd (orderOf x)) : x ∈ L := by
  rcases hc.mem_cases (mem_centralizer_singleton_iff.2 hxt) with h | ⟨l, hl, rfl⟩
  · exact h
  · exfalso
    obtain ⟨m, hm⟩ := hodd
    have h1 : (t * l) ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
    have hcomm : Commute t l := (hc.comm l hl).symm
    have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact hc.z_sq
    have h2 : t ^ (2 * m + 1) = t := by rw [pow_succ, pow_mul, ht2, one_pow, one_mul]
    rw [hcomm.mul_pow, h2] at h1
    apply hc.z_not_mem
    have : t = (l ^ (2 * m + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_mem (pow_mem hl _)

theorem cen_odd_le (hc : Config G L t) (h3 : RuThreeFacts L) {r : G} (hrL : r ∈ L)
    (hr3 : orderOf r = 3) {N : Subgroup G} (hN : N ≤ centralizer ({r} : Set G))
    (hnorm : ∀ y ∈ centralizer ({r} : Set G), ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) {x : G} (hx : x ∈ N) (hxt : x * t = t * x) : x ∈ zpowers r := by
  have hxL : x ∈ L := mem_of_odd_orderOf hc hxt
    (Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hx))
  set rL : L := ⟨r, hrL⟩ with hrL_def
  have hrL3 : orderOf rL = 3 := by rw [← hr3]; exact Subgroup.orderOf_mk r hrL
  set N'' : Subgroup L := (N ⊓ centralizer ({t} : Set G)).subgroupOf L with hN''
  have hle : N'' ≤ centralizer ({rL} : Set L) := by
    intro n hn
    have hn' := Subgroup.mem_subgroupOf.1 hn
    have : (n : G) * r = r * (n : G) :=
      mem_centralizer_singleton_iff.1 (hN (Subgroup.mem_inf.1 hn').1)
    exact mem_centralizer_singleton_iff.2 (Subtype.ext this)
  have hnorm' : ∀ y ∈ centralizer ({rL} : Set L), ∀ n ∈ N'', y * n * y⁻¹ ∈ N'' := by
    intro y hy n hn
    have hn' := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hn)
    have hyr : (y : G) ∈ centralizer ({r} : Set G) :=
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy))
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hnorm _ hyr _ hn'.1, ?_⟩)
    rw [mem_centralizer_singleton_iff]
    have h1 : Commute (n : G) t := mem_centralizer_singleton_iff.1 hn'.2
    have h2 : Commute (y : G) t := hc.comm y y.2
    exact ((h2.mul_left h1).mul_left h2.inv_left).eq
  have hodd' : Odd (Nat.card N'') := by
    refine Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective
      ((L.subtype.comp N''.subtype).codRestrict N fun n =>
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 n.2)).1) ?_)
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have hxN'' : (⟨x, hxL⟩ : L) ∈ N'' :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 hxt⟩)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (h3.oddCore rL hrL3 N'' hle hnorm' hodd' hxN'')
  exact mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem cen_odd_le_conj (hc : Config G L t) (h3 : RuThreeFacts L) {r g : G}
    (hr'L : g⁻¹ * r * g ∈ L) (hr3 : orderOf r = 3) {N : Subgroup G}
    (hN : N ≤ centralizer ({r} : Set G))
    (hnorm : ∀ y ∈ centralizer ({r} : Set G), ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) {x : G} (hx : x ∈ N)
    (hxt : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x) : x ∈ zpowers r := by
  set r' : G := g⁻¹ * r * g with hr'
  set N' : Subgroup G := N.map (MulAut.conj g⁻¹).toMonoidHom with hN'
  have hmem : ∀ y : G, y ∈ N' ↔ g * y * g⁻¹ ∈ N := by
    intro y
    constructor
    · rintro ⟨n, hn, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hn
    · intro h
      exact ⟨g * y * g⁻¹, h, by simp [mul_assoc]⟩
  have hr'3 : orderOf r' = 3 := by
    rw [← hr3]
    exact SemiconjBy.orderOf_eq g (show SemiconjBy g r' r by simp [SemiconjBy, r', mul_assoc])
  have hN'le : N' ≤ centralizer ({r'} : Set G) := by
    intro y hy
    have h := mem_centralizer_singleton_iff.1 (hN ((hmem y).1 hy))
    rw [mem_centralizer_singleton_iff]
    calc y * (g⁻¹ * r * g) = g⁻¹ * ((g * y * g⁻¹) * r) * g := by group
      _ = g⁻¹ * (r * (g * y * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * r * g) * y := by group
  have hnorm' : ∀ y ∈ centralizer ({r'} : Set G), ∀ n ∈ N', y * n * y⁻¹ ∈ N' := by
    intro y hy n hn
    rw [hmem]
    have hy' : g * y * g⁻¹ ∈ centralizer ({r} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h := mem_centralizer_singleton_iff.1 hy
      calc g * y * g⁻¹ * r = g * (y * (g⁻¹ * r * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * r * g) * y) * g⁻¹ := by rw [h]
        _ = r * (g * y * g⁻¹) := by group
    have h := hnorm _ hy' _ ((hmem n).1 hn)
    have e : g * (y * n * y⁻¹) * g⁻¹ = (g * y * g⁻¹) * (g * n * g⁻¹) * (g * y * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact h
  have hodd' : Odd (Nat.card N') := by
    rw [hN', Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact hodd
  have hx' : g⁻¹ * x * g ∈ N' := by
    rw [hmem]
    simpa [mul_assoc] using hx
  have hxt' : (g⁻¹ * x * g) * t = t * (g⁻¹ * x * g) := by
    calc (g⁻¹ * x * g) * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hxt]
      _ = t * (g⁻¹ * x * g) := by group
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (cen_odd_le hc h3 hr'L hr'3 hN'le hnorm' hodd' hx' hxt')
  refine mem_zpowers_iff.2 ⟨k, ?_⟩
  have h1 : r' ^ k = g⁻¹ * r ^ k * g := by
    have := conj_zpow (a := g⁻¹) (b := r) (i := k)
    simpa [r'] using this
  calc r ^ k = g * (g⁻¹ * r ^ k * g) * g⁻¹ := by group
    _ = g * r' ^ k * g⁻¹ := by rw [h1]
    _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hk]
    _ = x := by group

end KL

end CFSG.EvenSporadicStandard.RuStd.S2.Glue

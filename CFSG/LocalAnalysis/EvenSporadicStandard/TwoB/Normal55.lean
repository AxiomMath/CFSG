module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Level55

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.EvenSporadicStandard.TwoFi22
open scoped Pointwise

variable {G : Type} [Group G]

theorem isTwoConstrained_centralizer_map (e : G ≃* G) {z : G}
    (h : IsTwoConstrained (centralizer ({z} : Set G))) :
    IsTwoConstrained (centralizer ({e z} : Set G)) := by
  intro y hy
  obtain ⟨hyC, hyO⟩ := mem_inf.1 hy
  obtain ⟨x, rfl⟩ := e.surjective y
  have hxC : x ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hyC ⊢
    apply e.injective
    rw [map_mul, map_mul]
    exact hyC
  have hxO : x ∈ centralizer ((O2In (centralizer ({z} : Set G)) : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro o ho
    have ho' : e o ∈ O2In (centralizer ({e z} : Set G)) := by
      rw [O2In_centralizer_map e z]
      exact Subgroup.mem_map_of_mem _ ho
    apply e.injective
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hyO _ ho'
  have := h (mem_inf.2 ⟨hxC, hxO⟩)
  rw [O2In_centralizer_map e z]
  exact Subgroup.mem_map_of_mem _ this

theorem centPair_le_normPair (z t : G) : centPair z t ≤ normPair z t :=
  centralizer_le_normalizer _

theorem conj_mem_sup_of_conj_mem {A B S : Subgroup G} {g : G}
    (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ S) (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ S) :
    ∀ y ∈ A ⊔ B, g * y * g⁻¹ ∈ S := by
  intro y hy
  have hle : (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ S := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact hA a ha
    · rintro _ ⟨b, hb, rfl⟩
      exact hB b hb
  exact hle ⟨y, hy, rfl⟩

theorem conj_mem_zpowers_of_conj_mem {S : Subgroup G} {g b : G} (hb : g * b * g⁻¹ ∈ S) :
    ∀ y ∈ zpowers b, g * y * g⁻¹ ∈ S := by
  intro y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  rw [← conj_zpow]
  exact zpow_mem hb k

theorem mem_or_exists_mul_of_mem_sup_zpowers {R : Subgroup G} {x : G}
    (hxN : x ∈ normalizer (R : Set G)) (hx2 : x ^ 2 ∈ R) {u : G} (hu : u ∈ R ⊔ zpowers x) :
    u ∈ R ∨ ∃ r ∈ R, u = r * x := by
  have hLE : zpowers x ≤ normalizer (R : Set G) := zpowers_le.2 hxN
  have hu' : u ∈ (R : Set G) * (zpowers x : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hLE]
    exact hu
  obtain ⟨r, hr, y, hy, rfl⟩ := Set.mem_mul.1 hu'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_ofNat]
    exact mul_mem hr (zpow_mem hx2 m)
  · right
    refine ⟨r * (x ^ 2) ^ m, mul_mem hr (zpow_mem hx2 m), ?_⟩
    rw [zpow_add_one, zpow_mul, ← mul_assoc, zpow_ofNat]

theorem isPGroup_sup_zpowers_of_sq_mem {R : Subgroup G} (hR : IsPGroup 2 R) {x : G}
    (hxN : x ∈ normalizer (R : Set G)) (hx2 : x ^ 2 ∈ R) : IsPGroup 2 ↥(R ⊔ zpowers x) := by
  intro u
  rcases mem_or_exists_mul_of_mem_sup_zpowers hxN hx2 u.2 with hu | ⟨r, hr, hu⟩
  · obtain ⟨k, hk⟩ := hR ⟨u, hu⟩
    have hk' : (u : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact ⟨k, Subtype.ext hk'⟩
  · have h2 : (u : G) ^ 2 ∈ R := by
      have e : (u : G) ^ 2 = (r * (x * r * x⁻¹)) * x ^ 2 := by rw [hu, sq]; group
      rw [e]
      exact mul_mem (mul_mem hr ((mem_normalizer_iff.1 hxN r).1 hr)) hx2
    obtain ⟨k, hk⟩ := hR ⟨(u : G) ^ 2, h2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : ((u : G) ^ 2) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    show (u : G) ^ 2 ^ (k + 1) = 1
    rw [pow_succ, pow_mul']
    exact hk'

theorem conj_mem_O2In_sup_zpowers {K : Subgroup G} {x : G}
    (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ O2In K) {k : G} (hk : k ∈ K) :
    ∀ u ∈ O2In K ⊔ zpowers x, k * u * k⁻¹ ∈ O2In K ⊔ zpowers x := by
  refine conj_mem_sup_of_conj_mem (fun a ha => mem_sup_left ?_)
    (conj_mem_zpowers_of_conj_mem ?_)
  · exact (normal_subgroupOf_O2In K).conj_mem ⟨a, O2In_le K ha⟩ (mem_subgroupOf.2 ha) ⟨k, hk⟩
  · have e : k * x * k⁻¹ = (x * k * x⁻¹ * k⁻¹)⁻¹ * x := by group
    rw [e]
    exact mul_mem (mem_sup_left (inv_mem (hxK k hk))) (mem_sup_right (mem_zpowers x))

section Main

variable [Finite G] {t z : G}

theorem Level55.not_conj_z_t (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z)) (g : G) :
    g * z * g⁻¹ ≠ t := by
  intro hg
  apply d.not_constrained
  have := isTwoConstrained_centralizer_map (MulAut.conj g) h54
  rwa [MulAut.conj_apply, hg] at this

theorem Level55.eq_of_mem_pair (d : Level55 G t z) {y : G} (hy : y ∈ pair z t) :
    y = 1 ∨ y = z ∨ y = t ∨ y = z * t := by
  have hle : zpowers t ≤ centralizer ((zpowers z : Subgroup G) : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact ((Commute.zpow_left (show Commute z t from d.zt_comm) k).eq)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hy
  rcases eq_one_or_eq_of_mem_zpowers_two d.z_ord ha with rfl | rfl <;>
    rcases eq_one_or_eq_of_mem_zpowers_two d.t_ord hb with rfl | rfl <;> simp

private theorem Level55.mul_self_z (d : Level55 G t z) : z * z = 1 := by
  rw [← sq, ← d.z_ord]
  exact pow_orderOf_eq_one z

theorem Level55.inv_conj_of_swap (d : Level55 G t z) {x : G} (hxz : x * z = z * x)
    (hxt : x * t * x⁻¹ = t * z) : x⁻¹ * z * x = z ∧ x⁻¹ * t * x = t * z := by
  have hzz := d.mul_self_z
  have hxz' : x * z * x⁻¹ = z := by rw [hxz, mul_inv_cancel_right]
  refine ⟨by rw [mul_assoc, ← hxz, inv_mul_cancel_left], ?_⟩
  have h3 : x * (t * z) * x⁻¹ = t := by
    calc x * (t * z) * x⁻¹ = (x * t * x⁻¹) * (x * z * x⁻¹) := by group
      _ = (t * z) * z := by rw [hxt, hxz']
      _ = t := by rw [mul_assoc, hzz, mul_one]
  calc x⁻¹ * t * x = x⁻¹ * (x * (t * z) * x⁻¹) * x := by rw [h3]
    _ = t * z := by group

theorem mem_normPair_of_swap {x : G} (hxz : x * z = z * x) (hxt : x * t * x⁻¹ = t * z) :
    x ∈ normPair z t := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hxz' : x * z * x⁻¹ = z := by rw [hxz, mul_inv_cancel_right]
  refine conj_mem_sup_of_conj_mem (A := zpowers z) (B := zpowers t) (S := pair z t)
    (conj_mem_zpowers_of_conj_mem ?_) (conj_mem_zpowers_of_conj_mem ?_) n hn
  · rw [hxz']
    exact z_mem_pair z t
  · rw [hxt]
    exact mul_mem (t_mem_pair z t) (z_mem_pair z t)

theorem Level55.normPair_conj_z (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z)) {x : G}
    (hxz : x * z = z * x) (hxt : x * t * x⁻¹ = t * z) {n : G} (hn : n ∈ normPair z t) :
    n * z * n⁻¹ = z := by
  have hzz := d.mul_self_z
  obtain ⟨h1, h2⟩ := d.inv_conj_of_swap hxz hxt
  have hnz : n * z * n⁻¹ ∈ pair z t := (mem_normalizer_iff.1 hn z).1 (z_mem_pair z t)
  rcases d.eq_of_mem_pair hnz with h | h | h | h
  · exfalso
    have hz1 : z = 1 := by simpa using h
    have : orderOf z = 1 := by rw [hz1, orderOf_one]
    have := d.z_ord
    omega
  · exact h
  · exact absurd h (d.not_conj_z_t h54 n)
  · exfalso
    refine d.not_conj_z_t h54 (x⁻¹ * n) ?_
    calc x⁻¹ * n * z * (x⁻¹ * n)⁻¹ = x⁻¹ * (n * z * n⁻¹) * x := by group
      _ = x⁻¹ * (z * t) * x := by rw [h]
      _ = (x⁻¹ * z * x) * (x⁻¹ * t * x) := by group
      _ = z * (t * z) := by rw [h1, h2]
      _ = t := by rw [← mul_assoc, d.zt_comm, mul_assoc, hzz, mul_one]

theorem Level55.normPair_le_centZ (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z))
    {x : G} (hxz : x * z = z * x) (hxt : x * t * x⁻¹ = t * z) : normPair z t ≤ centZ z :=
  fun _ hn => mem_centralizer_singleton_iff.2
    (mul_inv_eq_iff_eq_mul.1 (d.normPair_conj_z h54 hxz hxt hn))

theorem Level55.normPair_conj_t (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z))
    {n : G} (hn : n ∈ normPair z t) : n * t * n⁻¹ = t ∨ n * t * n⁻¹ = t * z := by
  have hnt : n * t * n⁻¹ ∈ pair z t := (mem_normalizer_iff.1 hn t).1 (t_mem_pair z t)
  rcases d.eq_of_mem_pair hnt with h | h | h | h
  · exfalso
    have ht1 : t = 1 := by simpa using h
    have : orderOf t = 1 := by rw [ht1, orderOf_one]
    have := d.t_ord
    omega
  · exfalso
    refine d.not_conj_z_t h54 n⁻¹ ?_
    rw [← h]
    group
  · exact Or.inl h
  · exact Or.inr (h.trans d.zt_comm)

theorem Level55.mem_centPair_or_inv_mul_mem (d : Level55 G t z)
    (h54 : IsTwoConstrained (centZ z)) {x : G} (hxz : x * z = z * x)
    (hxt : x * t * x⁻¹ = t * z) {n : G} (hn : n ∈ normPair z t) :
    n ∈ centPair z t ∨ x⁻¹ * n ∈ centPair z t := by
  have hzz := d.mul_self_z
  obtain ⟨h1, h2⟩ := d.inv_conj_of_swap hxz hxt
  have hnz := d.normPair_conj_z h54 hxz hxt hn
  rcases d.normPair_conj_t h54 hn with h | h
  · left
    rw [mem_centPair_iff]
    exact ⟨(mul_inv_eq_iff_eq_mul.1 hnz).symm, (mul_inv_eq_iff_eq_mul.1 h).symm⟩
  · right
    rw [mem_centPair_iff]
    refine ⟨(mul_inv_eq_iff_eq_mul.1 ?_).symm, (mul_inv_eq_iff_eq_mul.1 ?_).symm⟩
    · calc x⁻¹ * n * z * (x⁻¹ * n)⁻¹ = x⁻¹ * (n * z * n⁻¹) * x := by group
        _ = x⁻¹ * z * x := by rw [hnz]
        _ = z := h1
    · calc x⁻¹ * n * t * (x⁻¹ * n)⁻¹ = x⁻¹ * (n * t * n⁻¹) * x := by group
        _ = x⁻¹ * (t * z) * x := by rw [h]
        _ = (x⁻¹ * t * x) * (x⁻¹ * z * x) := by group
        _ = t * z * z := by rw [h1, h2]
        _ = t := by rw [mul_assoc, hzz, mul_one]

theorem Level55.normal_subgroupOf_O2In_sup_zpowers (d : Level55 G t z)
    (h54 : IsTwoConstrained (centZ z)) {x : G} (hxz : x * z = z * x)
    (hxt : x * t * x⁻¹ = t * z)
    (hxK : ∀ k ∈ centPair z t, x * k * x⁻¹ * k⁻¹ ∈ O2In (centPair z t)) :
    ((O2In (centPair z t) ⊔ zpowers x).subgroupOf (normPair z t)).Normal := by
  refine ⟨fun u hu n => ?_⟩
  rw [mem_subgroupOf] at hu ⊢
  have hxU : x ∈ O2In (centPair z t) ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  rcases d.mem_centPair_or_inv_mul_mem h54 hxz hxt n.2 with hn | hn
  · exact conj_mem_O2In_sup_zpowers hxK hn _ hu
  · have e : (n : G) * u * (n : G)⁻¹ = x * ((x⁻¹ * n) * u * (x⁻¹ * n)⁻¹) * x⁻¹ := by group
    show (n : G) * u * (n : G)⁻¹ ∈ _
    rw [e]
    exact mul_mem (mul_mem hxU (conj_mem_O2In_sup_zpowers hxK hn _ hu)) (inv_mem hxU)

theorem Level55.O2In_sup_zpowers_le (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z))
    {x : G} (hxz : x * z = z * x) (hxt : x * t * x⁻¹ = t * z)
    (hxN : x ∈ normalizer ((O2In (centPair z t) : Subgroup G) : Set G))
    (hxK : ∀ k ∈ centPair z t, x * k * x⁻¹ * k⁻¹ ∈ O2In (centPair z t))
    (hx2 : x ^ 2 ∈ O2In (centPair z t)) :
    O2In (centPair z t) ⊔ zpowers x ≤ O2In (normPair z t) := by
  refine le_O2In ?_ (d.normal_subgroupOf_O2In_sup_zpowers h54 hxz hxt hxK)
    (isPGroup_sup_zpowers_of_sq_mem (isPGroup_O2In _) hxN hx2)
  exact sup_le ((O2In_le _).trans (centPair_le_normPair z t))
    (zpowers_le.2 (mem_normPair_of_swap hxz hxt))

theorem Level55.O2In_normPair_le (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z))
    {x : G} (hxz : x * z = z * x) (hxt : x * t * x⁻¹ = t * z)
    (hxN : x ∈ normalizer ((O2In (centPair z t) : Subgroup G) : Set G))
    (hxK : ∀ k ∈ centPair z t, x * k * x⁻¹ * k⁻¹ ∈ O2In (centPair z t))
    (hx2 : x ^ 2 ∈ O2In (centPair z t)) :
    O2In (normPair z t) ≤ O2In (centPair z t) ⊔ zpowers x := by
  have hVK : O2In (normPair z t) ⊓ centPair z t ≤ O2In (centPair z t) := by
    refine le_O2In inf_le_right ?_ ((isPGroup_O2In _).to_le inf_le_left)
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    refine mem_inf.2 ⟨?_, (centPair z t).mul_mem ((centPair z t).mul_mem g.2 hn.2)
      ((centPair z t).inv_mem g.2)⟩
    have := (normal_subgroupOf_O2In (normPair z t)).conj_mem
      ⟨(n : G), centPair_le_normPair z t n.2⟩ (by rw [mem_subgroupOf]; exact hn.1)
      ⟨(g : G), centPair_le_normPair z t g.2⟩
    exact this
  have hxU : x ∈ O2In (centPair z t) ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  have hxV : x ∈ O2In (normPair z t) := d.O2In_sup_zpowers_le h54 hxz hxt hxN hxK hx2 hxU
  intro v hv
  rcases d.mem_centPair_or_inv_mul_mem h54 hxz hxt (O2In_le _ hv) with hvK | hxvK
  · exact mem_sup_left (hVK (mem_inf.2 ⟨hv, hvK⟩))
  · have h2 : x⁻¹ * v ∈ O2In (centPair z t) :=
      hVK (mem_inf.2 ⟨mul_mem (inv_mem hxV) hv, hxvK⟩)
    have e : v = x * (x⁻¹ * v) := by group
    rw [e]
    exact mul_mem hxU (mem_sup_left h2)

set_option linter.unusedVariables false in
theorem Level55.O2In_normPair_eq (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z)) {x : G}
    (hxz : x * z = z * x) (hxt : x * t * x⁻¹ = t * z)
    (hxN : x ∈ normalizer ((O2In (centPair z t) : Subgroup G) : Set G))
    (hxK : ∀ k ∈ centPair z t, x * k * x⁻¹ * k⁻¹ ∈ O2In (centPair z t))
    (hx2 : x ^ 2 ∈ O2In (centPair z t)) (hxn : x ∉ O2In (centPair z t)) :
    O2In (normPair z t) = O2In (centPair z t) ⊔ zpowers x :=
  le_antisymm (d.O2In_normPair_le h54 hxz hxt hxN hxK hx2)
    (d.O2In_sup_zpowers_le h54 hxz hxt hxN hxK hx2)

end Main

end CFSG.EvenSporadicStandard.TwoB

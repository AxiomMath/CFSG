module

public import CFSG.GF2Type.CenterFour.CaseBPsiBasic

import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

private theorem card_inf_centerAt (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) :
    Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓ centerAt z : Subgroup G) = 2 := by
  obtain ⟨k, hZk, hk4, hk2⟩ := hC.exists_generator
  have hz1 : z ≠ 1 := by
    intro h
    have h2 := hC.orderOf_eq
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hkZ : k ∈ centerAt z := hZk ▸ Subgroup.mem_zpowers k
  have hzH : z ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓ centerAt z :=
    Subgroup.mem_inf.mpr ⟨CaseB.mem hC hH, hC.mem_center⟩
  have hkR : k ∉ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) := by
    intro hkR
    have hc : k * (g⁻¹ * z * g) = (g⁻¹ * z * g) * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hkR).2
    have h1 := hC.inv_of_not_mem_centralizer hH hK hkZ
    have h2 : (g⁻¹ * z * g) * k * (g⁻¹ * z * g)⁻¹ = k := by
      rw [← hc, mul_inv_cancel_right]
    have hinv : k⁻¹ = k := by rw [← h1]; exact h2
    have hkk : k * k = 1 := inv_eq_iff_mul_eq_one.mp hinv
    apply hz1
    rw [← hk2, sq]
    exact hkk
  have hdvd : Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓ centerAt z : Subgroup G)
      ∣ Nat.card (centerAt z) :=
    Subgroup.card_dvd_of_le (inf_le_right : coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓
      centerAt z ≤ centerAt z)
  rw [hC.card_center] at hdvd
  have hne4 : Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓ centerAt z : Subgroup G)
      ≠ 4 := by
    intro h4
    have hHZ : coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓ centerAt z = centerAt z :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hC.card_center, h4])
    have hkH : k ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓ centerAt z := by
      rw [hHZ]
      exact hkZ
    exact hkR (Subgroup.mem_inf.mp hkH).1
  have hne1 : Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓ centerAt z : Subgroup G)
      ≠ 1 := by
    intro h1
    obtain ⟨hsub, _⟩ := Nat.card_eq_one_iff_unique.mp h1
    exact hz1 (congrArg Subtype.val
      (@Subsingleton.elim _ hsub ⟨z, hzH⟩ ⟨1, one_mem _⟩))
  generalize Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊓ centerAt z : Subgroup G) =
    m at hdvd hne4 hne1 ⊢
  have hle : m ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases m <;> first | omega | norm_num at hdvd

theorem CaseB.card_sup (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) :
    Nat.card ((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z : Subgroup G) =
      2 * Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) := by
  have hcomm : ∀ x ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G),
      ∀ y ∈ centerAt z, x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp
      (hC.core_le_centralizer_center (Subgroup.mem_inf.mp hx).1) y hy).symm
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) (centerAt z) hcomm).1
  rw [card_inf_centerAt hC hH hK, hC.card_center] at hprod
  omega

private theorem psi_eq_iff_inv_mul_mem (hC : Config z n) {z₁ a b : G} (ha : a ∈ coreAt z)
    (hb : b ∈ coreAt z) :
    psi z₁ a = psi z₁ b ↔ a⁻¹ * b ∈ coreAt z ⊓ centralizer ({z₁} : Set G) := by
  rw [CaseB.psi_eq_psi_iff hC ha hb]
  constructor
  · intro h
    have h' := inv_mem_iff.mpr h
    rwa [mul_inv_rev, inv_inv] at h'
  · intro h
    have h' := inv_mem_iff.mpr h
    rwa [mul_inv_rev, inv_inv] at h'

theorem CaseB.ncard_range_psi (hC : Config z n) (z₁ : G) :
    Set.ncard ((fun q => psi z₁ q) '' (coreAt z : Set G)) *
        Nat.card (coreAt z ⊓ centralizer ({z₁} : Set G) : Subgroup G) =
      Nat.card (coreAt z) := by
  let H : Subgroup (coreAt z) := (coreAt z ⊓ centralizer ({z₁} : Set G)).subgroupOf (coreAt z)
  let F : (coreAt z) ⧸ H → G :=
    Quotient.lift (fun q : coreAt z => psi z₁ (q : G)) (fun a b hab => by
      have h1 : (a : G)⁻¹ * (b : G) ∈ coreAt z ⊓ centralizer ({z₁} : Set G) :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab)
      exact (psi_eq_iff_inv_mul_mem hC a.2 b.2).mpr h1)
  have hinj : Function.Injective F := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    have hpsi : psi z₁ (a : G) = psi z₁ (b : G) := hxy
    have h1 := (psi_eq_iff_inv_mul_mem hC a.2 b.2).mp hpsi
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    exact Subgroup.mem_subgroupOf.mpr h1
  have hrange : Set.range F = (fun q => psi z₁ q) '' (coreAt z : Set G) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      exact ⟨(a : G), a.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨QuotientGroup.mk (⟨q, hq⟩ : coreAt z), rfl⟩
  have hset : Set.ncard ((fun q => psi z₁ q) '' (coreAt z : Set G)) =
      Nat.card ((coreAt z) ⧸ H) := by
    rw [← hrange, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
  have hcardQ := Subgroup.card_eq_card_quotient_mul_card_subgroup H
  have hcardH : Nat.card H = Nat.card (coreAt z ⊓ centralizer ({z₁} : Set G) : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hset, hcardQ, hcardH]

private theorem eq_pow_of_dvd_bounds {a n : ℕ} (hdvd : a ∣ 2 ^ (2 * n + 2))
    (hle : a ≤ 2 ^ (n + 1)) (hsq : 2 ^ (2 * n + 1) ≤ a * a) : a = 2 ^ (n + 1) := by
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj1 : n + 1 ≤ j := by
    by_contra hcon
    have h2j : 2 ^ j ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm : 2 ^ j * 2 ^ j ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul h2j h2j
    have e : (2 : ℕ) ^ (2 * n + 1) = 2 ^ n * 2 ^ n * 2 := by ring
    have hpos : 0 < 2 ^ n * 2 ^ n := by positivity
    linarith
  have hj2 : j ≤ n + 1 := by
    by_contra hcon
    have h3 : 2 ^ (n + 2) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : (2 : ℕ) ^ (n + 2) = 2 ^ (n + 1) * 2 := by ring
    have hpos : 0 < 2 ^ (n + 1) := by positivity
    linarith
  rw [show j = n + 1 by omega]

theorem CaseB.card (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) :
    Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) = 2 ^ (n + 1) := by
  have hle : Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) ≤ 2 ^ (n + 1) :=
    hC.card_elem_le _ inf_le_left (CaseB.isElemAbelian hC hH hK)
  have hprod := CaseB.ncard_range_psi hC (g⁻¹ * z * g)
  rw [hC.card_core] at hprod
  have hsub : (fun q => psi (g⁻¹ * z * g) q) '' (coreAt z : Set G) ⊆
      ((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z : Subgroup G) := by
    rintro _ ⟨q, hq, rfl⟩
    exact CaseB.psi_mem hC hH hK hq
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : Set.ncard (((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z :
      Subgroup G) : Set G) = Nat.card ((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔
        centerAt z : Subgroup G) := (Nat.card_coe_set_eq _).symm
  have h3 := CaseB.card_sup hC hH hK
  have hxle : Set.ncard ((fun q => psi (g⁻¹ * z * g) q) '' (coreAt z : Set G)) ≤
      2 * Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) := by
    omega
  have hdvd : Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) ∣
      2 ^ (2 * n + 2) := Dvd.intro_left _ hprod
  have hsq : 2 ^ (2 * n + 1) ≤
      Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) *
        Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) := by
    have hm := Nat.mul_le_mul_right
      (Nat.card (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G)) hxle
    have e : (2 : ℕ) ^ (2 * n + 2) = 2 * 2 ^ (2 * n + 1) := by ring
    linarith
  exact eq_pow_of_dvd_bounds hdvd hle hsq

private theorem sq_eq_one_of_mem_zpowers {y : G} (hy2 : y ^ 2 = 1) {q : G}
    (hq : q ∈ Subgroup.zpowers y) : q ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  have h : y ^ ((2 : ℕ) : ℤ) = 1 := by simpa using hy2
  rw [h, one_zpow]

private theorem commute_zpowers {R₁ : Subgroup G} {y : G} (hyR : ∀ r ∈ R₁, y * r = r * y) :
    ∀ x ∈ R₁, ∀ w ∈ Subgroup.zpowers y, x * w = w * x := by
  intro x hx w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact (Commute.zpow_right (show Commute x y from (hyR x hx).symm) k).eq

private theorem isElemAbelian_sup_zpowers {R₁ : Subgroup G} {y : G} (hy2 : y ^ 2 = 1)
    (hRc : ∀ a ∈ R₁, ∀ b ∈ R₁, a * b = b * a) (hRsq : ∀ a ∈ R₁, a ^ 2 = 1)
    (hyR : ∀ r ∈ R₁, y * r = r * y) :
    CFSG.Open.IsElemAbelian 2 (R₁ ⊔ Subgroup.zpowers y) := by
  have hc := commute_zpowers hyR
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute R₁ (Subgroup.zpowers y) hc).2
  have decomp : ∀ x ∈ R₁ ⊔ Subgroup.zpowers y,
      ∃ p ∈ R₁, ∃ q ∈ Subgroup.zpowers y, p * q = x := by
    intro x hx
    have hx' : x ∈ (R₁ : Set G) * (Subgroup.zpowers y : Set G) := by
      rw [← hset]
      exact hx
    exact Set.mem_mul.mp hx'
  have hKc : ∀ q ∈ Subgroup.zpowers y, ∀ q' ∈ Subgroup.zpowers y, q * q' = q' * q := by
    intro q hq q' hq'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq'
    exact (Commute.zpow_zpow_self y k l).eq
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    change (a : G) * (b : G) = (b : G) * (a : G)
    obtain ⟨p1, hp1, q1, hq1, hA⟩ := decomp a a.2
    obtain ⟨p2, hp2, q2, hq2, hB⟩ := decomp b b.2
    rw [← hA, ← hB]
    have hcomm1 : Commute p1 p2 := hRc p1 hp1 p2 hp2
    have hcomm2 : Commute q1 p2 := (hc p2 hp2 q1 hq1).symm
    have hcomm3 : Commute p1 q2 := hc p1 hp1 q2 hq2
    have hcomm4 : Commute q1 q2 := hKc q1 hq1 q2 hq2
    have h1 : Commute (p1 * q1) p2 := Commute.mul_left hcomm1 hcomm2
    have h2 : Commute (p1 * q1) q2 := Commute.mul_left hcomm3 hcomm4
    exact (Commute.mul_right h1 h2).eq
  · intro x hx
    obtain ⟨p, hp, q, hq, rfl⟩ := decomp x hx
    have hpq : Commute p q := hc p hp q hq
    rw [hpq.mul_pow, hRsq p hp, sq_eq_one_of_mem_zpowers hy2 hq, one_mul]

private theorem card_inf_eq_one_of_card_two {R K : Subgroup G} (hK : Nat.card K = 2)
    (hKR : ¬ K ≤ R) : Nat.card (R ⊓ K : Subgroup G) = 1 := by
  have hdvd : Nat.card (R ⊓ K : Subgroup G) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_right
  rw [hK] at hdvd
  have hne2 : Nat.card (R ⊓ K : Subgroup G) ≠ 2 := by
    intro h2
    apply hKR
    have heq : R ⊓ K = K := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    rw [← heq]
    exact inf_le_left
  have hle : Nat.card (R ⊓ K : Subgroup G) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  generalize Nat.card (R ⊓ K : Subgroup G) = m at hdvd hne2 hle ⊢
  interval_cases m <;> first | rfl | exact absurd rfl hne2 | norm_num at hdvd

private theorem exists_sq_one_of_commute (hC : Config z n) {R₁ : Subgroup G}
    (hR₁ : R₁ ≤ coreAt z) {x : G} (hx : x ∈ coreAt z) (hxR : ∀ r ∈ R₁, x * r = r * x)
    (hxS : x ∉ R₁ ⊔ centerAt z) :
    ∃ y ∈ coreAt z, y ^ 2 = 1 ∧ y ∉ R₁ ⊔ centerAt z ∧ ∀ r ∈ R₁, y * r = r * y := by
  obtain ⟨k, hZk, _, hk2⟩ := hC.exists_generator
  have hkZ : k ∈ centerAt z := hZk ▸ Subgroup.mem_zpowers k
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hC.orderOf_eq] at this
  rcases hC.sq_eq x hx with hx2 | hx2
  · exact ⟨x, hx, hx2, hxS, hxR⟩
  · have hxk : Commute x k :=
      (Subgroup.mem_centralizer_iff.mp (hC.core_le_centralizer_center hx) k hkZ).symm
    refine ⟨x * k, mul_mem hx (hC.center_le_core hkZ), ?_, ?_, ?_⟩
    · rw [hxk.mul_pow, hx2, hk2, ← sq, hz2]
    · intro hmem
      apply hxS
      have hx_eq : x = x * k * k⁻¹ := (mul_inv_cancel_right x k).symm
      rw [hx_eq]
      exact mul_mem hmem (inv_mem (Subgroup.mem_sup_right hkZ))
    · intro r hr
      have hrQ : r ∈ coreAt z := hR₁ hr
      have hkr : k * r = r * k :=
        Subgroup.mem_centralizer_iff.mp (hC.core_le_centralizer_center hrQ) k hkZ
      calc x * k * r = x * (k * r) := mul_assoc _ _ _
        _ = x * (r * k) := by rw [hkr]
        _ = x * r * k := (mul_assoc _ _ _).symm
        _ = r * x * k := by rw [hxR r hr]
        _ = r * (x * k) := mul_assoc _ _ _

theorem CaseB.mem_sup_of_commute (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G)) {x : G} (hx : x ∈ coreAt z)
    (hxR : ∀ r ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G), x * r = r * x) :
    x ∈ (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z := by
  by_contra hxS
  obtain ⟨y, hyQ, hy2, hyS, hyR⟩ := exists_sq_one_of_commute hC inf_le_left hx hxR hxS
  have hR := CaseB.isElemAbelian hC hH hK
  have hy1 : y ≠ 1 := fun h => hyS (h ▸ one_mem _)
  have hycard : Nat.card (zpowers y) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hy2 hy1
  have hyR₁ : ¬ zpowers y ≤ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) := fun h =>
    hyS (Subgroup.mem_sup_left (h (mem_zpowers y)))
  have hinf := card_inf_eq_one_of_card_two hycard hyR₁
  have hRc : ∀ a ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G),
      ∀ b ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G), a * b = b * a := by
    intro a ha b hb
    have := hR.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hE := isElemAbelian_sup_zpowers hy2 hRc hR.2 hyR
  have hEle : (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ zpowers y ≤ coreAt z :=
    sup_le inf_le_left ((zpowers_le (H := coreAt z)).mpr hyQ)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) (zpowers y)
    (commute_zpowers hyR)).1
  rw [hinf, mul_one, hycard] at hprod
  have hle := hC.card_elem_le _ hEle hE
  rw [hprod, CaseB.card hC hH hK] at hle
  have hpos : 0 < 2 ^ (n + 1) := pow_pos (by norm_num) _
  omega

end CFSG.GF2Type.CenterFour

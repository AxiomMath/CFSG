module

public import CFSG.GF2Type.Aschbacher1976Full.HSQuot
public import CFSG.GF2Type.Aschbacher1976Full.WidthZ1
public import CFSG.GF2Type.Aschbacher1976Full.HSDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.PartC

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_gen_eq {y y' : G} (hy : orderOf y = 4)
    (h : Subgroup.zpowers y = Subgroup.zpowers y') : ∃ j : ℤ, y' = (y ^ 2) ^ j * y := by
  have hy' : y' ∈ Subgroup.zpowers y := h ▸ Subgroup.mem_zpowers y'
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hy'
  have hord' : orderOf y' = 4 := by
    rw [← Nat.card_zpowers, ← h, Nat.card_zpowers, hy]
  have h4 : y ^ (4 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hy]
    exact pow_orderOf_eq_one y
  rcases Int.even_or_odd' i with ⟨j, rfl | rfl⟩
  · exfalso
    have h2 : y' ^ 2 = 1 := by
      rw [← hi, ← zpow_natCast, ← zpow_mul]
      have e : (2 * j * ((2 : ℕ) : ℤ)) = 4 * j := by push_cast; ring
      rw [e, zpow_mul, h4, one_zpow]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hord'] at this
    omega
  · refine ⟨j, ?_⟩
    rw [← hi, zpow_add, zpow_mul, zpow_one]
    norm_cast

section ZConj

variable {z : G} {Z A : Subgroup G}

theorem ZF_z (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z)) :
    ZF z = Z :=
  Subgroup.ext fun _ => Width.mem_centerAt_iff hD hz hF2

theorem ZF_conj (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    (g : G) : ZF (g⁻¹ * z * g) = conjugate Z g := by
  rw [← ZF_z hD hz hF2]
  exact centerAt_conj z g

theorem exists_conj {v : G} (h : IsConj z v) : ∃ g : G, v = g⁻¹ * z * g := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact ⟨c⁻¹, by rw [← hc]; simp⟩

theorem ZF_props (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    {v : G} (h : IsConj z v) :
    IsCyclic (ZF v) ∧ Nat.card (ZF v) = 4 ∧ v ∈ ZF v ∧ v ^ 2 = 1 ∧ v ≠ 1 := by
  obtain ⟨g, rfl⟩ := exists_conj h
  rw [ZF_conj hD hz hF2 g]
  haveI := hD.cyc
  refine ⟨Width.isCyclic_conjugate' Z g, by rw [Width.card_conjugate', hD.card_Z], ?_, ?_, ?_⟩
  · apply Width.mem_conjugate_iff.mpr
    rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
    exact hD.mem_z
  · rw [pow_two, show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, ← pow_two,
      Width.z_sq hz]
    group
  · intro h1
    have : z = 1 := by
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hz
    omega

theorem gen_props (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    {v y : G} (h : IsConj z v) (hy : ZF v = zpowers y) : orderOf y = 4 ∧ y ^ 2 = v := by
  obtain ⟨-, hcard, -, -, -⟩ := ZF_props hD hz hF2 h
  have hord : orderOf y = 4 := by rw [← Nat.card_zpowers, ← hy, hcard]
  refine ⟨hord, ?_⟩
  obtain ⟨g, rfl⟩ := exists_conj h
  rw [ZF_conj hD hz hF2 g] at hy
  have hyZ : g * y * g⁻¹ ∈ Z := Width.mem_conjugate_iff.mp (hy ▸ mem_zpowers y)
  have hy4 : y ^ 4 = 1 := hord ▸ pow_orderOf_eq_one y
  have hsq : (g * y * g⁻¹) ^ 2 = z := by
    apply Width.involution_eq hD hz (Z.pow_mem hyZ 2)
    · rw [← pow_mul, conj_pow, show 2 * 2 = 4 from rfl, hy4]
      group
    · intro h1
      rw [conj_pow] at h1
      have : y ^ 2 = 1 := by
        calc y ^ 2 = g⁻¹ * (g * y ^ 2 * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      have := orderOf_dvd_of_pow_eq_one this
      rw [hord] at this
      omega
  calc y ^ 2 = g⁻¹ * (g * y * g⁻¹) ^ 2 * g := by rw [conj_pow]; group
    _ = g⁻¹ * z * g := by rw [hsq]

theorem exists_gen (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    {v : G} (h : IsConj z v) : ∃ y : G, ZF v = zpowers y := by
  obtain ⟨y, hy⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mp
    (ZF_props hD hz hF2 h).1
  exact ⟨y, hy.symm⟩

theorem mem_ZF_conj_iff {v n x : G} : x ∈ ZF (n * v * n⁻¹) ↔ n⁻¹ * x * n ∈ ZF v := by
  have h : ZF (n * v * n⁻¹) = conjugate (ZF v) n⁻¹ := by
    have := centerAt_conj v n⁻¹
    rwa [inv_inv] at this
  rw [h, Width.mem_conjugate_iff, inv_inv]

theorem ZF_conj_zpowers {v y : G} (n : G) (hy : ZF v = zpowers y) :
    ZF (n * v * n⁻¹) = zpowers (n * y * n⁻¹) := by
  ext x
  rw [mem_ZF_conj_iff, hy, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [conj_zpow, hi]; group⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    calc y ^ i = n⁻¹ * (n * y ^ i * n⁻¹) * n := by group
      _ = n⁻¹ * x * n := by rw [← conj_zpow, hi]

theorem Dinv_conj {v n : G} (hv : v ∈ Dinv z) (hn : n ∈ Hz z) : n * v * n⁻¹ ∈ Dinv z := by
  obtain ⟨hconj, hne, hle⟩ := hv
  have hnz : n * z = z * n := Subgroup.mem_centralizer_singleton_iff.mp hn
  refine ⟨hconj.trans (isConj_iff.mpr ⟨n, rfl⟩), ?_, ?_⟩
  · intro h
    apply hne
    calc v = n⁻¹ * (n * v * n⁻¹) * n := by group
      _ = n⁻¹ * z * n := by rw [h]
      _ = z := by rw [mul_assoc, ← hnz]; group
  · intro x hx
    rw [mem_ZF_conj_iff] at hx
    have h1 := hle hx
    have : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
    rw [this]
    exact (Hz z).mul_mem ((Hz z).mul_mem hn h1) ((Hz z).inv_mem hn)

theorem exists_gen_H (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    {v : G} (hv : v ∈ Dinv z) : ∃ y : ↥(Hz z), ZF v = zpowers (y : G) := by
  obtain ⟨y, hy⟩ := exists_gen hD hz hF2 hv.1
  exact ⟨⟨y, hv.2.2 (hy ▸ mem_zpowers y)⟩, hy⟩

end ZConj

open Classical in
noncomputable def yBar (z v : G) : Qbar z :=
  if h : ∃ y : ↥(Hz z), ZF v = Subgroup.zpowers (y : G) then qmk z h.choose else 1

section Tl

variable {z : G} {Z A : Subgroup G}

theorem yBar_eq (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    (hti : HSTI z) {v : G} (hv : v ∈ Dinv z) {y : ↥(Hz z)} (hy : ZF v = zpowers (y : G)) :
    yBar z v = qmk z y := by
  have h : ∃ y : ↥(Hz z), ZF v = zpowers (y : G) := ⟨y, hy⟩
  rw [yBar, dif_pos h]
  have hy₀ : ZF v = zpowers ((h.choose : ↥(Hz z)) : G) := h.choose_spec
  obtain ⟨hord, hsq⟩ := gen_props hD hz hF2 hv.1 hy
  obtain ⟨j, hj⟩ := exists_gen_eq hord (hy.symm.trans hy₀)
  have h1 : h.choose = (y ^ 2) ^ j * y := Subtype.ext (by simpa using hj)
  have h2 : qmk z (y ^ 2) = 1 := by
    rw [qmk_eq_one_iff, Subgroup.coe_pow, hsq]
    exact (hti.2 v hv).1
  rw [h1, map_mul, map_zpow, h2, one_zpow, one_mul]

theorem yBar_sq (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    (hti : HSTI z) {v : G} (hv : v ∈ Dinv z) : yBar z v ^ 2 = 1 := by
  obtain ⟨y, hy⟩ := exists_gen_H hD hz hF2 hv
  obtain ⟨-, hsq⟩ := gen_props hD hz hF2 hv.1 hy
  rw [yBar_eq hD hz hF2 hti hv hy, ← map_pow, qmk_eq_one_iff, Subgroup.coe_pow, hsq]
  exact (hti.2 v hv).1

theorem yBar_ne_one (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    (hti : HSTI z) {v : G} (hv : v ∈ Dinv z) : yBar z v ≠ 1 := by
  obtain ⟨y, hy⟩ := exists_gen_H hD hz hF2 hv
  rw [yBar_eq hD hz hF2 hti hv hy, Ne, qmk_eq_one_iff]
  exact (hti.2 v hv).2 y hy

theorem orderOf_yBar (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    (hti : HSTI z) {v : G} (hv : v ∈ Dinv z) : orderOf (yBar z v) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (yBar_sq hD hz hF2 hti hv) (yBar_ne_one hD hz hF2 hti hv)

theorem yBar_conj (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    (hti : HSTI z) {v : G} (hv : v ∈ Dinv z) (n : ↥(Hz z)) :
    yBar z ((n : G) * v * (n : G)⁻¹) = qmk z n * yBar z v * (qmk z n)⁻¹ := by
  obtain ⟨y, hy⟩ := exists_gen_H hD hz hF2 hv
  have hvn : (n : G) * v * (n : G)⁻¹ ∈ Dinv z := Dinv_conj hv n.2
  have hy' : ZF ((n : G) * v * (n : G)⁻¹) = zpowers (((n * y * n⁻¹ : ↥(Hz z)) : G)) := by
    simpa using ZF_conj_zpowers (n : G) hy
  rw [yBar_eq hD hz hF2 hti hvn hy', yBar_eq hD hz hF2 hti hv hy, map_mul, map_mul, map_inv]

theorem exists_yBar_conj (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) (hti : HSTI z) {v : G} (hv : v ∈ Dinv z) (x : Qbar z) :
    ∃ v' ∈ Dinv z, x * yBar z v * x⁻¹ = yBar z v' := by
  obtain ⟨n, rfl⟩ := qmk_surjective z x
  exact ⟨(n : G) * v * (n : G)⁻¹, Dinv_conj hv n.2, (yBar_conj hD hz hF2 hti hv n).symm⟩

end Tl

end CFSG.GF2Type.Aschbacher1976Full.HS.PartC

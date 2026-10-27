module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallDih

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup

variable {G : Type} [Group G] {D : Subgroup G} {c : G}

@[expose] noncomputable def cz (c : G) : G := c ^ (orderOf c / 2)

theorem cz_mem (hcD : c ∈ D) : cz c ∈ D := pow_mem hcD _

theorem cz_mul_cz (hk : 4 ∣ orderOf c) : cz c * cz c = 1 := by
  rw [cz, ← pow_add, show orderOf c / 2 + orderOf c / 2 = orderOf c by omega,
    pow_orderOf_eq_one]

theorem exists_refl [Finite G] (hcard : Nat.card D = 2 * orderOf c) :
    ∃ u ∈ D, u ∉ zpowers c := by
  by_contra h
  have hle : D ≤ zpowers c := fun u hu => by
    by_contra hu'
    exact h ⟨u, hu, hu'⟩
  have := card_le_of_le hle
  rw [Nat.card_zpowers, hcard] at this
  have h0 := orderOf_pos c
  omega

variable [Finite G]

theorem cz_ne_one (hk : 4 ∣ orderOf c) : cz c ≠ 1 := by
  have h0 := orderOf_pos c
  exact pow_ne_one_of_lt_orderOf (by omega) (by omega)

theorem orderOf_cz (hk : 4 ∣ orderOf c) : orderOf (cz c) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact cz_mul_cz hk) (cz_ne_one hk)

omit [Finite G] in
theorem cz_inv (hk : 4 ∣ orderOf c) : (cz c)⁻¹ = cz c :=
  inv_eq_of_mul_eq_one_right (cz_mul_cz hk)

theorem eq_one_or_eq_cz (hk : 4 ∣ orderOf c) {y : G} (hy : y ∈ zpowers c) (hy2 : y * y = 1) :
    y = 1 ∨ y = cz c := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  have h0 := orderOf_pos c
  have h2i : c ^ (2 * i) = 1 := by rw [mul_comm, zpow_mul, zpow_two]; exact hy2
  have hdvd : (orderOf c : ℤ) ∣ 2 * i := orderOf_dvd_iff_zpow_eq_one.mpr h2i
  obtain ⟨h, hh⟩ : ∃ h : ℕ, orderOf c = 2 * h := ⟨orderOf c / 2, by omega⟩
  have hh2 : orderOf c / 2 = h := by omega
  rw [hh] at hdvd
  push_cast at hdvd
  have hi : (h : ℤ) ∣ i := by
    obtain ⟨s, hs⟩ := hdvd
    exact ⟨s, by linarith⟩
  obtain ⟨t, rfl⟩ := hi
  rw [zpow_mul, zpow_natCast, ← hh2]
  change cz c ^ t = 1 ∨ cz c ^ t = cz c
  have h := zpow_mod_orderOf (cz c) t
  rw [orderOf_cz hk] at h
  rcases Int.emod_two_eq_zero_or_one t with h' | h'
  · left
    rw [← h, show ((2 : ℕ) : ℤ) = 2 from rfl, h', zpow_zero]
  · right
    rw [← h, show ((2 : ℕ) : ℤ) = 2 from rfl, h', zpow_one]

variable (hD : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹)) (hk : 4 ∣ orderOf c)
include hD hk

omit [Finite G] in
theorem comm_cz {x : G} (hx : x ∈ D) : x * cz c = cz c * x := by
  rcases hD x hx with h | ⟨-, h⟩
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp h
    have := Commute.zpow_zpow_self c i ((orderOf c / 2 : ℕ) : ℤ)
    rw [zpow_natCast] at this
    exact this.eq
  · have h1 : x * cz c * x⁻¹ = cz c := by
      rw [cz, ← conj_pow, h, inv_pow]
      exact cz_inv hk
    calc x * cz c = x * cz c * x⁻¹ * x := by group
      _ = cz c * x := by rw [h1]

theorem conj_c_mem {t : G} (ht : t ∈ normalizer (D : Set G)) (hcD : c ∈ D) :
    t * c * t⁻¹ ∈ zpowers c := by
  have hmem : t * c * t⁻¹ ∈ D := (mem_normalizer_iff.mp ht c).mp hcD
  rcases hD _ hmem with h | ⟨h, -⟩
  · exact h
  · exfalso
    have h2 : c * c = 1 := by
      have : t * (c * c) * t⁻¹ = 1 := by rw [← h]; group
      calc c * c = t⁻¹ * (t * (c * c) * t⁻¹) * t := by group
        _ = 1 := by rw [this]; group
    have hdvd : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
    have h0 := orderOf_pos c
    have := Nat.le_of_dvd (by norm_num) hdvd
    have := Nat.le_of_dvd h0 hk
    omega

theorem conj_cz {t : G} (ht : t ∈ normalizer (D : Set G)) (hcD : c ∈ D) :
    t * cz c * t⁻¹ = cz c := by
  have hmem : t * cz c * t⁻¹ ∈ zpowers c := by
    rw [cz, ← conj_pow]
    exact pow_mem (conj_c_mem hD hk ht hcD) _
  have h2 : (t * cz c * t⁻¹) * (t * cz c * t⁻¹) = 1 := by
    rw [show (t * cz c * t⁻¹) * (t * cz c * t⁻¹) = t * (cz c * cz c) * t⁻¹ by group,
      cz_mul_cz hk]
    group
  rcases eq_one_or_eq_cz hk hmem h2 with h | h
  · exfalso
    apply cz_ne_one hk
    calc cz c = t⁻¹ * (t * cz c * t⁻¹) * t := by group
      _ = 1 := by rw [h]; group
  · exact h

theorem sq_mem_zpowers {w : G} (hw : w ∈ normalizer (D : Set G)) (hcD : c ∈ D)
    (hwD : w * w ∈ D) : w * w ∈ zpowers c := by
  rcases hD _ hwD with h | ⟨-, h⟩
  · exact h
  · exfalso
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (conj_c_mem hD hk hw hcD)
    have h1 : (w * w) * c * (w * w)⁻¹ = c ^ (j * j) := by
      calc (w * w) * c * (w * w)⁻¹ = w * (w * c * w⁻¹) * w⁻¹ := by group
        _ = w * c ^ j * w⁻¹ := by rw [hj]
        _ = (w * c * w⁻¹) ^ j := by rw [conj_zpow]
        _ = c ^ (j * j) := by rw [← hj, ← zpow_mul]
    rw [h1] at h
    have h2 : c ^ (j * j + 1) = 1 := by rw [zpow_add, h, zpow_one, inv_mul_cancel]
    have h3 : (orderOf c : ℤ) ∣ j * j + 1 := orderOf_dvd_iff_zpow_eq_one.mpr h2
    have h4 : (4 : ℤ) ∣ j * j + 1 := (Int.natCast_dvd_natCast.mpr hk).trans h3
    have h5 : ((j * j + 1 : ℤ) : ZMod 4) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr h4
    push_cast at h5
    generalize (j : ZMod 4) = x at h5
    revert x
    decide

omit hk in
theorem exists_mul (hcard : Nat.card D = 2 * orderOf c) {x : G} (hx : x ∈ D) :
    ∃ a ∈ D, ∃ b ∈ D, a * a = 1 ∧ b * b = 1 ∧ x = a * b := by
  obtain ⟨u, huD, huC⟩ := exists_refl hcard
  have hu2 : u * u = 1 := by
    rcases hD u huD with h | ⟨h, -⟩
    · exact absurd h huC
    · exact h
  by_cases hxC : x ∈ zpowers c
  · have hux : u * x ∉ zpowers c := fun h => huC (by
      have : u = (u * x) * x⁻¹ := by group
      rw [this]
      exact mul_mem h (inv_mem hxC))
    have hux2 : (u * x) * (u * x) = 1 := by
      rcases hD _ (mul_mem huD hx) with h | ⟨h, -⟩
      · exact absurd h hux
      · exact h
    refine ⟨u, huD, u * x, mul_mem huD hx, hu2, hux2, ?_⟩
    rw [← mul_assoc, hu2, one_mul]
  · have hx2 : x * x = 1 := by
      rcases hD x hx with h | ⟨h, -⟩
      · exact absurd h hxC
      · exact h
    exact ⟨x, hx, 1, one_mem D, hx2, mul_one 1, (mul_one x).symm⟩

variable (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
  ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d)
include hcl

omit hk in
theorem conj_mem_of_sic_of_le (hcard : Nat.card D = 2 * orderOf c)
    {T : Subgroup G} (hT : T ≤ normalizer (D : Set G)) {g : G}
    (hg : ∀ d ∈ D, g⁻¹ * d * g ∈ T) {d : G} (hd : d ∈ D) : g⁻¹ * d * g ∈ D := by
  obtain ⟨a, ha, b, hb, ha2, hb2, rfl⟩ := exists_mul hD hcard hd
  rw [show g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) by group]
  exact mul_mem (HallD8.conj_mem_of_sic hcl ha ha2 (hT (hg a ha)))
    (HallD8.conj_mem_of_sic hcl hb hb2 (hT (hg b hb)))

omit hk in
theorem le_normalizer_of_sic (hcard : Nat.card D = 2 * orderOf c)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hDS : D ≤ S) : S ≤ normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hle
  set H := S ⊓ normalizer (D : Set G) with hH
  have hlt : H < S := lt_of_le_of_ne inf_le_left fun h => hle (h ▸ inf_le_right)
  obtain ⟨y, hyS, hyH, hyN⟩ := FooteLit.exists_mem_normalizer_of_lt hS hlt
  apply hyH
  refine mem_inf.mpr ⟨hyS, ?_⟩
  have hHN : H ≤ normalizer (D : Set G) := inf_le_right
  have hsub : ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    intro d hd
    have h := conj_mem_of_sic_of_le hD hcl hcard hHN (g := y⁻¹) (fun d hd => by
      rw [inv_inv]
      exact (mem_normalizer_iff.mp hyN d).mp (mem_inf.mpr ⟨hDS hd, le_normalizer hd⟩)) hd
    rwa [inv_inv] at h
  have hmap : D.map (MulAut.conj y).toMonoidHom = D := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj y).injective).ge
    rintro _ ⟨d, hd, rfl⟩
    exact hsub d hd
  exact mem_normalizer_iff_map_conj_eq.mpr hmap

theorem mem_centralizer_of_pow (hcD : c ∈ D) {T : Subgroup G}
    (hT : T ≤ normalizer (D : Set G)) {p g : G} {j : ℕ} (hp : p ^ (2 ^ (j + 1)) = cz c)
    (hpg : g⁻¹ * p * g ∈ T) : g ∈ centralizer ({cz c} : Set G) := by
  set w := (g⁻¹ * p * g) ^ (2 ^ j) with hw
  have hwT : w ∈ T := pow_mem hpg _
  have hconj : ∀ n : ℕ, (g⁻¹ * p * g) ^ n = g⁻¹ * p ^ n * g := fun n => by
    have := conj_pow (a := g⁻¹) (b := p) (i := n)
    rwa [inv_inv] at this
  have hww : w * w = g⁻¹ * cz c * g := by
    rw [hw, ← pow_add, ← two_mul, ← pow_succ', hconj, hp]
  have hzN : g⁻¹ * cz c * g ∈ normalizer (D : Set G) := by
    rw [← hww]
    exact mul_mem (hT hwT) (hT hwT)
  have hzD : g⁻¹ * cz c * g ∈ D :=
    HallD8.conj_mem_of_sic hcl (cz_mem hcD) (cz_mul_cz hk) hzN
  rw [← hww] at hzD
  have hwC := sq_mem_zpowers hD hk (hT hwT) hcD hzD
  have hz2 : (w * w) * (w * w) = 1 := by
    rw [hww, show (g⁻¹ * cz c * g) * (g⁻¹ * cz c * g) = g⁻¹ * (cz c * cz c) * g by group,
      cz_mul_cz hk]
    group
  rcases eq_one_or_eq_cz hk hwC hz2 with h | h
  · exfalso
    rw [hww] at h
    apply cz_ne_one hk
    calc cz c = g * (g⁻¹ * cz c * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · rw [hww] at h
    rw [mem_centralizer_singleton_iff]
    calc g * cz c = g * (g⁻¹ * cz c * g) := by rw [h]
      _ = cz c * g := by group

end CFSG.ComponentClassification.Foote5.HallGen

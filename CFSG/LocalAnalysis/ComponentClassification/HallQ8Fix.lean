module

public import CFSG.LocalAnalysis.ComponentClassification.HallQ8Basic
public import CFSG.LocalAnalysis.ComponentClassification.HallQ8Sylow

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

@[expose] def Th (c x : G) : Prop := ∃ g : G, g⁻¹ * cy c * g = x

namespace Q8Cfg

omit [Finite G] in
theorem isPGroup_D (h : Q8Cfg D c) : IsPGroup 2 D := by
  obtain ⟨m, -, hk⟩ := h.two_pow
  exact IsPGroup.of_card (n := m + 1) (by rw [h.card, hk, pow_succ'])

theorem le_normalizer (h : Q8Cfg D c) {P : Subgroup G} (hP : IsPGroup 2 P) (hDP : D ≤ P) :
    P ≤ normalizer (D : Set G) :=
  le_normalizer_of_sic h.dih h.sic h.card hP hDP

theorem inv_fuse (h : Q8Cfg D c) {P : Subgroup G} (hP : IsPGroup 2 P) (hDP : D ≤ P)
    {d g : G} (hd : d ∈ D) (hd2 : d * d = 1) (hg : g⁻¹ * d * g ∈ P) : g⁻¹ * d * g ∈ D :=
  HallD8.conj_mem_of_sic h.sic hd hd2 (h.le_normalizer hP hDP hg)

theorem weak_closed (h : Q8Cfg D c) {P : Subgroup G} (hP : IsPGroup 2 P) (hDP : D ≤ P) {g : G}
    (hg : ∀ d ∈ D, g⁻¹ * d * g ∈ P) {d : G} (hd : d ∈ D) : g⁻¹ * d * g ∈ D :=
  conj_mem_of_sic_of_le h.dih h.sic h.card (h.le_normalizer hP hDP) hg hd

omit [Finite G] in
theorem Th_conj {x : G} (hx : Th c x) (a : G) : Th c (a⁻¹ * x * a) := by
  obtain ⟨g, rfl⟩ := hx
  exact ⟨g * a, by group⟩

omit [Finite G] in
theorem Th_cy : Th c (cy c) := ⟨1, by group⟩

omit [Finite G] in
theorem Th_sq (h : Q8Cfg D c) {x : G} (hx : Th c x) : x * x = cz c := by
  obtain ⟨g, rfl⟩ := hx
  rw [show g⁻¹ * cy c * g * (g⁻¹ * cy c * g) = g⁻¹ * (cy c * cy c) * g by group, cy_mul_cy h]
  have := h.central g
  calc g⁻¹ * cz c * g = g⁻¹ * (g * cz c) := by rw [this]; group
    _ = cz c := by group

omit [Finite G] in
theorem refl_cy (h : Q8Cfg D c) {u : G} (hu : u ∈ D) (huK : u ∉ zpowers c) :
    u * cy c * u⁻¹ = (cy c)⁻¹ := by
  rw [cy, ← conj_pow, (refl_data h hu huK).2, inv_pow]

omit [Finite G] in
theorem Th_inv_cy (h : Q8Cfg D c) {u : G} (hu : u ∈ D) (huK : u ∉ zpowers c) : Th c (cy c)⁻¹ := by
  refine ⟨u⁻¹, ?_⟩
  rw [← refl_cy h hu huK]
  group

omit [Finite G] in
theorem Th_inv (h : Q8Cfg D c) {u : G} (hu : u ∈ D) (huK : u ∉ zpowers c) {x : G} (hx : Th c x) :
    Th c x⁻¹ := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨g', hg'⟩ := Th_inv_cy h hu huK
  exact ⟨g' * g, by
    rw [show (g' * g)⁻¹ * cy c * (g' * g) = g⁻¹ * (g'⁻¹ * cy c * g') * g by group, hg']
    group⟩

omit [Finite G] in
theorem le_normalizer_of_forall {P V : Subgroup G} (hP : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V) :
    P ≤ normalizer (V : Set G) := by
  intro p hp
  rw [mem_normalizer_iff]
  intro v
  refine ⟨hP p hp v, fun hv => ?_⟩
  have := hP p⁻¹ (inv_mem hp) _ hv
  rwa [show p⁻¹ * (p * v * p⁻¹) * p⁻¹⁻¹ = v by group] at this

theorem conj_mem_zpowers_K (h : Q8Cfg D c) {w x : G} (hw : w ∈ normalizer (D : Set G))
    (hx : x ∈ zpowers c) :
    w * x * w⁻¹ ∈ zpowers x := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  obtain ⟨j, hj⟩ := conj_c h hw
  rw [← conj_zpow, hj, ← zpow_mul, mul_comm, zpow_mul]
  exact zpow_mem (mem_zpowers _) _

theorem le_normalizer_zpowers_K (h : Q8Cfg D c) {P : Subgroup G}
    (hP : P ≤ normalizer (D : Set G)) {x : G}
    (hx : x ∈ zpowers c) : P ≤ normalizer (zpowers x : Set G) := by
  refine le_normalizer_of_forall fun p hp v hv => ?_
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hv
  rw [← conj_zpow]
  exact zpow_mem (conj_mem_zpowers_K h (hP hp) hx) _

omit [Finite G] in
theorem isPGroup_zpowers_of_pow {x : G} {m : ℕ} (hx : x ^ (2 ^ m) = 1) :
    IsPGroup 2 (zpowers x) := by
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  exact IsPGroup.of_card (n := e) (by rw [Nat.card_zpowers, he])

omit [Finite G] in
theorem isPGroup_sup_zpowers {a b : G} (hab : Commute a b) {m n : ℕ} (ha : a ^ (2 ^ m) = 1)
    (hb : b ^ (2 ^ n) = 1) : IsPGroup 2 (zpowers a ⊔ zpowers b : Subgroup G) := by
  have hK : zpowers b ≤ normalizer (zpowers a : Set G) := by
    refine le_normalizer_of_forall fun p hp v hv => ?_
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hp
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
    have : Commute (b ^ i) (a ^ j) := ((hab.symm).zpow_left i).zpow_right j
    rw [this.eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers a) j
  exact IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_pow ha) (isPGroup_zpowers_of_pow hb)
    hK

theorem lemmaW (h : Q8Cfg D c) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hDS : D ≤ S)
    {V : Subgroup G} (hVD : V ≤ D) (hSV : S ≤ normalizer (V : Set G)) {g : G}
    (hDN : D ≤ normalizer ((cjS V g : Subgroup G) : Set G)) : cjS V g ≤ D := by
  obtain ⟨t, htV, hDt⟩ := exists_conj_sylow hS hSV g h.isPGroup_D hDN
  intro x hx
  rw [← htV, mem_cjS] at hx
  have hP : IsPGroup 2 (cjS S t) := isPGroup_cjS hS.isPGroup t
  have hv : t * x * t⁻¹ ∈ D := hVD hx
  have := h.weak_closed hP hDt (g := t) (fun d hd => by
    rw [mem_cjS, show t * (t⁻¹ * d * t) * t⁻¹ = d by group]
    exact hDS hd) hv
  rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at this

theorem c1 (h : Q8Cfg D c) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hDS : D ≤ S) {d g k : G}
    (hd : d ∈ D) (hd2 : d * d = 1)
    (hcomm : (g⁻¹ * d * g) * (k⁻¹ * cy c * k) = (k⁻¹ * cy c * k) * (g⁻¹ * d * g)) :
    d = 1 ∨ d = cz c := by
  have hSN : S ≤ normalizer (D : Set G) := h.le_normalizer hS.isPGroup hDS
  set w := g⁻¹ * d * g with hw
  set yk := k⁻¹ * cy c * k with hyk
  have hw2 : w ^ (2 ^ 1) = 1 := by
    rw [pow_one, sq, hw, show g⁻¹ * d * g * (g⁻¹ * d * g) = g⁻¹ * (d * d) * g by group, hd2]
    group
  have hykz : yk * yk = cz c := Th_sq h ⟨k, rfl⟩
  have hyk4 : yk ^ (2 ^ 2) = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 by rfl, pow_add, sq, hykz]
    exact cz_mul_cz h.h4
  have hwc : Commute w yk := hcomm
  have hR2 := isPGroup_sup_zpowers hwc hw2 hyk4
  set V := zpowers (cy c) with hV
  have hVD : V ≤ D := (zpowers_le.mpr ((zpowers_le.mpr h.mem) (cy_mem h)))
  have hSV : S ≤ normalizer (V : Set G) := le_normalizer_zpowers_K h hSN (cy_mem h)
  have hcj : cjS V k = zpowers yk := by
    rw [cjS, hV, MonoidHom.map_zpowers]
    simp [hyk]
  have hRN : (zpowers w ⊔ zpowers yk : Subgroup G) ≤
      normalizer ((cjS V k : Subgroup G) : Set G) := by
    rw [hcj]
    refine sup_le ?_ Subgroup.le_normalizer
    refine le_normalizer_of_forall fun p hp v hv => ?_
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hp
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
    have : Commute (w ^ i) (yk ^ j) := (hwc.zpow_left i).zpow_right j
    rw [this.eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers yk) j
  obtain ⟨t, htV, hRt⟩ := exists_conj_sylow hS hSV k hR2 hRN
  have hwS : t * w * t⁻¹ ∈ S := mem_cjS.mp (hRt (mem_sup_left (mem_zpowers w)))
  have hykV : t * yk * t⁻¹ ∈ V := by
    have : yk ∈ cjS V k := by
      rw [mem_cjS, hyk, show k * (k⁻¹ * cy c * k) * k⁻¹ = cy c by group]
      exact mem_zpowers _
    rw [← htV] at this
    exact mem_cjS.mp this
  set d' := t * w * t⁻¹ with hd'
  have hd'eq : d' = (g * t⁻¹)⁻¹ * d * (g * t⁻¹) := by rw [hd', hw]; group
  have hd'D : d' ∈ D := by
    rw [hd'eq]
    exact h.inv_fuse hS.isPGroup hDS hd hd2 (by rw [← hd'eq]; exact hwS)
  have hd'2 : d' * d' = 1 := by
    rw [hd'eq, show (g * t⁻¹)⁻¹ * d * (g * t⁻¹) * ((g * t⁻¹)⁻¹ * d * (g * t⁻¹)) =
      (g * t⁻¹)⁻¹ * (d * d) * (g * t⁻¹) by group, hd2]
    group
  set yt := t * yk * t⁻¹ with hyt
  have hytK : yt ∈ zpowers c := (zpowers_le.mpr (cy_mem h)) hykV
  have hyt2 : yt * yt = cz c := by
    rw [hyt, show t * yk * t⁻¹ * (t * yk * t⁻¹) = t * (yk * yk) * t⁻¹ by group, hykz]
    have := h.central t
    calc t * cz c * t⁻¹ = cz c * t * t⁻¹ := by rw [this]
      _ = cz c := by group
  have hcomm' : d' * yt = yt * d' := by
    have : t * (w * yk) * t⁻¹ = t * (yk * w) * t⁻¹ := by rw [hcomm]
    rw [hd', hyt]
    calc t * w * t⁻¹ * (t * yk * t⁻¹) = t * (w * yk) * t⁻¹ := by group
      _ = t * (yk * w) * t⁻¹ := this
      _ = t * yk * t⁻¹ * (t * w * t⁻¹) := by group
  have hcy : d' * cy c = cy c * d' := by
    rcases eq_cy_or_inv h hytK hyt2 with h1 | h1
    · rwa [h1] at hcomm'
    · rw [h1] at hcomm'
      have h3 : Commute d' (cy c)⁻¹ := hcomm'
      have h4 := h3.inv_right
      rw [inv_inv] at h4
      exact h4.eq
  have hd'1 : d' = 1 ∨ d' = cz c := by
    by_cases hK : d' ∈ zpowers c
    · exact eq_one_or_eq_cz h.h4 hK hd'2
    · exfalso
      have h1 := refl_cy h hd'D hK
      have h2 : d' * cy c * d'⁻¹ = cy c := by rw [hcy]; group
      rw [h2] at h1
      exact cy_mul_cy_ne_one h (mul_eq_one_iff_eq_inv.mpr h1)
  have hdd : d = (g * t⁻¹) * d' * (g * t⁻¹)⁻¹ := by rw [hd'eq]; group
  rcases hd'1 with h1 | h1
  · left
    rw [hdd, h1]
    group
  · right
    rw [hdd, h1]
    have := h.central (g * t⁻¹)
    calc (g * t⁻¹) * cz c * (g * t⁻¹)⁻¹ = cz c * (g * t⁻¹) * (g * t⁻¹)⁻¹ := by rw [this]
      _ = cz c := by group

end Q8Cfg

end CFSG.ComponentClassification.Foote5.HallGen

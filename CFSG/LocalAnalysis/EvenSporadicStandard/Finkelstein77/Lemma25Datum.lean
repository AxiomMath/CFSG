module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

open Subgroup

variable {G : Type*} [Group G]

theorem mem_zpowers_of_weaklyClosed {x : G}
    (hwc : WeaklyClosedInNormalizer (zpowers x)) (h : G)
    (hh : h * x * h⁻¹ ∈ normalizer ((zpowers x : Subgroup G) : Set G)) :
    h * x * h⁻¹ ∈ zpowers x := by
  have hle : (zpowers x).map (MulAut.conj h).toMonoidHom ≤
      normalizer ((zpowers x : Subgroup G) : Set G) := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    simpa using hh
  have := hwc h hle
  have hmem : h * x * h⁻¹ ∈ (zpowers x).map (MulAut.conj h).toMonoidHom :=
    ⟨x, Subgroup.mem_zpowers x, by simp⟩
  rwa [this] at hmem

theorem mem_zpowers_conj_iff {x w : G} (c : G) :
    w ∈ zpowers (c * x * c⁻¹) ↔ c⁻¹ * w * c ∈ zpowers x := by
  have : zpowers (c * x * c⁻¹) = (zpowers x).map (MulAut.conj c).toMonoidHom := by
    rw [MonoidHom.map_zpowers]; simp
  rw [this, Subgroup.mem_map_equiv]
  simp

theorem mem_normalizer_zpowers_conj {x m : G} (c : G) :
    c * m * c⁻¹ ∈ normalizer ((zpowers (c * x * c⁻¹) : Subgroup G) : Set G) ↔
      m ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h w
    have := h (c * w * c⁻¹)
    rw [mem_zpowers_conj_iff c, mem_zpowers_conj_iff c] at this
    simpa [mul_assoc] using this
  · intro h w
    rw [mem_zpowers_conj_iff c]
    have := h (c⁻¹ * w * c)
    have h2 : c⁻¹ * (c * m * c⁻¹ * w * (c * m * c⁻¹)⁻¹) * c = m * (c⁻¹ * w * c) * m⁻¹ := by group
    rw [mem_zpowers_conj_iff c, h2]
    exact this

theorem exists_mem_normalizer_not_mem [Finite G] {p : ℕ} [Fact p.Prime] {S T : Subgroup G}
    (hT : IsPGroup p T) (hST : S < T) :
    ∃ n ∈ T, n ∈ normalizer (S : Set G) ∧ n ∉ S := by
  classical
  let S' : Subgroup T := S.subgroupOf T
  have hS'ne : S' ≠ ⊤ := by
    intro htop
    obtain ⟨y, hyT, hyS⟩ := IsConcreteLE.exists_of_lt hST
    refine hyS ?_
    have : (⟨y, hyT⟩ : T) ∈ S' := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent T := hT.isNilpotent
  have hlt : S' < normalizer (S' : Set T) :=
    Group.normalizerCondition_of_isNilpotent S' (lt_of_le_of_ne le_top hS'ne)
  obtain ⟨n, hnN, hnS⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨n, n.2, ?_, fun h => hnS (Subgroup.mem_subgroupOf.mpr h)⟩
  have hsub : n ∈ (normalizer (S : Set G)).subgroupOf T := by
    rw [Subgroup.subgroupOf_normalizer_eq hST.le]
    exact hnN
  exact Subgroup.mem_subgroupOf.mp hsub

theorem mem_normalizer_of_map_conj_eq {Z : Subgroup G} {n : G}
    (h : Z.map (MulAut.conj n).toMonoidHom = Z) : n ∈ normalizer (Z : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← h]
    exact ⟨g, hg, by simp⟩
  · intro hg
    rw [← h] at hg
    obtain ⟨y, hy, hyg⟩ := hg
    have : y = g := by simpa using hyg
    rwa [← this]

theorem exists_sylow_le_normalizer [Finite G] {x : G} (hx : orderOf x = 4)
    (hwc : WeaklyClosedInNormalizer (zpowers x)) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({x ^ 2} : Set G)) ∧
      S ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup G := zpowers x with hZ
  set C : Subgroup G := centralizer ({x ^ 2} : Set G) with hC
  have hZp : IsPGroup 2 Z :=
    IsPGroup.of_card (n := 2) (by rw [hZ, Nat.card_zpowers, hx]; norm_num)
  have hZC : Z ≤ C := by
    rw [hZ, hC, zpowers_le, mem_centralizer_singleton_iff]
    exact (Commute.pow_right (Commute.refl x) 2).eq
  let Fam : Set (Subgroup G) :=
    {P | P ≤ C ∧ IsPGroup 2 P ∧ Z ≤ P ∧ P ≤ normalizer (Z : Set G)}
  have hZFam : Z ∈ Fam := ⟨hZC, hZp, le_rfl, le_normalizer⟩
  obtain ⟨S, hS⟩ := Set.Finite.exists_maximal (Set.toFinite Fam) ⟨Z, hZFam⟩
  obtain ⟨hSC, hSp, hZS, hSN⟩ := hS.1
  obtain ⟨Q, hSQ⟩ := IsPGroup.exists_le_sylow (P := S.subgroupOf C) hSp.comap_subtype
  set T : Subgroup G := (Q : Subgroup C).map C.subtype with hT
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T C := ⟨Q, rfl⟩
  have hTp : IsPGroup 2 T := hTsyl.isPGroup
  have hST : S ≤ T := by
    intro y hy
    have : (⟨y, hSC hy⟩ : C) ∈ (Q : Subgroup C) := hSQ (Subgroup.mem_subgroupOf.mpr hy)
    exact ⟨⟨y, hSC hy⟩, this, rfl⟩
  have hSeq : S = T := by
    by_contra hne
    obtain ⟨n, hnT, hnS, hnnot⟩ := exists_mem_normalizer_not_mem hTp (lt_of_le_of_ne hST hne)
    have hnC : n ∈ C := hTsyl.le hnT
    have hle : Z.map (MulAut.conj n).toMonoidHom ≤ normalizer (Z : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      apply hSN
      have := (mem_normalizer_iff.mp hnS y).mp (hZS hy)
      simpa using this
    have hnZ : n ∈ normalizer (Z : Set G) := mem_normalizer_of_map_conj_eq (hwc n hle)
    have hzp : IsPGroup 2 (zpowers n) := hTp.to_le (zpowers_le.mpr hnT)
    have hS'p : IsPGroup 2 (S ⊔ zpowers n : Subgroup G) :=
      hSp.to_sup_of_normal_left' hzp (zpowers_le.mpr hnS)
    have hS'mem : (S ⊔ zpowers n : Subgroup G) ∈ Fam :=
      ⟨sup_le hSC (zpowers_le.mpr hnC), hS'p, hZS.trans le_sup_left,
        sup_le hSN (zpowers_le.mpr hnZ)⟩
    exact hnnot (hS.2 hS'mem le_sup_left (le_sup_right (b := zpowers n) (Subgroup.mem_zpowers n)))
  exact ⟨S, hSeq ▸ hTsyl, hSN⟩

theorem exists_datum [Finite G] {x : G} (hx : orderOf x = 4)
    (hwc : WeaklyClosedInNormalizer (zpowers x)) {a : G} (ha : IsConj (x ^ 2) a)
    {P : Subgroup G} (hPp : IsPGroup 2 P) (hPC : P ≤ centralizer ({a} : Set G)) :
    ∃ y : G, IsConj x y ∧ y ^ 2 = a ∧ P ≤ normalizer ((zpowers y : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀, hS₀N⟩ := exists_sylow_le_normalizer hx hwc
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  set C₀ : Subgroup G := centralizer ({x ^ 2} : Set G) with hC₀
  set P' : Subgroup G := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hconj : ∀ p : G, (MulAut.conj g⁻¹).toMonoidHom p = g⁻¹ * p * g := by intro p; simp
  have hP'C : P' ≤ C₀ := by
    rintro _ ⟨p, hp, rfl⟩
    have hpa : p * a = a * p := mem_centralizer_singleton_iff.mp (hPC hp)
    have h1 : p * (g * x ^ 2 * g⁻¹) = (g * x ^ 2 * g⁻¹) * p := by rw [hg]; exact hpa
    rw [hconj, hC₀, mem_centralizer_singleton_iff]
    calc g⁻¹ * p * g * x ^ 2 = g⁻¹ * (p * (g * x ^ 2 * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x ^ 2 * g⁻¹) * p) * g := by rw [h1]
      _ = x ^ 2 * (g⁻¹ * p * g) := by group
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (P := P'.subgroupOf C₀) (hPp.map _).comap_subtype
  set T : Subgroup G := (Q : Subgroup C₀).map C₀.subtype with hT
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T C₀ := ⟨Q, rfl⟩
  have hP'T : P' ≤ T := by
    intro y hy
    have : (⟨y, hP'C hy⟩ : C₀) ∈ (Q : Subgroup C₀) := hQ (Subgroup.mem_subgroupOf.mpr hy)
    exact ⟨⟨y, hP'C hy⟩, this, rfl⟩
  obtain ⟨k, hkC, hk⟩ := hTsyl.exists_mem_conj hS₀
  have hkx : k * x ^ 2 = x ^ 2 * k := mem_centralizer_singleton_iff.mp hkC
  refine ⟨(g * k⁻¹) * x * (g * k⁻¹)⁻¹, isConj_iff.mpr ⟨g * k⁻¹, rfl⟩, ?_, ?_⟩
  · calc ((g * k⁻¹) * x * (g * k⁻¹)⁻¹) ^ 2 = (g * k⁻¹) * x ^ 2 * (g * k⁻¹)⁻¹ := by
          rw [← conj_pow]
      _ = g * (k⁻¹ * x ^ 2 * k) * g⁻¹ := by group
      _ = a := by
          rw [← hg]
          congr 2
          calc k⁻¹ * x ^ 2 * k = k⁻¹ * (x ^ 2 * k) := by group
            _ = k⁻¹ * (k * x ^ 2) := by rw [hkx]
            _ = x ^ 2 := by group
  · intro p hp
    have hpP' : g⁻¹ * p * g ∈ P' := ⟨p, hp, hconj p⟩
    have hmem : k * (g⁻¹ * p * g) * k⁻¹ ∈ S₀ := by
      rw [hk]
      have : k⁻¹ * (k * (g⁻¹ * p * g) * k⁻¹) * k = g⁻¹ * p * g := by group
      rw [this]
      exact hP'T hpP'
    have := (mem_normalizer_zpowers_conj (x := x) (g * k⁻¹)).mpr (hS₀N hmem)
    have heq : (g * k⁻¹) * (k * (g⁻¹ * p * g) * k⁻¹) * (g * k⁻¹)⁻¹ = p := by group
    rw [heq] at this
    exact this

theorem mem_zpowers_of_conj {x y : G} (hwc : WeaklyClosedInNormalizer (zpowers x))
    (hxy : IsConj x y) (hn : x ∈ normalizer ((zpowers y : Subgroup G) : Set G)) :
    x ∈ zpowers y := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp hxy
  have h1 : h⁻¹ * x * h⁻¹⁻¹ ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    have := (mem_normalizer_zpowers_conj (x := h * x * h⁻¹) (m := x) h⁻¹).mpr hn
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [e] at this
  have h2 := mem_zpowers_of_weaklyClosed hwc h⁻¹ h1
  rw [mem_zpowers_conj_iff h]
  simpa using h2

theorem eq_sq_of_mem_zpowers {x u : G} (hx : orderOf x = 4) (hu : u ∈ zpowers x)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) : u = x ^ 2 := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
  have hx4 : x ^ 4 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hx] at this
    omega
  have hmod : x ^ i = x ^ (i % 4) := by
    have := zpow_mod_orderOf x i
    rw [hx] at this
    simpa using this.symm
  have hi : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases hi with h | h | h | h
  · exact absurd (by rw [hmod, h]; simp) hu1
  · rw [hmod, h] at hu2
    simp only [zpow_one] at hu2
    exact absurd (by rw [sq]; exact hu2) hx2
  · rw [hmod, h]; norm_cast
  · rw [hmod, h] at hu2
    have : x ^ (3 : ℤ) * x ^ (3 : ℤ) = x ^ 2 := by
      calc x ^ (3 : ℤ) * x ^ (3 : ℤ) = x ^ 4 * x ^ 2 := by
            simp only [zpow_ofNat]; group
        _ = x ^ 2 := by rw [hx4, one_mul]
    exact absurd (this ▸ hu2) hx2

theorem eq_or_eq_inv_of_mem_zpowers {y v : G} (hy : orderOf y = 4) (hv : v ∈ zpowers y)
    (hv2 : v * v ≠ 1) : v = y ∨ v = y⁻¹ := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hv
  have hy4 : y ^ 4 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hmod : y ^ i = y ^ (i % 4) := by
    have := zpow_mod_orderOf y i
    rw [hy] at this
    simpa using this.symm
  have hi : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases hi with h | h | h | h
  · exfalso; apply hv2; rw [hmod, h]; simp
  · left; rw [hmod, h]; simp
  · exfalso; apply hv2; rw [hmod, h]
    calc y ^ (2 : ℤ) * y ^ (2 : ℤ) = y ^ 4 := by simp only [zpow_ofNat]; group
      _ = 1 := hy4
  · right; rw [hmod, h]
    have : y ^ (3 : ℤ) * y = 1 := by
      calc y ^ (3 : ℤ) * y = y ^ 4 := by simp only [zpow_ofNat]; group
        _ = 1 := hy4
    exact eq_inv_of_mul_eq_one_left this


theorem orderOf_conj_eq (c x : G) : orderOf (c * x * c⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq c (show SemiconjBy c x (c * x * c⁻¹) by
    simp [SemiconjBy, mul_assoc])).symm

theorem orderOf_eq_of_isConj {x y : G} (h : IsConj x y) : orderOf y = orderOf x := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact orderOf_conj_eq c x

theorem conj_eq_or_eq_inv_of_mem_normalizer {y p : G} (hy : orderOf y = 4)
    (hp : p ∈ normalizer ((zpowers y : Subgroup G) : Set G)) :
    p * y * p⁻¹ = y ∨ p * y * p⁻¹ = y⁻¹ := by
  have hmem : p * y * p⁻¹ ∈ zpowers y := (mem_normalizer_iff.mp hp y).mp (mem_zpowers y)
  have hne : (p * y * p⁻¹) * (p * y * p⁻¹) ≠ 1 := by
    intro h
    have hyy : y * y = 1 := by
      have h1 : p * (y * y) * p⁻¹ = 1 := by rw [← h]; group
      have h2 : y * y = p⁻¹ * 1 * p := by rw [← h1]; group
      simpa using h2
    have := orderOf_dvd_of_pow_eq_one (show y ^ 2 = 1 by rwa [sq])
    rw [hy] at this
    omega
  exact eq_or_eq_inv_of_mem_zpowers hy hmem hne

section Class

variable {x : G} (hx : orderOf x = 4)
include hx

theorem sq_eq_one_of_isConj {u : G} (hu : IsConj (x ^ 2) u) : u * u = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hu
  have hx4 : x ^ 4 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  calc c * x ^ 2 * c⁻¹ * (c * x ^ 2 * c⁻¹) = c * x ^ 4 * c⁻¹ := by group
    _ = 1 := by rw [hx4]; group

theorem ne_one_of_isConj {u : G} (hu : IsConj (x ^ 2) u) : u ≠ 1 := by
  intro h
  rw [h, isConj_one_left] at hu
  have := orderOf_dvd_of_pow_eq_one hu
  rw [hx] at this
  omega

theorem orderOf_eq_two_of_isConj {u : G} (hu : IsConj (x ^ 2) u) : orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact sq_eq_one_of_isConj hx hu) (ne_one_of_isConj hx hu)

variable [Finite G]

theorem eq_sq_of_commute (hwc : WeaklyClosedInNormalizer (zpowers x)) {u : G}
    (hu : IsConj (x ^ 2) u) (hux : u * x = x * u) : u = x ^ 2 := by
  have hZp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
  have hPC : zpowers x ≤ centralizer ({u} : Set G) := by
    rw [zpowers_le, mem_centralizer_singleton_iff]; exact hux.symm
  obtain ⟨y, hxy, hy2, hP⟩ := exists_datum hx hwc hu hZp hPC
  have hx_in : x ∈ zpowers y := mem_zpowers_of_conj hwc hxy (hP (mem_zpowers x))
  have hyo : orderOf y = 4 := by rw [orderOf_eq_of_isConj hxy, hx]
  have heq : zpowers x = zpowers y :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hx_in)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hyo])
  have hyZ : y ∈ zpowers x := heq ▸ mem_zpowers y
  have huZ : u ∈ zpowers x := by rw [← hy2]; exact pow_mem hyZ 2
  exact eq_sq_of_mem_zpowers hx huZ (sq_eq_one_of_isConj hx hu) (ne_one_of_isConj hx hu)

theorem eq_sq_of_commute_conj (hwc : WeaklyClosedInNormalizer (zpowers x)) {y u : G}
    (hxy : IsConj x y) (hu : IsConj (x ^ 2) u) (huy : u * y = y * u) : u = y ^ 2 := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp hxy
  have hu' : IsConj (x ^ 2) (h⁻¹ * u * h) := by
    refine hu.trans (isConj_iff.mpr ⟨h⁻¹, ?_⟩)
    simp
  have hc : h⁻¹ * u * h * x = x * (h⁻¹ * u * h) := by
    have : u * (h * x * h⁻¹) = (h * x * h⁻¹) * u := huy
    calc h⁻¹ * u * h * x = h⁻¹ * (u * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * u) * h := by rw [this]
      _ = x * (h⁻¹ * u * h) := by group
  have := eq_sq_of_commute hx hwc hu' hc
  calc u = h * (h⁻¹ * u * h) * h⁻¹ := by group
    _ = h * x ^ 2 * h⁻¹ := by rw [this]
    _ = (h * x * h⁻¹) ^ 2 := by rw [conj_pow]


variable (hwc : WeaklyClosedInNormalizer (zpowers x))
include hwc

theorem mul_isConj_of_commute {a b : G} (ha : IsConj (x ^ 2) a) (hb : IsConj (x ^ 2) b)
    (hab : a ≠ b) (hcomm : a * b = b * a) : IsConj (x ^ 2) (a * b) := by
  have hbp : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_two_of_isConj hx hb]; norm_num)
  have hPC : zpowers b ≤ centralizer ({a} : Set G) := by
    rw [zpowers_le, mem_centralizer_singleton_iff]; exact hcomm.symm
  obtain ⟨y, hxy, hy2, hP⟩ := exists_datum hx hwc ha hbp hPC
  have hyo : orderOf y = 4 := by rw [orderOf_eq_of_isConj hxy, hx]
  have hbn : b ∈ normalizer ((zpowers y : Subgroup G) : Set G) := hP (mem_zpowers b)
  rcases conj_eq_or_eq_inv_of_mem_normalizer hyo hbn with h | h
  · exfalso
    have hbc : b * y = y * b := by
      calc b * y = (b * y * b⁻¹) * b := by group
        _ = y * b := by rw [h]
    exact hab (hy2 ▸ (eq_sq_of_commute_conj hx hwc hxy hb hbc)).symm
  · refine hb.trans (isConj_iff.mpr ⟨y⁻¹, ?_⟩)
    have hbyb : b * y = y⁻¹ * b := by
      calc b * y = (b * y * b⁻¹) * b := by group
        _ = y⁻¹ * b := by rw [h]
    have haa : a * a = 1 := sq_eq_one_of_isConj hx ha
    calc y⁻¹ * b * y⁻¹⁻¹ = y⁻¹ * (b * y) := by group
      _ = y⁻¹ * (y⁻¹ * b) := by rw [hbyb]
      _ = (y ^ 2)⁻¹ * b := by group
      _ = a⁻¹ * b := by rw [hy2]
      _ = a * b := by rw [inv_eq_of_mul_eq_one_right haa]

end Class


end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof
